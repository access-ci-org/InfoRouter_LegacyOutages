#!/usr/bin/env python3

# InforRouter ACCESS Infrastructure News from URL to Legacy Outages Django Model
#
import argparse
from datetime import datetime, tzinfo, timedelta
import http.client as httplib
import json
import logging
import logging.handlers
import os
from pid import PidFile
import pwd
import re
import sys
import shutil
import signal
import ssl
from time import sleep
import traceback
from urllib.parse import urlparse

import django
django.setup()
from django.db import DataError, IntegrityError
from django.conf import settings
from django.utils.dateparse import parse_datetime
from outages.models import *
from processing_status.process import ProcessingActivity

import pdb

class UTC(tzinfo):
    def utcoffset(self, dt):
        return timedelta(0)
    def tzname(self, dt):
        return 'UTC'
    def dst(self, dt):
        return timedelta(0)
utc = UTC()

# Used during initialization before loggin is enabled
def eprint(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

class Router():
    def __init__(self):
        parser = argparse.ArgumentParser(epilog='File SRC|DEST syntax: file:<file path and name')
        parser.add_argument('daemonaction', nargs='?', choices=('start', 'stop', 'restart'), \
                            help='{start, stop, restart} daemon')
        parser.add_argument('-s', '--source', action='store', dest='src', \
                            help='Messages source {file, http[s]} (default=file)')
        parser.add_argument('-d', '--destination', action='store', dest='dest', \
                            help='Message destination {file, analyze, or warehouse} (default=analyze)')
        parser.add_argument('--daemon', action='store_true', \
                            help='Daemonize execution')
        parser.add_argument('-l', '--log', action='store', \
                            help='Logging level (default=warning)')
        parser.add_argument('-c', '--config', action='store', default='./inforouter_legacyoutages.conf', \
                            help='Configuration file default=./inforouter_legacyoutages.conf')
        parser.add_argument('--pdb', action='store_true', \
                            help='Run with Python debugger')
        self.args = parser.parse_args()

        # Trace for debugging as early as possible
        if self.args.pdb:
            pdb.set_trace()

        # Load configuration file
        self.config_file = os.path.abspath(self.args.config)
        try:
            with open(self.config_file, 'r') as file:
                conf=file.read()
        except IOError as e:
            eprint('Error "{}" reading config={}'.format(e, config_path))
            sys.exit(1)
        try:
            self.config = json.loads(conf)
        except ValueError as e:
            eprint('Error "{}" parsing config={}'.format(e, config_path))
            sys.exit(1)

        if self.config.get('PID_FILE'):
            self.pidfile_path =  self.config['PID_FILE']
        else:
            name = os.path.basename(__file__).replace('.py', '')
            self.pidfile_path = '/var/run/{}/{}.pid'.format(name, name)

    def Setup(self):
        # Initialize log level from arguments, or config file, or default to WARNING
        loglevel_str = (self.args.log or self.config.get('LOG_LEVEL', 'WARNING')).upper()
        loglevel_num = getattr(logging, loglevel_str, None)
        self.logger = logging.getLogger('DaemonLog')
        self.logger.setLevel(loglevel_num)
        self.formatter = logging.Formatter(fmt='%(asctime)s.%(msecs)03d %(levelname)s %(message)s', \
                                           datefmt='%Y/%m/%d %H:%M:%S')
        self.handler = logging.handlers.TimedRotatingFileHandler(self.config['LOG_FILE'], \
            when='W6', backupCount=999, utc=True)
        self.handler.setFormatter(self.formatter)
        self.logger.addHandler(self.handler)

        # Initialize stdout, stderr
        if self.args.daemon and 'LOG_FILE' in self.config:
            self.stdout_path = self.config['LOG_FILE'].replace('.log', '.daemon.log')
            self.stderr_path = self.stdout_path
            self.SaveDaemonStdOut(self.stdout_path)
            sys.stdout = open(self.stdout_path, 'wt+')
            sys.stderr = open(self.stderr_path, 'wt+')

        signal.signal(signal.SIGINT, self.exit_signal)
        signal.signal(signal.SIGTERM, self.exit_signal)

        self.logger.info('Starting program=%s pid=%s, uid=%s(%s)' % \
                     (os.path.basename(__file__), os.getpid(), os.geteuid(), pwd.getpwuid(os.geteuid()).pw_name))

        self.src = {}
        self.dest = {}
        for var in ['uri', 'scheme', 'path', 'display']: # Where <full> contains <type>:<obj>
            self.src[var] = None
            self.dest[var] = None
        self.peak_sleep = 10 * 60        # 10 minutes in seconds during peak business hours
        self.off_sleep = 60 * 60         # 60 minutes in seconds during off hours
        self.max_stale = 24 * 60 * 60    # 24 hours in seconds force refresh
        # These attributes have their own database column
        # Some fields exist in both parent and sub-resources, while others only in one
        # Those in one will be left empty in the other, or inherit from the parent
        self.have_column = ['resource_id', 'info_resourceid',
                            'resource_descriptive_name', 'resource_description',
                            'project_affiliation', 'provider_level',
                            'resource_status', 'current_statuses', 'updated_at']
        default_file = 'file:./outages.json'

        # Verify arguments and parse compound arguments
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            if 'SOURCE_URL' in self.config:
                self.args.src = self.config['SOURCE_URL']
        if not getattr(self.args, 'src', None): # Tests for None and empty ''
            self.args.src = default_file
        idx = self.args.src.find(':')
        if idx > 0:
            (self.src['scheme'], self.src['path']) = (self.args.src[0:idx], self.args.src[idx+1:])
        else:
            (self.src['scheme'], self.src['path']) = (self.args.src, None)
        if self.src['scheme'] not in ['file', 'http', 'https']:
            self.logger.error('Source not {file, http, https}')
            sys.exit(1)
        if self.src['scheme'] in ['http', 'https']:
            if self.src['path'][0:2] != '//':
                self.logger.error('Source URL not followed by "//"')
                sys.exit(1)
            self.src['path'] = self.src['path'][2:]
        self.src['uri'] = self.args.src
        self.src['display'] = self.args.src

        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            if 'DESTINATION' in self.config:
                self.args.dest = self.config['DESTINATION']
        if not getattr(self.args, 'dest', None): # Tests for None and empty ''
            self.args.dest = 'analyze'
        idx = self.args.dest.find(':')
        if idx > 0:
            (self.dest['scheme'], self.dest['path']) = (self.args.dest[0:idx], self.args.dest[idx+1:])
        else:
            self.dest['scheme'] = self.args.dest
        if self.dest['scheme'] not in ['file', 'analyze', 'warehouse']:
            self.logger.error('Destination not {file, analyze, warehouse}')
            sys.exit(1)
        self.dest['uri'] = self.args.dest
        if self.dest['scheme'] == 'warehouse':
            self.dest['display'] = '{}@database={}'.format(self.dest['scheme'], settings.DATABASES['default']['HOST'])
        else:
            self.dest['display'] = self.args.dest

        if self.src['scheme'] in ['file'] and self.dest['scheme'] in ['file']:
            self.logger.error('Source and Destination can not both be a {file}')
            sys.exit(1)

        self.AFFILIATIONS = self.config.get('AFFILIATIONS', ['NONE'])  # Default to NONE
        
        if self.args.daemonaction == 'start':
            if self.src['scheme'] not in ['http', 'https'] or self.dest['scheme'] not in ['warehouse']:
                self.logger.error('Can only daemonize when source=[http|https] and destination=warehouse')
                sys.exit(1)

        self.logger.info('Source: ' + self.src['display'])
        self.logger.info('Destination: ' + self.dest['display'])
        self.logger.info('Config: ' + self.config_file)
        self.logger.info('Affiliations: ' + ', '.join(self.AFFILIATIONS))

    def SaveDaemonStdOut(self, path):
        # Save daemon log file using timestamp only if it has anything unexpected in it
        try:
            file = open(path, 'r')
            lines = file.read()
            file.close()
            if not re.match("^started with pid \d+$", lines) and not re.match("^$", lines):
                ts = datetime.strftime(datetime.now(), '%Y-%m-%d_%H:%M:%S')
                newpath = '{}.{}'.format(path, ts)
                self.logger.debug('Saving previous daemon stdout to {}'.format(newpath))
                shutil.copy(path, newpath)
        except Exception as e:
            self.logger.error('Exception in SaveDaemonStdOut({})'.format(path))
        return

    def exit_signal(self, signum, frame):
        self.logger.critical('Caught signal={}({}), exiting with rc={}'.format(signum, signal.Signals(signum).name, signum))
        sys.exit(signum)

    def exit(self, rc):
        if rc:
            self.logger.error('Exiting with rc={}'.format(rc))
        sys.exit(rc)

    def Read_SOURCE(self, url):
        urlp = urlparse(url)
        if not urlp.scheme or not urlp.netloc or not urlp.path:
            self.logger.error('SOURCE URL is not valid: {}'.format(url))
            sys.exit(1)
        if urlp.scheme not in ['http', 'https']:
            self.logger.error('SOURCE URL scheme is not valid: {}'.format(url))
            sys.exit(1)
        if ':' in urlp.netloc:
            (host, port) = urlp.netloc.split(':')
        else:
            (host, port) = (urlp.netloc, '')
        if not port:
            port = '80' if urlp.scheme == 'http' else '443'     # Default is HTTPS/443
        
        headers = {'Content-type': 'application/json'
            }
        ctx = ssl.create_default_context(ssl.Purpose.CLIENT_AUTH)
        conn = httplib.HTTPSConnection(host=host, port=port, context=ctx)
        conn.request('GET', urlp.path, None , headers)
        self.logger.debug('HTTP GET  {}'.format(url))
        response = conn.getresponse()
        result = response.read()
        self.logger.debug('HTTP RESP {} {} (returned {}/bytes)'.format(response.status, response.reason, len(result)))
        try:
            input_json = json.loads(result)
        except ValueError as e:
            self.logger.error('Response not in expected JSON format ({})'.format(e))
            return(None)
        return(input_json)

    def Analyze_SOURCE(self, input_obj):
        maxlen = {}
        for p_res in input_obj:  # Parent resources
            self.stats['Update'] += 1
            self.logger.info('Item={}, Affected={}, StartDatetime="{}"'.format(p_res['view_node'], len(p_res['affected_infrastructure_elements']), p_res['start_timestamp'], p_res['resource_descriptive_name']))

    def Write_Cache(self, file, input_obj):
        data = json.dumps(input_obj)
        with open(file, 'w') as my_file:
            my_file.write(data)
            my_file.close()
        self.logger.info('Serialized and wrote {} bytes to file={}'.format(len(data), file))
        return(len(data))

    def Read_Cache(self, file):
        with open(file, 'r') as my_file:
            data = my_file.read()
            my_file.close()
        try:
            input_obj = json.loads(data)
            self.logger.info('Read and parsed {} bytes from file={}'.format(len(data), file))
            return(input_obj)
        except ValueError as e:
            self.logger.error('Error "{}" parsing file={}'.format(e, file))
            sys.exit(1)

    def Warehouse_LegacyOutages(self, input_obj):
        self.cur = {}   # Resources currently in database
        self.new = {}   # New resources in document
        for item in Outages.objects.filter(ID__startswith='urn:ogf:glue2:operations.access-ci.org:infrastructure_news:'))
            self.cur[item.ID] = item

        for p_res in input_obj:
            if p_res['type'] = 'Outage Full':
                type = 'Full'
            elsif p_res['type'] = 'Outage Partial':
                type = 'Partial'
            else:
                type = 'Reconfiguration'
            for resource in p_res['affected_infrastructure_elements']:
                siteid = '.'.join(resource['resourceid'].split('.')[1:])
                try:
                    model, created = Outagers.objects.update_or_create(
                                        ID=p_res['ID'],
                                        defaults = {
                                            'OutageID': p_res['outage_id'],
                                            'ResourceID': resource['resourceid'],
                                            'WebURL': p_res['web_url'],
                                            'Subject': p_res['subject'],
                                            'Content': p_res['content
                                            'OutageStart': p_res['start_timestamp'],
                                            'OutageEnd': p_res['end_timestamp'],
                                            'SiteID': siteid,
                                            'OutageType': type
                                        })
                    model.save()
                    self.logger.debug('Base ID={}, ResourceID={}'.format(p_res['ID'], p_res['info_resourceid']))
                    self.new[p_res['ID']]=model
                    self.stats['Update'] += 1
                except (DataError, IntegrityError) as e:
                    msg = '{} saving resource_id={} ({}): {}'.format(type(e).__name__, p_res['resource_id'], p_res['info_resourceid'], e.message)
                    self.logger.error(msg)
                    return(False, msg)

        for id in self.cur:
            if id not in self.new:
                try:
                    Outages.objects.filter(ID=id).delete()
                    self.stats['Delete'] += 1
                    self.logger.info('Deleted ID={}'.format(id))
                except (DataError, IntegrityError) as e:
                    self.logger.error('{} deleting ID={}: {}'.format(type(e).__name__, id, e.message))
        return(True, '')
            
    def smart_sleep(self, last_run):
        # This functions sleeps, performs refresh checks, and returns when it's time to refresh
        while True:
            if 12 <= datetime.now(utc).hour <= 24: # Between 6 AM and 6 PM Central (~12 to 24 UTC)
                current_sleep = self.peak_sleep
            else:
                current_sleep = self.off_sleep
            self.logger.debug('sleep({})'.format(current_sleep))
            sleep(current_sleep)

            # Force a refresh every 12 hours at Noon and Midnight UTC
            now_utc = datetime.now(utc)
            if ( (now_utc.hour < 12 and last_run.hour > 12) or \
                (now_utc.hour > 12 and last_run.hour < 12) ):
                self.logger.info('REFRESH TRIGGER: Every 12 hours')
                return

            # Force a refresh every max_stale seconds
            since_last_run = now_utc - last_run
            if since_last_run.seconds > self.max_stale:
                self.logger.info('REFRESH TRIGGER: Stale {}/seconds above thresdhold of {}/seconds'.format(since_last_run.seconds, self.max_stale) )
                return

    def Run(self):
        while True:
            self.start = datetime.now(utc)
            self.stats = {
                'Update': 0,
                'Delete': 0,
                'Skip': 0,
            }
            
            if self.src['scheme'] == 'file':
                SOURCE_DATA = self.Read_Cache(self.src['path'])
            else:
                SOURCE_DATA = self.Read_SOURCE(self.src['uri'])

            if SOURCE_DATA:
                if self.dest['scheme'] == 'file':
                    bytes = self.Write_Cache(self.dest['path'], SOURCE_DATA)
                elif self.dest['scheme'] == 'analyze':
                    self.Analyze_SOURCE(SOURCE_DATA)
                elif self.dest['scheme'] == 'warehouse':
                    pa_application=os.path.basename(__file__)
                    pa_function='Warehouse_LegacyOutages'
                    pa_topic = 'Infrastructure News'
                    pa_about = ','.join(self.AFFILIATIONS)
                    pa_id = '{}:{}:{}'.format(pa_application, pa_function, pa_topic)
                    pa = ProcessingActivity(pa_application, pa_function, pa_id , pa_topic, pa_about)
                    (rc, warehouse_msg) = self.Warehouse_LegacyOutages(SOURCE_DATA)
                
                self.end = datetime.now(utc)
                summary_msg = 'Processed in {:.3f}/seconds: {}/updates, {}/deletes, {}/skipped'.format((self.end - self.start).total_seconds(), self.stats['Update'], self.stats['Delete'], self.stats['Skip'])
                self.logger.info(summary_msg)
                if self.dest['scheme'] == 'warehouse':
                    if rc:  # No errors
                        pa.FinishActivity(rc, summary_msg)
                    else:   # Something failed, use returned message
                        pa.FinishActivity(rc, warehouse_msg)
            if not self.args.daemonaction:
                break
            self.smart_sleep(self.start)

########## CUSTOMIZATIONS END ##########

if __name__ == '__main__':
    router = Router()
    with PidFile(router.pidfile_path):
        try:
            router.Setup()
            rc = router.Run()
        except Exception as e:
            msg = '{} Exception: {}'.format(type(e).__name__, e)
            router.logger.error(msg)
            traceback.print_exc(file=sys.stdout)
            rc = 1
    router.exit(rc)
