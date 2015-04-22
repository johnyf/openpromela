#!/usr/bin/env python
import argparse
import datetime
import logging
import os
import re
import time
import psutil
from openpromela import logic


INPUT_FILE = 'amba.pml'
SLUGS_LOG = 'openpromela.slugs.slugs'
LOG_FILE = 'amba_log.txt'
DEBUG = False  # for this script only
N = 2
M = 17


logger = logging.getLogger(__name__)


def form_progress(i):
    """Return conjunction of LTL formulae for progress."""
    prog = ' && '.join(
        '[]<>(request[{k}] -> (master == {k}))'.format(k=k)
        for k in xrange(i))
    return 'assert ltl { ' + prog + ' }'


if __name__ == '__main__':
    # args
    p = argparse.ArgumentParser()
    p.add_argument('--min', default=N, type=int,
                   help='from this # of masters')
    p.add_argument('--max', default=M, type=int,
                   help='to this # of masters')
    p.add_argument('--debug', type=int, default=logging.ERROR,
                   help='python logging level')
    p.add_argument('--log', action='store_true',
                   help='dump debug log file')
    args = p.parse_args()
    n = args.min
    m = args.max + 1
    # config logging
    # log to file
    level = args.debug
    if args.log:
        h = logging.FileHandler(LOG_FILE)
    else:
        h = logging.StreamHandler()
    logs = {'openpromela.logic', 'openpromela.bitvector'}
    for name in logs:
        log = logging.getLogger(name)
        log.addHandler(h)
        log.setLevel(level)
    # slugs memory log files
    level = logging.DEBUG - 1
    log = logging.getLogger(SLUGS_LOG)
    log.setLevel(level)
    # own logger to screen
    if DEBUG:
        sh = logging.StreamHandler()
        logger.addHandler(sh)
        logger.setLevel(logging.DEBUG)
    # input and iter
    with open(INPUT_FILE) as f:
        s = f.read()
    for i in xrange(n, m):
        # print('drop caches...')
        # this avoids creating log files as root
        # os.system('sudo sh -c "sync; echo 3 > /proc/sys/vm/drop_caches"')
        #
        # # check if other users
        users = psutil.get_users()
        if len(users) > 1:
            print('warning: other users logged in'
                  '(may start running expensive jobs).')
        # print info
        print('starting {i} masters...'.format(i=i))
        bdd_file = 'bdd_{i}_masters.txt'.format(i=i)
        log_file = 'log_{i}_masters.txt'.format(i=i)
        # update log file
        fh = logging.FileHandler(log_file)
        log.addHandler(fh)
        # prep input
        j = i - 1
        newline = '#define N {j}'.format(j=j)
        c = re.sub('#define N.*', newline, s)
        logger.debug(c)
        # add multiple weak fairness assumptions
        # prog = ' && '.join(
        #    '[]<>(request[{k}] -> (master == {k}))'.format(k=k)
        #    for k in xrange(i))
        # c += form_progress(i)
        # run
        t0 = time.time()
        r = logic.synthesize(c, symbolic=True, bddfile=bdd_file)
        t1 = time.time()
        dt = datetime.timedelta(seconds=t1 - t0)
        # close log
        for h in log.handlers:
            log.removeHandler(h)
        fh.close()
        assert r is not None, 'NOT REALIZABLE !!!'
        print('Done with {i} masters in {dt}.'.format(i=i, dt=dt))
