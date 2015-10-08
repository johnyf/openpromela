"""Interface to `slugs` synthesizer."""
from __future__ import absolute_import
from __future__ import print_function
import datetime
import json
import logging
import os
import pprint
import subprocess32
import sys
import time
import textwrap
import humanize
from omega.symbolic import symbolic as _symbolic
import natsort
import networkx as nx
from omega.logic import bitvector
import psutil


logger = logging.getLogger(__name__)
DETAILS_LOG = 'details.txt'
SLUGS_SPEC = 'slugs.txt'
SLUGS_NICE = 'slugs_readable.txt'
STRATEGY_FILE = 'slugs_strategy.txt'


def synthesize(spec, symbolic=True, filename=None):
    """Return `True` if realizable, dump strategy to `filename`.

    @param spec: first-order Street(1)
    @type spec: `omega.symbolic.symbolic.Automaton`
    @param symbolic: select between symbolic and enumerated transducer
    @param filename: dump strategy in this file
        If symbolic, then this is a `dddmp` file (see `cudd`).
        If enumerated, then this is a `json` file (see `gr1c`).
    """
    if filename is None:
        strategy_file = STRATEGY_FILE
    else:
        strategy_file = filename
    logger.info('++ compile LTL to slugsin\n')
    aut = _symbolic._bitblast(spec)
    s = _to_slugs(aut)
    logger.info((
        '\n\n spec:\n\n {spec}'
        '\n\n slugsin:\n\n {s}'
        '-- done compiling to slugsin').format(spec=spec, s=s))
    # debug dump
    with open(SLUGS_SPEC, 'w') as f:
        f.write(s)
    w = textwrap.fill(s, replace_whitespace=False)
    with open(SLUGS_NICE, 'w') as f:
        f.write(w)
    realizable = _call_slugs(SLUGS_SPEC, symbolic, strategy_file)
    return realizable


def load_enumerated_strategy(json_file, spec):
    """Return transducer for strategy in `bdd_file`.

    @param json_file: `
    @type json_file: `str`
    @type spec: `omega.symbolic.symbolic.Automaton`
    """
    with open(json_file, 'r') as f:
        out = f.read()
    g = loads_enumerated_strategy(out)
    aut = _symbolic._bitblast(spec)
    h = bitvector.bitfield_to_int_states(g, aut.vars)
    return h


def loads_enumerated_strategy(s):
    """Return `networkx.DiGraph` for strategy in `s`.

    @type s: JSON `str`
    """
    dout = json.loads(s)
    g = nx.DiGraph()
    dvars = dout['variables']
    for stru, d in dout['nodes'].iteritems():
        u = int(stru)
        state = dict(zip(dvars, d['state']))
        g.add_node(u, state=state)
        for v in d['trans']:
            g.add_edge(u, v)
    logger.debug(
        ('loaded strategy with vertices:\n  {v}\n'
         'and edges:\n {e}\n').format(
            v='\n  '.join(str(x) for x in g.nodes(data=True)),
            e=g.edges()))
    return g


def _to_slugs(aut):
    """Return spec in `slugsin` format.

    @type aut: `omega.symbolic.symbolic.Automaton`.
    """
    dbits = bitvector.list_bits(aut.vars)
    print('number of unprimed bits: {n}'.format(n=len(dbits)))
    logger.debug(
        'slugs variables:\n{v}'.format(v=pprint.pformat(dbits)))
    f = _slugs_str
    return (
        _format_slugs_vars(dbits, 'env', 'INPUT') +
        _format_slugs_vars(dbits, 'sys', 'OUTPUT') +
        # env
        f(aut.init['env'], 'ENV_INIT') +
        f(aut.action['env'], 'ENV_TRANS') +
        f(aut.win['<>[]'], 'ENV_LIVENESS') +
        # sys
        f(aut.init['sys'], 'SYS_INIT') +
        f(aut.action['sys'], 'SYS_TRANS') +
        f(aut.win['[]<>'], 'SYS_LIVENESS'))


def _slugs_str(r, name, sep='\n'):
    if not r:
        return '[{name}]\n'.format(name=name)
    sep = ' {sep} '.format(sep=sep)
    f = sep.join(x for x in r if x)
    return '[{name}]\n{f}\n\n'.format(name=name, f=f)


def _format_slugs_vars(dvars, owner, name):
    a = [var for var, d in dvars.iteritems()
         if d['owner'] == owner]
    print('number of unprimed {owner} vars: {n}'.format(
        owner=owner, n=len(a)))
    a = natsort.natsorted(a)
    return '[{name}]\n{vars}\n\n'.format(
        name=name, vars='\n'.join(a))


def _call_slugs(filename, symbolic, strategy_file):
    """Call `slugs` and log memory usage and time."""
    options = ['slugs', filename]
    if symbolic:
        options.append('--symbolicStrategy')
    else:
        options.append('--jsonOutput')
    options.append(strategy_file)
    logger.debug('Calling: {cmd}'.format(cmd=' '.join(options)))
    # use a file, to avoid buffer deadlock of PIPE
    with open(DETAILS_LOG, 'w') as f:
        p = _popen(options, f)
        _log_process(p)
    _, err = p.communicate()
    # error ?
    if p.returncode != 0:
        raise Exception(err + str(p.returncode))
    # was realizable ?
    if 'Specification is realizable' in err:
        realizable = True
        logger.info('realizable')
    elif 'Specification is unrealizable' in err:
        realizable = False
        logger.info('not realizable')
    else:
        raise Exception(
            'slugs stderr does not say whether realizable')
    return realizable


def _popen(options, f):
    try:
        p = subprocess32.Popen(
            options,
            stdout=f,
            stderr=subprocess32.PIPE,
            bufsize=100)
    except OSError as e:
        if e.errno == os.errno.ENOENT:
            raise Exception('slugs not found in path.')
        else:
            raise
    return p


def _log_process(p):
    proc = psutil.Process(p.pid)
    logger.info('call slugs')
    while p.poll() is None:
        try:
            user, system = proc.cpu_times()
            rss, vms = proc.memory_info()
            t = user + system
            dt = datetime.timedelta(seconds=round(t, 1))
            s = 'time: {dt}, rss: {rss}, vms: {vms}'.format(
                dt=dt,
                rss=humanize.naturalsize(rss),
                vms=humanize.naturalsize(vms))
            logger.info(s)
            print(s, end='\r')
            sys.stdout.flush()  # python buffers `print`
        except psutil.AccessDenied:
            logger.debug('slugs has terminated already.')
        time.sleep(1.0)
    print(s)
    logger.info('slugs returned')
