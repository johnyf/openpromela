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
import tempfile
import textwrap
import humanize
from omega.symbolic import symbolic as _symbolic
import natsort
import networkx as nx
from openpromela import bitvector
import psutil


logger = logging.getLogger(__name__)
slugs_log = logging.getLogger(__name__ + '.slugs')
details_log = logging.getLogger(__name__ + '.details')
SLUGS_SPEC = 'slugs.txt'
SLUGS_NICE = 'slugs_readable.txt'
STRATEGY_FILE = 'slugs_strategy.txt'


def synthesize(spec, symbolic=True, filename=None, make=True):
    """Return strategy satisfying the specification `spec`.

    @param spec: first-order Street(1)
    @type spec: `symbolic.Automaton`
    @param symbolic: select between symbolic and enumerated transducer
    @param filename: dump strategy in this file
        If symbolic, then this is a `dddmp` file (see `cudd`).
        If enumerated, then this is a `json` file (see `gr1c`).
    @param make: if `False`, then only check realizability

    @return: If realizable, then return `True` for symbolic
        strategies (load them separately),
        and a `networkx.DiGraph` for enumerated strategies.
        If unrealizable, then return `None`.
    """
    if filename is None:
        strategy_file = STRATEGY_FILE
    logger.info('++ compile LTL to slugsin\n')
    aut = _symbolic._bitblast(spec)
    s = _to_slugs(aut)
    # dump for use in manual debugging
    if logger.getEffectiveLevel() < logging.DEBUG:
        with open(SLUGS_SPEC, 'w') as f:
            f.write(s)
        with open(SLUGS_NICE, 'w') as f:
            w = textwrap.fill(s, replace_whitespace=False)
            f.write(w)
    # call slugs
    with tempfile.NamedTemporaryFile(delete=False) as fin:
        fin.write(s)
    logger.info('\n\n spec:\n\n {spec}'.format(
        spec=spec) + '\n\n slugs in:\n\n {s}\n'.format(s=s))
    logger.info('-- done compiling to slugsin')
    realizable = _call_slugs(fin.name, symbolic, strategy_file, make)
    os.unlink(fin.name)
    # logger.debug('slugs output:\n{out}'.format(out=out))
    if realizable:
        logger.info('realizable')
    else:
        logger.info('not realizable')
    # symbolic strategies not loaded from file yet
    if symbolic:
        return realizable
    if not realizable:
        return None
    # enumerated strategy
    with open(strategy_file, 'r') as f:
        out = f.read()
        g = load_strategy(out)
    logger.debug(
        ('loaded strategy with vertices:\n  {v}\n'
         'and edges:\n {e}\n').format(
            v='\n  '.join(str(x) for x in g.nodes(data=True)),
            e=g.edges()))
    h = bitvector.bitfield_to_int_states(g, aut.vars)
    return h


def load_strategy(filename):
    """Return `networkx.DiGraph` for strategy in JSON file."""
    dout = json.loads(filename)
    # use nx graph to represent strategy
    g = nx.DiGraph()
    dvars = dout['variables']
    for stru, d in dout['nodes'].iteritems():
        u = int(stru)
        state = dict(zip(dvars, d['state']))
        g.add_node(u, state=state)
        for v in d['trans']:
            g.add_edge(u, v)
    return g


def _to_slugs(aut):
    """Return spec in `slugsin` format.

    @type aut: `symbolic.Automaton`.
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
        f(aut.win['env'], 'ENV_LIVENESS') +
        # sys
        f(aut.init['sys'], 'SYS_INIT') +
        f(aut.action['sys'], 'SYS_TRANS') +
        f(aut.win['sys'], 'SYS_LIVENESS'))


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
    return '[{name}]\n{vars}\n\n'.format(name=name, vars='\n'.join(a))


def _call_slugs(filename, symbolic, strategy_file, make):
    """Call `slugs` and log memory usage and time."""
    options = ['slugs', filename]
    if make:
        if symbolic:
            options.append('--symbolicStrategy')
        else:
            options.append('--jsonOutput')
        options.append(strategy_file)
    else:
        options.append('--onlyRealizability')
    logger.debug('Calling: {cmd}'.format(cmd=' '.join(options)))
    f = open('slugs_details.txt', 'w')
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
    proc = psutil.Process(p.pid)
    slugs_log.info('call slugs')
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
            slugs_log.info(s)
            print(s, end='\r')
            sys.stdout.flush()
        except psutil.AccessDenied:
            logger.debug('slugs has terminated already.')
        time.sleep(1.0)
    print(s)
    slugs_log.info('slugs returned')
    _, err = p.communicate()
    f.close()
    #msg = (
    #    '\n slugs return code: {c}\n\n'.format(c=p.returncode) +
    #    '\n slugs stderr: {c}\n\n'.format(c=err) +
    #    '\n slugs stdout:\n\n {out}\n\n'.format(out=out))
    #logger.debug(msg)
    #details_log.info(out)
    # error ?
    if p.returncode != 0:
        raise Exception(p.returncode)
    realizable = 'Specification is realizable' in err
    # check sanity
    if not realizable:
        assert 'Specification is unrealizable' in err
    return realizable
