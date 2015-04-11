"""Interface to `slugs` synthesizer."""
from __future__ import absolute_import
import datetime
import json
import logging
import os
import pprint
import subprocess
import time
import tempfile
import textwrap
import humanize
import logic.symbolic
import natsort
import networkx as nx
from openpromela import bitvector
import psutil


logger = logging.getLogger(__name__)
slugs_log = logging.getLogger(__name__ + '.slugs')
SLUGS_SPEC = 'slugs.txt'
SLUGS_NICE = 'slugs_readable.txt'
BDD_FILE = 'bdd.txt'


def synthesize(spec, symbolic=True, bddfile=None, make=True):
    """Return strategy satisfying the specification `spec`.

    @param spec: first-order Street(1)
    @type spec: `symbolic.Automaton`
    @param symbolic: select between symbolic and enumerated transducer
    @param bddfile: CUDD dumps the strategy in this file
    @param make: if `False`, then only check realizability

    @return: If realizable return synthesized strategy, otherwise `None`.
    @rtype: `automata.Transducer` or `symbolic.Automaton`
    """
    logger.info('++ compile LTL to slugsin\n')
    aut = logic.symbolic._bitblast(spec)
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
    realizable, out = _call_slugs(
        fin.name, symbolic=symbolic, bddfile=bddfile, make=make)
    os.unlink(fin.name)
    logger.debug('slugs output:\n{out}'.format(out=out))
    if realizable:
        logger.info('realizable')
    else:
        logger.info('not realizable')
    # symbolic strategies not loaded from file yet
    if symbolic:
        return realizable
    if not realizable:
        return None
    g = load_strategy(out)
    logger.debug(
        ('loaded strategy with vertices:\n  {v}\n'
         'and edges:\n {e}\n').format(
            v='\n  '.join(str(x) for x in g.nodes(data=True)),
            e=g.edges()))
    h = bitvector.bitfield_to_int_states(g, aut.vars)
    mealy = strategy_to_mealy(h, spec)
    return mealy


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
    a = natsort.natsorted(a)
    return '[{name}]\n{vars}\n\n'.format(name=name, vars='\n'.join(a))


def _call_slugs(filename, symbolic=True, bddfile=None, make=True):
    """Call `slugs` and log memory usage and time."""
    if bddfile is None:
        bddfile = BDD_FILE
    options = ['slugs', filename]
    if make:
        if symbolic:
            options.extend(['--symbolicStrategy', bddfile])
        else:
            options.append('--jsonOutput')
    else:
        options.append('--onlyRealizability')
    logger.debug('Calling: {cmd}'.format(cmd=' '.join(options)))
    try:
        p = subprocess.Popen(
            options,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE)
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
            dt = datetime.timedelta(seconds=t)
            s = 'time: {dt}, rss: {rss}, vms: {vms}'.format(
                dt=dt,
                rss=humanize.naturalsize(rss),
                vms=humanize.naturalsize(vms))
            slugs_log.info(s)
        except psutil.AccessDenied:
            logger.debug('slugs has terminated already.')
        time.sleep(1.0)
    slugs_log.info('slugs returned')
    out, err = p.communicate()
    msg = (
        '\n slugs return code: {c}\n\n'.format(c=p.returncode) +
        '\n slugs stdrr: {c}\n\n'.format(c=err) +
        '\n slugs stdout:\n\n {out}\n\n'.format(out=out))
    logger.debug(msg)
    # error ?
    if p.returncode != 0:
        raise Exception(msg)
    realizable = 'Specification is realizable' in err
    # check sanity
    if not realizable:
        assert 'Specification is unrealizable' in err
    return realizable, out
