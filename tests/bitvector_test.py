#!/usr/bin/env python
import logging
logger = logging.getLogger(__name__)
logging.getLogger('tulip.ltl_parser_log').setLevel(logging.WARNING)
h = logging.StreamHandler()
log = logging.getLogger('openpromela.bitvector')
log.setLevel(logging.WARNING)
log.addHandler(h)
import networkx as nx
from openpromela import bitvector as bv
from nose import tools as nt


# TODO: test truncation, test ALU up to 32 bits


def test_bitfield_to_int_states():
    t = {'x': dict(type='bool'),
         'y': dict(type='int', signed=True, bitnames=['y0', 'y1', 'y2'])}
    g = nx.DiGraph()
    w = [dict(x=1, y0=1, y1=1, y2=0),
         dict(x=0, y0=0, y1=1, y2=1),
         dict(x=1, y0=1, y1=1, y2=1)]
    for i, d in enumerate(w):
        g.add_node(i, state=d)
    g.add_edges_from([(0, 1), (1, 2), (2, 1)])
    h = bv.bitfield_to_int_states(g, t)
    assert set(h) == {0, 1, 2}
    assert set(h.edges()) == {(0, 1), (1, 2), (2, 1)}
    z = [dict(x=1, y=3), dict(x=0, y=-2), dict(x=1, y=-1)]
    for u, d in h.nodes_iter(data=True):
        assert z[u] == d['state']


def test_bitfields_to_ints():
    t = {'x': dict(type='bool'),
         'y': dict(type='int', signed=True, bitnames=['y0', 'y1', 'y2'])}
    bit_state = {'x': 0, 'y0': 0, 'y1': 1, 'y2': 1}
    d = bv.bitfields_to_ints(bit_state, t)
    assert d == {'x': 0, 'y': -2}


t = {'a': {'type': 'int',
           'signed': True,
           'bitnames': ['a0', 'a1']},
     'b': {'type': 'int',
           'signed': True,
           'bitnames': ['b0', 'b1']},
     'x': {'type': 'int',
           'signed': True,
           'bitnames': ['x@0.0.3', 'x@1']}}
parser = bv.Parser()


def test_flatten_comparator():
    """Test arithmetic predicates."""
    # tree = parser.parse('x + 1 <= 2')
    # print(repr(tree) + '\n')
    log.setLevel(logging.ERROR)
    # (in)equality
    assert parser.parse('a = 1').flatten(t=t) == '$ 1 ! | ^ a0 1 | ^ a1 0 0'
    assert parser.parse('a != 1').flatten(t=t) == '$ 1 | ^ a0 1 | ^ a1 0 0'
    # '<' comparator
    f = parser.parse('a < 1').flatten(t=t)
    # print(f)
    assert (f == ('$ 5 '
                  '^ ^ a0 ! 1 1 '
                  '| & a0 ! 1 & ^ a0 ! 1 1 '
                  '^ ^ a1 ! 0 ? 1 '
                  '| & a1 ! 0 & ^ a1 ! 0 ? 1 '
                  '^ ! ^ a1 0 ? 3'))
    # TODO: more bits, larger numbers


def test_flatten_arithmetic():
    """Test arithmetic functions."""
    # addition
    mem = list()
    res = parser.parse('a + 1').flatten(t=t, mem=mem)
    assert res == ['? 0', '? 2']
    assert mem == ['^ ^ a0 1 0',
                   '| & a0 1 & ^ a0 1 0',
                   '^ ^ a1 0 ? 1',
                   '| & a1 0 & ^ a1 0 ? 1']
    # TODO: subtraction


def test_barrel_shifter():
    x = ['x0', 'x1', 'x2', 'x3']
    y = ['y0', 'y1']
    m = ['& ! y0 x0',
         '| & ! y0 x1 & y0 x0',
         '| & ! y0 x2 & y0 x1',
         '| & ! y0 x3 & y0 x2',
         '& ! y1 ? 0',
         '& ! y1 ? 1',
         '| & ! y1 ? 2 & y1 ? 0',
         '| & ! y1 ? 3 & y1 ? 1']
    # stage -1
    z, mem = bv.barrel_shifter(x, y, -1)
    assert z == x
    assert mem == list()
    # stage 0
    z, mem = bv.barrel_shifter(x, y, 0)
    assert z == ['? 0', '? 1', '? 2', '? 3']
    assert len(mem) == 4
    assert mem == m[:4]
    # stage 1
    z, mem = bv.barrel_shifter(x, y, 1)
    print(z)
    print(bv._format_mem(mem))
    assert z == ['? 4', '? 5', '? 6', '? 7']
    assert len(mem) == 8
    assert mem == m
    # fun: (2**n)-bit x
    # n = 5
    # x = ['x{i}'.format(i=i) for i in xrange(2**n)]
    # y = ['y{i}'.format(i=i) for i in xrange(n)]
    # z, mem = sl.barrel_shifter(x, y)
    # print(z)
    # print(sl._format_mem(mem))


def test_truncate():
    x = list('01010100011')
    n = 4
    r = bv.truncate(x, n)
    assert len(r) == n
    assert r == list('0101')


def test_twos_complement_for_var():
    t = {'x': {'type': 'bool'},
         'y': {'type': 'int', 'signed': True, 'bitnames': ['y0', 'y1']},
         'z': {'type': 'int', 'signed': False, 'bitnames': ['z0']}}
    with nt.assert_raises(Exception):
        bv.var_to_twos_complement('r', t)
    with nt.assert_raises(TypeError):
        bv.var_to_twos_complement('x', t)
    assert bv.var_to_twos_complement('y', t) == ['y0', 'y1']
    assert bv.var_to_twos_complement('z', t) == ['z0', '0']


def test_twos_complement_for_int():
    f = bv.twos_complement_to_int
    g = bv.int_to_twos_complement
    pairs = {1: ['1', '0'],
             2: ['0', '1', '0'],
             5: ['1', '0', '1', '0'],
             -1: ['1', '1'],
             -2: ['0', '1', '1']}
    for k, v in pairs.iteritems():
        assert g(k) == v
        assert k == f(v)
    pairs = {-1: ['1', '1', '1'],
             -2: ['0', '1', '1', '1'],
             2: ['0', '1', '0', '0']}
    for k, v in pairs.iteritems():
        assert k == f(v)


def test_equalize_width():
    x = list('0101')
    y = list('10')
    p, q = bv.equalize_width(x, y)
    assert len(p) == len(q) == 4
    for a in p[len(x):]:
        assert a == x[-1]
    for a in q[len(y):]:
        assert a == y[-1]


def test_sign_extension():
    t = {'a': {'type': 'int',
               'signed': True,
               'bitnames': ['a0', 'a1']},
         'b': {'type': 'int',
               'signed': True,
               'bitnames': ['b0', 'b1']}}
    parser = bv.Parser()
    with nt.assert_raises(ValueError):
        bv.sign_extension(['1'], 2)
    with nt.assert_raises(ValueError):
        bv.sign_extension(['1', '1'], 0)
    assert bv.sign_extension(['1', '1'], 3) == ['1', '1', '1']
    assert bv.sign_extension(['1', '0'], 3) == ['1', '0', '0']
    with nt.assert_raises(AssertionError):
        mem = list()
        parser.parse('a + 1').flatten(t=t)
    with nt.assert_raises(AssertionError):
        parser.parse('b < -1').flatten(t=t, mem=mem)


def test_ite():
    # ite connective
    x = 'x'
    y = 'y'
    z = 'z'
    s = bv.ite_connective(x, y, z)
    r = '$ 2 x | & y ? 0 & z ! ? 0'
    assert s == r, s
    # ite connective flattening
    t = {'x': {'type': 'bool'},
         'y': {'type': 'bool'},
         'z': {'type': 'bool'}}
    parser = bv.Parser()
    p = parser.parse('(ite x, y, z)')
    s = p.flatten(t=t)
    assert s == r, s
    with nt.assert_raises(AssertionError):
        bv.ite_connective('a', ['b', 'c'], 'd')
    # ite function
    x = 'x'
    y = ['y0', 'y1']
    z = ['z0', 'z1']
    mem = list()
    r = bv.ite_function(x, y, z, mem)
    correct = [
        'x',
        '| & y0 ? 0 & z0 ! ? 0',
        '| & y1 ? 0 & z1 ! ? 0']
    assert mem == correct, mem
    assert r == ['? 1', '? 2']
    # flip
    r = bv.ite_function(x, z, y, mem)
    correct.extend([
        'x',
        '| & z0 ? 3 & y0 ! ? 3',
        '| & z1 ? 3 & y1 ! ? 3'])
    assert mem == correct, mem
    assert r == ['? 4', '? 5']
    # ite function flattening
    t = {'x': {'type': 'bool'},
         'y': {'type': 'int',
               'signed': True,
               'bitnames': ['a0', 'a1']},
         'z': {'type': 'int',
               'signed': True,
               'bitnames': ['b0', 'b1']}}
    mem = list()
    r = p.flatten(t=t, mem=mem)
    assert mem == [
        'x',
        '| & a0 ? 0 & b0 ! ? 0',
        '| & a1 ? 0 & b1 ! ? 0']
    assert r == ['? 1', '? 2']
    with nt.assert_raises(AssertionError):
        bv.ite_function('x', ['y0'], ['z0', 'z1', 'z2'], list())


if __name__ == '__main__':
    test_ite()
