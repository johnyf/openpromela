#!/usr/bin/env python
"""Bit-blasting for signed integer arithmetic.

This module translates Boolean formulas that can
contain arithmetic expressions involving signed integers
to bitvector propositinal formulas.

Reference
=========

Chapter 6, in particular pp. 158--159 from:
Kroening D. and Strichman O.
Decision Procedures, Springer
"""
from __future__ import absolute_import
import logging
import math
import networkx as nx
from logic import lexyacc
from logic.ast import Nodes as _Nodes


logger = logging.getLogger(__name__)


def bitblast(f, t):
    """Flatten formula `f` to bitvector logic.

    @param f: unquantified first-order temporal logic formula
    @type f: `str`
    @param t: symbol table
    @type t: `dict`
    """
    tree = parser.parse(f)
    return tree.flatten(t=t)


def bitblast_table(table):
    """Return table of variables for bitvectors."""
    t = dict()
    init = {'env': list(), 'sys': list()}
    safety = {'env': list(), 'sys': list()}
    for var, d in table.iteritems():
        dtype = d['type']
        owner = d['owner']
        if dtype in ('boolean', 'bool'):
            b = dict(type='bool', owner=owner)
        elif dtype in ('saturating', 'modwrap', 'int'):
            dom = d['dom']
            assert len(dom) == 2, dom
            signed, width = dom_to_width(dom)
            b = dict(type='int', owner=owner,
                     signed=signed, width=width,
                     dom=dom)
        else:
            raise Exception(
                'unknown type: "{dtype}"'.format(dtype=dtype))
        if dtype == 'int':
            print('warning: "int" found as type '
                  '(instead of "saturating")')
        t[var] = b
        # initial value
        # imperative var or free var assigned at decl ?
        ival = d.get('init')
        if ival is not None:
            c = init_to_logic(var, d)
            init[owner].append(c)
        # ranged bitfield safety constraints
        if dtype == 'boolean':
            continue
        # int var
        # saturating semantics ?
        if dtype != 'saturating':
            continue
        dmin, dmax = dom
        safety[owner].append(
            '({min} <= {x}) & ({x} <= {max})'.format(
                min=dmin, max=dmax, x=var))
    check_data_types(t)
    add_bitnames(t)
    logger.info('-- done bitblasting vars table\n')
    return t, init, safety


def init_to_logic(var, d):
    """Return logic formulae for initial condition."""
    if d['type'] == 'boolean':
        op = '<->'
    else:
        op = '='
    return '{var} {op} {value}'.format(
        op=op, var=var, value=d['init'])


def dom_to_width(dom):
    """Return whether integer variable is signed and its bit width.

    @param dom: the variable's range
    @type dom: `(MIN, MAX)` where `MIN, MAX` are integers
    """
    minval, maxval = dom
    logger.debug('int in ({m}, {M})'.format(
        m=minval, M=maxval))
    signed = (minval < 0) or (maxval < 0)
    absval = max(abs(minval), abs(maxval))
    width = absval.bit_length()
    if width == 0:
        assert minval == maxval
        # TODO: optimize by substituting values
        # for variables that are constants
        width = 1
    if signed:
        width = width + 1
    return signed, width


def add_bitnames(t):
    # str_to_int not needed, because there
    # are no string variables in Promela
    for var, d in t.iteritems():
        if d['type'] == 'int':
            d['bitnames'] = ['{name}_{i}'.format(name=var, i=i)
                             for i in xrange(d['width'])]


def check_data_types(t):
    types = {'bool', 'int'}
    for var, d in t.iteritems():
        if d['type'] in types:
            continue
        raise Exception(
            'unknown type: "{dtype}"'.format(dtype=d['type']))


def list_bits(dvars):
    """Return symbol table of bits (comprising bitfields).

    For symbol table definition, see `bitblast`.

    @param dvars: symbol table of integer and Boolean vars
    @type dvars: `dict` of `dict`
    @return: symbol table of bits
    @rtype: `dict` of `dict`
    """
    dout = dict()
    for var, d in dvars.iteritems():
        dtype = d['type']
        if dtype == 'int':
            c = d['bitnames']
        elif dtype == 'bool':
            c = [var]
        else:
            raise Exception(
                'unknown type "{t}"'.format(t=dtype))
        owner = d['owner']
        assert owner in {'env', 'sys'}, owner
        for bit in c:
            dout[bit] = dict(type='bool', owner=owner)
    return dout


def bitfield_to_int_states(g, t):
    """Convert bitfields to integers for "state" at each strategy node.

    @type g: `networkx.DiGraph`
    @type t: `VariablesTable`

    @rtype: `networkx.Digraph`
    """
    h = nx.DiGraph()
    for u, d in g.nodes_iter(data=True):
        bit_state = d['state']
        int_state = bitfields_to_ints(bit_state, t)
        h.add_node(u, state=int_state)
    for u, v in g.edges_iter():
        h.add_edge(u, v)
    # remove deadends, where env looses
    s = {1}
    while s:
        s = {n for n in h if not h.succ.get(n)}
        h.remove_nodes_from(s)
    logger.debug(
        ('converted bitfields to integers.\n'
         'Strategy with vertices:\n  {v}\n'
         'and edges:\n {e}\n').format(
            v='\n  '.join(str(x) for x in h.nodes(data=True)),
            e=h.edges()))
    return h


def bitfields_to_ints(bit_state, t):
    """Convert bits to integer for state `dict`.

    @param bit_state: assignment to all bits
    @type bit_state: `dict`
    @type t: `VariablesTable`
    """
    int_state = dict()
    for flatname, d in t.iteritems():
        if d['type'] == 'bool':
            int_state[flatname] = bit_state[flatname]
            continue
        # this is an integer var
        bitnames = d['bitnames']
        bitvalues = [bit_state[b] for b in bitnames]
        if not d['signed']:
            bitvalues.append('0')
        int_state[flatname] = twos_complement_to_int(bitvalues)
    return int_state


class Parser(lexyacc.Parser):
    """LTL parser for signed arithmetic with truncation."""

    tabmodule = 'slugsin_parsetab'

    def __init__(self):
        super(Parser, self).__init__(nodes=Nodes())

    def p_truncator(self, p):
        """expr : expr TRUNCATE number"""
        p[0] = self.nodes.Truncator(p[2], p[1], p[3])


def make_table(d, env_vars=None):
    """Return symbol table from "simple" `dict`."""
    if env_vars is None:
        env_vars = set()
    t = dict()
    for var, dom in d.iteritems():
        if dom == 'bool':
            dtype = 'bool'
            dom = None
        else:
            assert isinstance(dom, tuple), (var, dom)
            assert len(dom) == 2, (var, dom)
            dtype = 'saturating'
        if var in env_vars:
            owner = 'env'
        else:
            owner = 'sys'
        t[var] = dict(type=dtype, dom=dom, owner=owner)
    return t


def make_dummy_table():
    t = dict(x=dict(type='bool', owner='env'),
             y=dict(type='bool', owner='sys'),
             z=dict(type='int', owner='env', signed=False, width=2),
             w=dict(type='int', owner='env', signed=False, width=2))
    return t


class Nodes(_Nodes):
    """Return object with AST node classes as attributes."""
    opmap = {
        'false': '0', 'true': '1',
        '!': '!',
        '|': '|', '&': '&', '->': '| !', '<->': '! ^',
        'ite': 'ite',
        'X': '',
        # 'G': '[]', 'F': '<>',
        '<': '<', '<=': '<=', '=': '=', '>=': '>=', '>': '>', '!=': '!=',
        '+': '+', '-': '-'}

    class Operator(_Nodes.Operator):
        def flatten(self, mem=None, *arg, **kw):
            if self.operator != 'ite':
                return super(Nodes.Operator, self).flatten(mem=mem, *arg, **kw)
            # ternary conditional
            assert self.operator == 'ite'
            x = self.operands[0].flatten(mem=None, *arg, **kw)
            y = self.operands[1].flatten(mem=mem, *arg, **kw)
            z = self.operands[2].flatten(mem=mem, *arg, **kw)
            # ternary connective ?
            if mem is None:
                return ite_connective(x, y, z)
            else:
                return ite_function(x, y, z, mem=mem)

    class Unary(_Nodes.Unary):
        def flatten(self, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            if self.operator == 'X':
                kw.update(prime=True)
                # avoid making it a string
                # (because in arithmetic context it is a list)
                return self.operands[0].flatten(*arg, **kw)
            return ' {op} {x}'.format(
                op=Nodes.opmap[self.operator],
                x=self.operands[0].flatten(*arg, **kw))

    # prefix and rm parentheses
    class Binary(_Nodes.Binary):
        def flatten(self, *arg, **kw):
            """Prefix flattener."""
            logger.info('flatten "{s}"'.format(s=repr(self)))
            x = self.operands[0].flatten(*arg, **kw)
            y = self.operands[1].flatten(*arg, **kw)
            assert isinstance(x, basestring), x
            assert isinstance(y, basestring), y
            return ' {op} {x} {y} '.format(
                op=Nodes.opmap[self.operator], x=x, y=y)

    class Var(_Nodes.Var):
        def flatten(self, prime=None, mem=None, t=None, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            name = self.value
            # not arithmetic scope ?
            if mem is None:
                # must be Boolean variable
                assert_var_in_table(name, t)
                v = t[name]
                assert v['type'] == 'bool', v['type']
                return '{v}{prime}'.format(
                    v=name, prime="'" if prime else '')
            # arithmetic context
            # must be integer variable
            bits = var_to_twos_complement(name, t)
            bits = ["{b}{prime}".format(
                b=b, prime="'" if b[0].isalpha() and prime else '')
                for b in bits]
            return bits

    class Num(_Nodes.Num):
        def flatten(self, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            return int_to_twos_complement(self.value)

    class Bool(_Nodes.Bool):
        def flatten(self, *arg, **kw):
            return Nodes.opmap[self.value.lower()]

    class Truncator(_Nodes.Binary):
        def flatten(self, *arg, **kw):
            logger.info('[++ flatten "{s}"'.format(s=repr(self)))
            p = self.operands[0].flatten(*arg, **kw)
            assert isinstance(p, list), p
            y = self.operands[1]
            assert isinstance(y, Nodes.Num), (type(y), y)
            n = int(y.value)
            tr = truncate(p, n)
            # if extended, should not use MSB of truncation
            tr.append('0')
            logger.debug('truncation result: {tr}\n'.format(tr=tr))
            logger.info('--] done flattening truncator.\n')
            return tr

    class Comparator(_Nodes.Comparator):
        def flatten(self, mem=None, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            assert mem is None, (
                '"{expr}" appears in arithmetic scope'.format(
                    expr=self))
            mem = list()
            p = self.operands[0].flatten(mem=mem, *arg, **kw)
            q = self.operands[1].flatten(mem=mem, *arg, **kw)
            return flatten_comparator(self.operator, p, q, mem)

    class Arithmetic(_Nodes.Arithmetic):
        def flatten(self, mem=None, *arg, **kw):
            logger.info('flatten "{s}"'.format(s=repr(self)))
            # only for testing purposes
            assert mem is not None, (
                'Arithmetic formula "{f}" in Boolean scope.'.format(
                    f=self))
            p = self.operands[0].flatten(mem=mem, *arg, **kw)
            q = self.operands[1].flatten(mem=mem, *arg, **kw)
            return flatten_arithmetic(self.operator, p, q, mem)


parser = Parser()


def flatten_comparator(operator, x, y, mem):
    """Return flattened comparator formula."""
    logger.info('++ flatten comparator "{op}" ...'.format(op=operator))
    assert isinstance(x, list)
    assert isinstance(y, list)
    p, q = equalize_width(x, y)
    assert len(p) == len(q)
    logger.debug('p = {p}\nq = {q}'.format(p=p, q=q))
    negate = False
    if operator in {'=', '!='}:
        r = inequality(p, q, mem)
        if operator == '=':
            negate = True
        else:
            assert operator == '!='
    elif operator in {'<', '<=', '>=', '>'}:
        swap = False
        if operator == '<=':
            negate = True
            swap = True
        elif operator == '>':
            swap = True
        elif operator == '>=':
            negate = True
        else:
            assert operator == '<'
        if swap:
            p, q = q, p
        r = less_than(p, q, mem)
    else:
        raise ValueError('Unknown operator "{op}"'.format(op=operator))
    if negate:
        r = '! {r}'.format(r=r)
    mem.append(r)
    logger.debug('mem = {mem}'.format(mem=_format_mem(mem=mem)))
    logger.debug('-- done flattening "{op}"\n'.format(op=operator))
    return '$ {n} {s}'.format(n=len(mem), s=' '.join(mem))


def inequality(p, q, mem):
    """Return bitvector propositional formula for '!='"""
    assert len(p) == len(q)
    return ' '.join('| ^ {a} {b}'.format(a=a, b=b)
                    for a, b in zip(p, q)) + ' 0'


def less_than(p, q, mem):
    """Return bitvector propositional formula for '<'"""
    res, res_mem, carry = adder_subtractor(p, q, add=False, start=len(mem))
    mem.extend(res_mem)
    return '^ ! ^ {a} {b} {carry}'.format(a=p[-1], b=q[-1], carry=carry)


def flatten_arithmetic(operator, p, q, mem):
    """Return flattened arithmetic expression."""
    logger.info('++ flatten arithmetic operator "{op}"'.format(op=operator))
    assert isinstance(p, list)
    assert isinstance(q, list)
    if operator in {'+', '-'}:
        add = (operator == '+')
        result, res_mem, _ = adder_subtractor(p, q, add, start=len(mem))
        mem.extend(res_mem)
    elif operator in {'*', '/', '%'}:
        raise NotImplementedError(
            'multiplication, division, modulo are not implemened yet.'
            ' In any case, BDDs are inefficient for representing them.')
    else:
        raise ValueError(
            'Unknown arithmetic operator "{op}"'.format(op=operator))
    logger.info('-- done flattening "{op}"\n'.format(op=operator))
    return result


def multiplier(x, y, s=None, start=0):
    """Return the unsigned product of `x` and `y`."""
    # caution: this is unsigned
    assert len(x) == len(y)
    assert start >= 0
    if s is None:
        s = len(y) - 1
    assert -1 <= s < len(x)
    # base stage: -1
    if s == -1:
        mem = list()
        return y, mem
    # stages: 0 ... n - 1
    shifted_x = fixed_shift(x, s)
    z = ['& {a} {b}'.format(a=a, b=y[s]) for a in shifted_x]
    mul_res, mem = multiplier(x, y, s=s - 1, start=start)
    res, sum_mem, carry = adder_subtractor(
        mul_res, z, add=True, start=len(mem) + start)
    mem.extend(sum_mem)
    assert len(res) == len(x)
    return res, mem


def adder_subtractor(x, y, add=True, start=0):
    """Return sum of `p` and `q`, w/o truncation.

    Implements a ripple-carry adder-subtractor.
    The control signal is `add`.

    Reference
    =========
    https://en.wikipedia.org/wiki/Adder%E2%80%93subtractor
    https://en.wikipedia.org/wiki/Adder_%28electronics%29

    @param x: two's complement representation
    @type x: `list` of bits
    @param y: two's complement representation
    @type y: `list` of bits
    @param add: if `True` then add, otherwise subtract
    @type add: `bool`
    @param start: insert first element at this index in memory structure
    @type start: `int` >= 0
    """
    assert start >= 0
    assert isinstance(x, list)
    assert isinstance(y, list)
    dowhat = 'add' if add else 'subtract'
    logger.info('++ {what}...'.format(what=dowhat))
    p, q = equalize_width(x, y)
    assert len(p) == len(q)
    logger.debug('p = {p}\nq = {q}'.format(p=p, q=q))
    # invert
    if add:
        carry = '0'
    else:
        q = ['! {bit}'.format(bit=b) for b in q]
        carry = '1'
    mem = list()
    result = list()
    # use a loop to emphasize the relation between mem, result, carries
    for i, (a, b) in enumerate(zip(p, q)):
        k = start + 2 * i
        r = k + 1
        # full-adder
        # result
        mem.append('^ ^ {a} {b} {c}'.format(a=a, b=b, c=carry))
        result.append('? {k}'.format(k=k))
        # carry
        mem.append('| & {a} {b} & ^ {a} {b} {c}'.format(a=a, b=b, c=carry))
        carry = '? {r}'.format(r=r)
    assert len(mem) == 2 * len(result)
    logger.debug('mem = {mem}\nres = {res}'.format(
        mem=_format_mem(mem), res=result))
    logger.info('-- done {what}ing\n'.format(what=dowhat))
    return result, mem, carry


def barrel_shifter(x, y, s=None, start=0):
    """Return left or right shift formula.

    Recursive implementatin of barrel shifter.
    Note that the shift distance must be represented as unsigned.

    @param x: shift (vector that is to be shifted)
    @type x: `list` of `str`
    @param y: shift distance
    @type y: `list` of `str` with `len(y) == math.log(len(x), 2)`
    @param s: desired stage of barrel shifter
    @type s: `int` with: `-1 <= s < len(y)`
    @param start: memory address to start indexing from
    @type start: `int` >= 0

    @return: 2-tuple:
      1. elements of composition of first `s` stages
      2. memory contents from stage 0 to stage `s`
    @rtype: `tuple([list, list])`
    """
    assert len(y) == math.log(len(x), 2)
    if s is None:
        s = len(y) - 1
    assert -1 <= s < len(y)
    assert start >= 0
    # base stage: -1
    if s == -1:
        mem = list()
        return x, mem
    # stages: 0 ... n - 1
    r, mem = barrel_shifter(x, y, s - 1, start=start)
    for i, a in enumerate(x):
        b = y[s]
        g = r[i]
        h = r[i - 2**s]
        if i < 2**s:
            z = '& ! {b} {g}'.format(b=b, g=g)
        else:
            z = '| & ! {b} {g} & {b} {h}'.format(b=b, g=g, h=h)
        mem.append(z)
    n = len(x)
    m = len(mem) - n
    c = ['? {i}'.format(i=i + m) for i in xrange(n)]
    assert len(c) == len(x)
    return c, mem


def fixed_shift(x, c):
    """Shift `x` left by fixed distance `s`.

    @param x: shift (vector to be shifted)
    @type x: `list` of `str`
    @param c: shift distance
    @type c: `int` with: `0 <= c <= len(x)`

    @return: shifted `x`
    @rtype: `list` of `str`
    """
    n = len(x)
    assert 0 <= c <= n
    return c * ['0'] + x[:n - c]


def truncate(x, n):
    """Return first `n` bits of bitvector `x`.

    @type x: `list`
    @type n: `int` >= 0

    @rtype: `list`
    """
    assert n >= 0
    return x[:n]


def ite_function(a, b, c, mem):
    """Return memory buffer elements for ite between integers.

    @param a: propositinal formula
    @type a: `str`

    @param b, c: arithmetic formula
    @type b, c: `list`

    @param start: continue indexing buffer cells from this value
    @type start: `int`

    @rtype: `list`
    """
    assert isinstance(a, basestring)
    assert isinstance(b, list)
    assert isinstance(c, list)
    assert len(b) == len(c)
    start = len(mem)
    m = list()
    m.append(a)
    for p, q in zip(b, c):
        s = '| & {p} ? {i} & {q} ! ? {i}'.format(p=p, q=q, i=start)
        m.append(s)
    mem.extend(m)
    r = ['? {i}'.format(i=i + start + 1) for i, _ in enumerate(b)]
    return r


def ite_connective(a, b, c):
    """Return memory buffer for ternary conditional operator.

    Note that economizes by avoiding rewrite formulae.
    In Boolean context, the arguments a, b, c will always
    be variables of type bit, or Boolean constants,
    or the result of expressions as a memory buffer.

    @rtype: `str`
    """
    assert isinstance(a, basestring)
    assert isinstance(b, basestring)
    assert isinstance(c, basestring)
    # local memory buffer
    return '$ 2 {a} | & {b} ? {i} & {c} ! ? {i}'.format(a=a, b=b, c=c, i=0)


def var_to_twos_complement(p, t):
    """Return `list` of bits in two's complement."""
    # little-endian encoding
    logger.info('++ encode variable "{p}" to 2s complement'.format(p=p))
    assert_var_in_table(p, t)
    v = t[p]
    # arithmetic operators defined only for integers
    if v['type'] == 'bool':
        raise TypeError(
            '2s complement undefined for Boolean variable "{p}"'.format(p=p))
    bits = list(v['bitnames'])
    logger.debug('bits of "{p}": {bits}"'.format(p=p, bits=bits))
    if v['signed']:
        logger.debug('variable "{p}" is signed'.format(p=p))
        if len(bits) < 2:
            raise ValueError(
                'A signed bitvector must have at least 2 bits.\n'
                'Got instead, for variable "{p}",'.format(p=p) +
                ' the bitvector:\n\t {bits}'.format(bits=bits))
    else:
        logger.debug('variable "{p}" is unsigned'.format(p=p))
        bits.append('0')
    assert len(bits) > 1
    logger.debug('encoded variable "{p}":\n\t{bits}'.format(
        p=p, bits=bits))
    logger.info('-- done encoding variable "{p}".\n'.format(p=p))
    return bits


def assert_var_in_table(name, t):
    """Raise `Exception` if variable `name` not in table `t`."""
    # not in variables table ?
    if name in t:
        return
    raise Exception(
        'Variable "{name}" missing from symbol table:\n{t}'.format(
            name=name, t=t))


def int_to_twos_complement(s):
    """Return two's complement of `s` as `list` of `str`.

    @type s: such that `int(s)` is well-defined
    """
    logger.info('++ convert integer "{s}" to 2s complement'.format(s=s))
    x = int(s)
    if x >= 0:
        sign_bit = '0'
        y = x
    else:
        sign_bit = '1'
        n = x.bit_length()
        y = 2**n + x
    # zfill catches the case: y == 0, because lstrip removes 0
    bits = list(reversed(bin(y).lstrip('-0b').zfill(1)))
    bits.append(sign_bit)
    assert x == twos_complement_to_int(bits)
    assert len(bits) > 1
    # bits = sign_extension(bits, n + 1)
    logger.info("two's complement of \"{s}\" is:\n\t{bits}".format(
        s=s, bits=bits))
    logger.info('-- done encoding int\n')
    return bits


def twos_complement_to_int(bits):
    """Return `int` equal to value of two's complement in `bits`."""
    n = len(bits)  # width including sign bit
    n = n - 1  # width w/o sign bit
    r = [int(b) for b in bits]
    return -r[-1] * 2**n + sum(b * 2**i for i, b in enumerate(r[:-1]))


def equalize_width(x, y):
    """Return bitvectors of equal len by applying sign extension."""
    logger.info('++ equalize width...')
    logger.debug('before equalization:\n\t x = {x}\n\t y = {y}'.format(
        x=x, y=y))
    n = max(len(x), len(y))
    p = sign_extension(x, n)
    q = sign_extension(y, n)
    logger.debug('after extension:\n\t x = {p}\n\t y = {q}'.format(
        p=p, q=q))
    assert len(p) == len(q)
    assert len(p) == n
    logger.info('-- done equalizing.\n')
    return p, q


def sign_extension(x, n):
    """Extend two's complement of `x` to `n` bits width.

    Note that the width of two's complement should be at
    least 2 bits, otherwise it doesn't make sense.

    Reference
    =========
    https://en.wikipedia.org/wiki/Sign_extension

    @type x: `list` of `str`
    @type n: `int` with: `len(x) <= n < 32`
    """
    logger.debug('++ sign extension to {n} bits of: {x}'.format(x=x, n=n))
    assert isinstance(x, list)
    assert n < 32
    m = len(x)
    if m < 2:
        raise ValueError('"{x}" has less than 2 bits.'.format(x=x))
    if n < m:
        raise ValueError(
            'Extension width is {n} < {m} = len(x)'.format(n=n, m=m))
    y = x + (n - m) * [x[-1]]
    assert y[:len(x)] == x
    assert len(y) == n
    logger.debug('-- result of extension: {y}\n'.format(y=y))
    return y


def _format_mem(mem):
    """Return pretty string for printing memory contents."""
    return 'memory:\n{mem}\n'.format(
        mem='\n'.join('{i}: {v}'.format(i=i, v=v)
                      for i, v in enumerate(mem)))
