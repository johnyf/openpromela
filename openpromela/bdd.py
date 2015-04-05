#!/usr/bin/env python
"""Slugsin parser with BDD backend.

This module translates Boolean formulas in prefix format
to binary decision diagrams.

Reference
=========

Slugsin syntax:
    https://github.com/LTLMoP/slugs/blob/master/doc/input_formats.md
"""
from __future__ import absolute_import
import logging
import ply.lex
from logic import ast


logger = logging.getLogger(__name__)
slugs_log = logging.getLogger(__name__ + '.slugs')


class SlugsLexer(object):
    """Token rules for slugsin lexer."""

    operators = ['NOT', 'AND', 'OR', 'XOR', 'DOLLAR', 'QUESTION']
    identifiers = ['NAME', 'NUMBER']

    t_NUMBER = r'\d+'
    t_NAME = r"[A-Za-z_][A-Za-z0-9_']*"
    t_NOT = r'\!'
    t_AND = r'\&'
    t_OR = r'\|'
    t_XOR = r'\^'
    t_DOLLAR = r'\$'
    t_QUESTION = r'\?'
    t_ignore = ' \t'

    def __init__(self):
        self.tokens = self.operators + self.identifiers
        self.build()

    def build(self):
        log = logging.getLogger(__name__ + '.slugs_logger')
        self.lexer = ply.lex.lex(module=self, debug=True, debuglog=log)

    def t_error(self, t):
        raise Exception('Illegal character "{t}"'.format(t=t.value[0]))


class PrefixParser(object):
    """Parser for prefix syntax with buffers."""
    # Context-sensitive grammar, so cannot use PLY

    def __init__(self, nodes=None):
        self.lexer = SlugsLexer()
        self.tokens = self.lexer.tokens
        self._binary = {'AND', 'OR', 'XOR'}
        if nodes is None:
            nodes = _make_memory_nodes()
        self._ast = nodes

    def parse(self, data):
        self.lexer.lexer.input(data)
        r = self._recurse()
        # empty stack ?
        tok = self.lexer.lexer.token()
        if not tok:
            return r
        # error
        s = tok.value
        while True:
            tok = self.lexer.lexer.token()
            if not tok:
                break
            s += tok.value
        raise Exception(
            'syntax error: remaining characters: {s}'.format(
                s=s))

    def _recurse(self):
        tok = self.lexer.lexer.token()
        if not tok:
            raise Exception('syntax error: stream ended early')
        t = tok.type
        if t == 'NOT':
            x = self._recurse()
            return self._ast.Operator('!', x)
        elif t in self._binary:
            op = tok.value
            x = self._recurse()
            y = self._recurse()
            return self._ast.Operator(op, x, y)
        elif t == 'DOLLAR':
            u = self._recurse()
            assert u.type == 'num', u.type
            n = int(u.value)
            mem = [self._recurse() for i in xrange(n)]
            return self._ast.Buffer(mem)
        elif t == 'QUESTION':
            u = self._recurse()
            assert u.type == 'num', u.type
            return self._ast.Register(u.value)
        elif t == 'NAME':
            return self._ast.Var(tok.value)
        elif t == 'NUMBER':
            return self._ast.Num(tok.value)
        else:
            raise Exception('Unknown token "{t}"'.format(t=tok))


def _make_memory_nodes():
    nodes = ast.make_fol_nodes()

    # difference with slugs parser:
    # cyclic references are possible, but assumed absent
    # any cyclic reference would introduce infinite recursion,
    # so a new variable
    class Buffer(object):
        def __init__(self, memory):
            self.memory = memory
            self.type = 'buffer'

        def __repr__(self):
            return 'Memory({c})'.format(
                c=', '.join(repr(u) for u in self.memory))

        def flatten(self, indent=0, *arg, **kw):
            indent += 1
            sep = ',\n{s}'.format(s=' ' * indent)
            mem = sep.join(
                u.flatten(indent=indent)
                for u in self.memory)
            return '\n{s}buffer[{i}](\n{s1}{mem})'.format(
                i=len(self.memory),
                mem=mem,
                s=' ' * (indent - 1),
                s1=' ' * indent)

    class Register(nodes.Terminal):
        def __init__(self, value):
            super(Register, self).__init__(value)
            self.type = 'register'

        def flatten(self, *arg, **kw):
            return 'reg[{i}]'.format(i=self.value)

    # infix Binary flattening
    class Operator(nodes.Operator):
        def flatten(self, *arg, **kw):
            if len(self.operands) == 2:
                return nodes.Binary.flatten(self)
            else:
                return super(Operator, self).flatten()

    nodes.Buffer = Buffer
    nodes.Register = Register
    nodes.Operator = Operator
    return nodes


def make_bdd_nodes():
    """Factory of AST to flatten prefix syntax to a BDD."""
    nodes = _make_memory_nodes()

    class Buffer(nodes.Buffer):
        def flatten(self, bdd, *arg, **kw):
            mem = list()
            for u in self.memory:
                s = u.flatten(bdd=bdd, mem=mem)
                mem.append(s)
            r = mem[-1]
            # print 'mem: ', mem, ', res: ', r
            return r

    class Operator(nodes.Operator):
        def flatten(self, bdd, *arg, **kw):
            operands = [
                u.flatten(bdd=bdd, *arg, **kw)
                for u in self.operands]
            u = bdd.apply(self.operator, *operands)
            # print 'op: ', self.operator, operands, u
            return u

    class Register(nodes.Register):
        def flatten(self, bdd, mem, *arg, **kw):
            i = int(self.value)
            # no circular refs
            assert 0 <= i < len(mem), (i, mem)
            r = mem[i]
            # print 'reg: ', i, ', of mem: ', mem, ', contains: ', r
            return r

    class Var(nodes.Var):
        def flatten(self, bdd, *arg, **kw):
            u = bdd.add_ast(self)
            # print 'add var: ', self.value, u
            return u

    class Num(nodes.Num):
        def flatten(self, bdd, *arg, **kw):
            # the only registers in the tree are Boolean constants
            assert self.value in ('0', '1'), self.value
            u = int(self.value)
            if u == 0:
                u = -1
            return u

    nodes.Buffer = Buffer
    nodes.Register = Register
    nodes.Operator = Operator
    nodes.Var = Var
    nodes.Num = Num
    return nodes
