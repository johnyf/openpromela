#!/usr/bin/env python
"""Translate Promela to linear temporal logic (LTL)"""
from __future__ import absolute_import
import argparse
import copy
import json
import logging
import pprint
import textwrap
import warnings
from dd import bdd as _bdd
import networkx as nx
from networkx.utils import misc
from promela import ast
from promela import lex
from promela import yacc
from omega.logic import bitvector
from omega.logic import past
from openpromela import slugs
from openpromela import _version
from omega.symbolic import symbolic as _symbolic
from omega import gr1
from omega.logic.syntax import conj, disj


logger = logging.getLogger(__name__)
TABMODULE = 'openpromela.open_promela_parsetab'
LTL_SPEC = 'spec_ltl.txt'
SPEC_REPR = 'spec_repr.txt'


class Lexer(lex.Lexer):
    """Lex for open Promela."""

    reserved = dict(lex.Lexer.reserved)
    reserved.update({
        'assume': 'ASSUME',
        'env': 'ENV',
        'sys': 'SYS',
        'free': 'FREE',
        'sync': 'SYNC',
        'async': 'ASYNC',
        'S': 'SINCE'})
    operators = list(lex.Lexer.operators)
    operators.extend([
        'PRIME', 'PREVIOUS', 'WEAK_PREVIOUS', 'HISTORICALLY', 'ONCE'])
    # more token rules
    t_PRIME = r"\'"
    t_PREVIOUS = r'--X'
    t_WEAK_PREVIOUS = r'-X'
    t_HISTORICALLY = r'-\[\]'
    t_ONCE = r'-\<\>'
    t_SINCE = r'S'


class Parser(yacc.Parser):
    """Yacc for open Promela."""

    tabmodule = TABMODULE  # avoid conflict of table file
    # low to high
    precedence = (
        ('right', 'EQUALS'),
        ('left', 'TX2', 'RCV', 'R_RCV'),
        ('left', 'IMPLIES', 'EQUIV'),
        ('left', 'LOR'),
        ('left', 'LAND'),
        ('left', 'ALWAYS', 'EVENTUALLY', 'HISTORICALLY', 'ONCE'),
        ('left', 'UNTIL', 'WEAK_UNTIL', 'RELEASE', 'SINCE'),
        ('left', 'OR'),
        ('left', 'XOR'),
        ('left', 'AND'),
        ('left', 'EQ', 'NE'),
        ('left', 'LT', 'LE', 'GT', 'GE'),
        ('left', 'LSHIFT', 'RSHIFT'),
        ('left', 'PLUS', 'MINUS'),
        ('left', 'TIMES', 'DIVIDE', 'MOD'),
        ('left', 'INCR', 'DECR'),
        ('right', 'LNOT', 'NOT', 'UMINUS', 'NEG'),  # LNOT is also SND
        ('right', 'NEXT', 'PREVIOUS', 'WEAK_PREVIOUS'),
        ('left', 'PRIME'),  # this is the only addition
        ('left', 'DOT'),
        ('left', 'LPAREN', 'RPAREN', 'LBRACKET', 'RBRACKET'))

    def __init__(self):
        super(Parser, self).__init__(ast=AST(), lexer=Lexer())

    def p_ltl_assume(self, p):
        """ltl : ASSUME LTL LBRACE expr RBRACE
               | ASSERT LTL LBRACE expr RBRACE
        """
        p[0] = self.ast.LTL(p[4], assume=p[1])

    def p_unit_product(self, p):
        """unit : async
                | sync
        """
        p[0] = p[1]

    def p_async(self, p):
        """async : ASYNC LBRACE async_body RBRACE"""
        p[0] = self.ast.Product(p[3])

    def p_async_onwer(self, p):
        """async : owner ASYNC LBRACE async_body RBRACE"""
        p[0] = self.ast.Product(p[4], owner=p[1])

    def p_async_body_iter(self, p):
        """async_body : async_body async_unit"""
        p[0] = self._iter(p)

    def p_async_body_end(self, p):
        """async_body : async_unit"""
        p[0] = self._end(p)

    def p_async_unit(self, p):
        """async_unit : sync
                      | proc
                      | one_decl
        """
        p[0] = p[1]

    def p_async_unit_semi(self, p):
        """async_unit : semi"""

    def p_sync_block(self, p):
        """sync : SYNC LBRACE sync_body RBRACE"""
        p[0] = self.ast.Product(p[3], sync=True)

    def p_sync_block_owner(self, p):
        """sync : owner SYNC LBRACE sync_body RBRACE"""
        p[0] = self.ast.Product(p[3], sync=True, owner=p[1])

    def p_sync_body_iter(self, p):
        """sync_body : sync_body sync_unit"""
        p[0] = self._iter(p)

    def p_sync_body_end(self, p):
        """sync_body : sync_unit"""
        p[0] = self._end(p)

    def p_sync_unit(self, p):
        """sync_unit : async
                     | proc
                     | one_decl
        """
        p[0] = p[1]

    def p_sync_unit_semi(self, p):
        """sync_unit : semi"""

    def p_owned_proctype(self, p):
        """proctype : owner PROCTYPE"""
        p[0] = {'owner': p[1]}

    def p_conditioned_owned_proctype(self, p):
        """prefix_proctype : ASSUME prefix_proctype
                           | ASSERT prefix_proctype
        """
        d = p[2]
        d['assume'] = p[1]
        p[0] = d

    def p_typename_ranged_int(self, p):
        """typename : INT LPAREN number COMMA number RPAREN"""
        p[0] = {'type': 'int', 'min': p[3], 'max': p[5]}

    def p_one_decl_owner(self, p):
        """one_decl : var_semantics typename var_list
                    | var_semantics NAME var_list
        """
        d = p[1]
        typ = p[2]
        var_list = p[3]
        p[0] = self.one_decl(typ, var_list, **d)

    def one_decl(self, typ, var_list,
                 visible=None, owner=None, free=False):
        s = list()
        for d in var_list:
            v = self.ast.VarDef(vartype=typ, visible=visible,
                                owner=owner, free=free, **d)
            s.append(v)
        return self.ast.Sequence(s)

    def p_free_owned_var(self, p):
        """var_semantics : FREE owner"""
        p[0] = {'free': True, 'owner': p[2]}

    def p_owned_var(self, p):
        """var_semantics : owner"""
        p[0] = {'owner': p[1]}

    def p_free_var(self, p):
        """var_semantics : FREE"""
        p[0] = {'free': True}

    def p_owner(self, p):
        """owner : ENV
                 | SYS
        """
        p[0] = p[1]

    def p_expr_primed(self, p):
        """expr : expr PRIME"""
        p[0] = self.ast.Next('X', p[1])

    def p_expr_postfix_previous(self, p):
        """expr : expr PERIOD %prec PREVIOUS"""
        p[0] = self.ast.Unary('-X', p[1])

    def p_var_postfix_previous(self, p):
        """cmpnd : cmpnd PERIOD %prec PREVIOUS"""
        p[0] = self.ast.Unary('-X', p[1])

    def p_expr_past_ltl_unary(self, p):
        """expr : PREVIOUS expr
                | WEAK_PREVIOUS expr
                | HISTORICALLY expr
                | ONCE expr
        """
        p[0] = self.ast.Unary(p[1], p[2])

    def p_expr_past_ltl_binary(self, p):
        """expr : expr SINCE expr"""
        p[0] = self.ast.Binary(p[1], p[3])


class AST(object):
    """Open Promela abstract syntax tree."""

    # Program = ast.Program
    # Proctype = ast.Proctype
    # omit: NeverClaim
    Init = ast.Init
    Sequence = ast.Sequence
    # VarDef = ast.VarDef
    MessageChannel = ast.MessageChannel
    TypeDef = ast.TypeDef
    MessageType = ast.MessageChannel
    # VarRef = ast.VarRef
    Options = ast.Options
    # Else = ast.Else
    Break = ast.Break
    Return = ast.Return
    # omit: Run
    Label = ast.Label
    Goto = ast.Goto
    Inline = ast.Inline
    # omit: Call
    Assert = ast.Assert
    # Expression = ast.Expression
    # Assignment = ast.Assignment
    Receive = ast.Receive
    Send = ast.Send
    Operator = ast.Operator
    # Binary = ast.Binary
    # Unary = ast.Unary
    Printf = ast.Printf

    class Program(ast.Program):
        def to_table(self):
            units = misc.flatten(self)
            groups = {x for x in units
                      if isinstance(x, (AST.Proctype, AST.Product))}
            ltl = {x for x in units if isinstance(x, AST.LTL)}
            global_defs = set(units).difference(groups).difference(ltl)
            return global_defs, groups, ltl

    class LTL(ast.LTL):
        def __init__(self, formula, assume='assert'):
            super(AST.LTL, self).__init__(formula)
            self.assume = assume

    class Product(object):
        def __init__(self, iterable, sync=False, owner=None):
            self.body = iterable
            self.sync = sync
            self.owner = owner

        def __repr__(self):
            return 'Product({body}, sync={sync}, owner={owner})'.format(
                body=repr(self.body),
                sync=self.sync,
                owner=self.owner)

        def __str__(self):
            sync = 'sync' if self.sync else 'async'
            owner = '' if self.owner is None else self.owner + ' '
            return '{owner}{sync} {{\n{body}\n}}'.format(
                owner=owner, sync=sync,
                body='\n'.join(ast.to_str(x) for x in self.body))

        # TODO: flattener that simplifies consecutive
        # products of the same type, e.g.,
        # `async{ async{ ... }} = async{ ... }`

    class Proctype(ast.Proctype):
        def __init__(self, name, body, owner=None, assume=None,
                     active=None, **kw):
            if owner is None and assume is not None:
                owner = 'env' if assume == 'assume' else 'sys'
            if owner is None:
                owner = 'sys'
            assert owner in {'env', 'sys'}
            self.owner = owner
            if assume is None:
                assume = 'assume' if owner == 'env' else 'assert'
            assert assume in {'assume', 'assert'}
            assume = 'env' if assume == 'assume' else 'sys'
            self.assume = assume
            # different default than Promela
            if active is None:
                active = AST.Integer('1')
            super(AST.Proctype, self).__init__(
                name=name, body=body, active=active, **kw)

        def to_str(self):
            return (
                '{active} {owner} proctype {name}({args}){{\n'
                '{body}\n'
                '}}\n\n').format(
                    active=self._active_str(),
                    owner=self.owner,
                    name=self.name,
                    args=self._args_str(),
                    body=ast._indent(ast.to_str(self.body)))

    class VarDef(ast.VarDef):
        def __init__(
            self, name, vartype, length=None,
            visible=None, bitwidth=None, msg_types=None,
            initval=None, owner=None, free=False
        ):
            self.owner = owner
            self.free = free
            self.min = None
            self.max = None
            if isinstance(vartype, dict):
                assert vartype['type'] == 'int'
                typ = vartype['type']
                self.min = int(vartype['min'].value)
                self.max = int(vartype['max'].value)
                if self.min > self.max:
                    raise ValueError(
                        'integer must have min <= max\n'
                        'Got instead: min = {min}, max = {max}'.format(
                            min=self.min, max=self.max))
            else:
                assert isinstance(vartype, basestring)
                typ = vartype
            # imperative modwrap int initially at minimum of domain
            if initval is None and self.min is not None and not free:
                initval = ast.Integer(str(self.min))
            super(AST.VarDef, self).__init__(
                name, typ,
                length=length, visible=visible,
                bitwidth=bitwidth, msg_types=msg_types,
                initval=initval)
            # unassigned free var decl ?
            if free and initval is None:
                self.initial_value = None

        def _type_str(self):
            # always showing the owner requires passing
            # a symbol table around
            free = 'free ' if self.free else ''
            if self.owner:
                owner = '{owner} '.format(owner=self.owner)
            else:
                owner = ''
            if self.min is not None:
                bounds = '({min}, {max})'.format(
                    min=self.min, max=self.max)
            else:
                bounds = ''
            return '{free}{owner}{type}{bounds}'.format(
                free=free, owner=owner,
                type=self.type, bounds=bounds)

        def insert_logic_var(self, t, assume_context, pid):
            """Insert variable in table of variables for synthesis.

            @type vart: L{VariablesTable}

            @type pid: int
            """
            name = self.name
            # type
            r = self.type
            if r in {'bool'}:
                dom = 'bool'
                dtype = 'bool'
            elif r in {'bit'}:
                dom = (0, 1)
                dtype = 'modwrap'
            elif r in {'byte'}:
                dom = (0, 255)
                dtype = 'modwrap'
            elif r in {'int'}:
                if self.min is not None:
                    dom = (self.min, self.max)
                else:
                    warnings.warn(
                        'non-ranged integer bounded to (0, 255)')
                    dom = (0, 255)
                dtype = 'saturating'
            else:
                raise NotImplementedError('data type: {r}'.format(r=r))
            # context determines default owner
            owner = assume_context if self.owner is None else self.owner
            assert owner == 'env' or owner == 'sys', \
                'unknown owner "{owner}" for "{var}"'.format(
                    owner=owner, var=name)
            # add var
            flatname = 'pid{pid}_{name}'.format(pid=pid, name=name)
            t.add_var(pid, name, flatname, dom, dtype,
                      self.free, owner, length=self.length,
                      init=self.initial_value)

    class VarRef(ast.VarRef):
        def _context(self, d):
            if d['dom'] == 'bool':
                return 'bool'
            else:
                return 'numerical'

        def to_logic(self, t, pid, *arg, **kw):
            d = find_var_in_scope(self.name, t, pid)
            context = self._context(d)
            # get index expr
            expr = self.index
            # not an array ?
            if expr is None:
                return d['flatname'], context
            # array
            flatnames = array_to_flatnames(d['flatname'], d['length'])
            if is_constant_expr(expr):
                # => fix the element of the array
                i = eval(str(expr))
                s = flatnames[i]
            else:
                e, index_context = expr.to_logic(t, pid)
                assert index_context == 'numerical', (
                    'index "{e}" must be '
                    'arithmetic expression').format(e=e)
                # TODO: implement more efficiently with log selector
                s = flatnames[0]
                for i in xrange(1, d['length']):
                    element = flatnames[i]
                    s = 'ite( {expr} = {i}, {element}, {s})'.format(
                        expr=e,
                        i=i,
                        element=element,
                        s=s)
                # TODO: generate array index bound safety constraint
            return s, context

        def to_guard(self, t, pid, assume, primed, negated):
            d = find_var_in_scope(self.name, t, pid)
            s, context = self.to_logic(t, pid)
            controlled_primed = primed and d['owner'] == assume
            # primed sys variable in env context ?
            if d['owner'] == 'sys' and assume == 'env' and primed:
                raise AssertionError(
                    'Primed system variable "{v}" '
                    'found in assumption. Invalid when '
                    'assuming Moore environment.'.format(
                        v=self.name))
            # get index expr
            expr = self.index
            # is an array ?
            if expr is not None:
                _, controlled_primed_index = expr.to_guard(
                    t, pid, assume, primed=False, negated=False)
                # controlled primed var inside index ?
                if controlled_primed_index and not controlled_primed:
                    raise AssertionError((
                        'Primed variable controlled by {assume} found '
                        'inside array index in a {assume} proctype. '
                        'Such action has undefined guard.').format(
                            assume=assume))
            # (different owner than context) or unprimed ?
            if not controlled_primed:
                # return (name, primed controlled)
                return (s, False)
            # controlled primed
            # just reflect ?
            if context == 'numerical':
                return (s, True)
            # primed in propositional context
            if negated:
                return ('False', True)
            else:
                return ('True', True)

    class Expression(ast.Expression):
        def to_logic(self, *arg, **kw):
            return self.expr.to_logic(*arg, **kw)

        def to_guard(self, t, pid, assume):
            e, pr = self.expr.to_guard(
                t, pid, assume, primed=False, negated=False)
            return e

    class Assignment(ast.Assignment):
        def to_logic(self, t, pid, *arg, **kw):
            flatname, var_context = self.var.to_logic(t, pid)
            value, val_context = self.value.to_logic(t, pid)
            if var_context == 'bool' or val_context == 'bool':
                context = 'bool'
                op = '<->'
            else:
                context = 'numerical'
                op = '='
                d = find_var_in_scope(self.var.name, t, pid)
                dom = d['dom']
                dtype = d['type']
                _, width = bitvector.dom_to_width(dom)
                if dtype == 'saturating':
                    value = value
                elif dtype == 'modwrap':
                    value = '({value} <<>> {width})'.format(
                        value=value, width=width)
                else:
                    raise Exception(
                        'Unknown semantics: {dtype}'.format(dtype=dtype))
            f = '(X {var}) {op} {val}'.format(
                var=flatname, op=op, val=value)
            return f, context

        def to_guard(self, *arg, **kw):
            return 'True'

    class Else(ast.Else):
        def to_logic(self, t, pid, assume, *arg, **kw):
            c = [stmt.to_guard(t, pid, assume)
                 for stmt in self.other_guards]
            s = conj('! ({s})'.format(s=s) for s in c)
            return s, 'bool'

        def to_guard(self, *arg, **kw):
            s, context = self.to_logic(*arg, **kw)
            return s

    class Binary(ast.Binary):
        def to_logic(self, *arg, **kw):
            x, xc = self.operands[0].to_logic(*arg, **kw)
            y, yc = self.operands[1].to_logic(*arg, **kw)
            # check context orrectness
            functions = {'+', '-', '/', '%', '^', '|', '&'}
            predicates = {'<', '<=', '==', '>=', '>', '!='}
            connectives = {'->', '<->', '&&', '||',
                           '[]', '<>', 'U', 'W', 'V'}
            # context: type check
            op = self.operator
            if op in functions:
                assert xc == 'numerical', self
                assert yc == 'numerical', self
                c = 'numerical'
            elif op in predicates:
                assert xc == 'numerical', self
                assert yc == 'numerical', self
                c = 'bool'
                if op == '==':
                    op = '='  # convert to logic
            elif op in connectives:
                assert xc == 'bool', self
                assert yc == 'bool', self
                c = 'bool'
            else:
                raise Exception('Unknown operator "{op}"'.format(
                    op=op))
            # c = 'bool'
            # replace
            # if op == '==':
            #     op = '<->'
            s = '({x} {op} {y})'.format(x=x, op=op, y=y)
            return (s, c)

        def to_guard(self, t, pid, assume, primed, negated):
            op = self.operator
            if op in {'->', '<->'}:
                xneg = not negated
                yneg = negated
            else:
                xneg = negated
                yneg = negated
            x, prx = self.operands[0].to_guard(t, pid, assume, primed, xneg)
            y, pry = self.operands[1].to_guard(t, pid, assume, primed, yneg)
            pr = prx or pry
            # does not contain primed variables of given player ?
            if not pr:
                s, _ = self.to_logic(t, pid)
                return (s, False)
            # primed
            # predicate ?
            if op in {'<', '<=', '==', '!=', '>=', '>'}:
                return (str(not negated), True)
            if op == '<->':
                x_, _ = self.operands[0].to_guard(
                    t, pid, assume, primed, negated)
                y_, _ = self.operands[1].to_guard(
                    t, pid, assume, primed, not negated)
                return ('({xp} & {yp}) | (!{xn} & !{yn})'.format(
                    xp=x_, xn=x, yp=y, yn=y_), True)
            # other op, including '->'
            return ('({x} {op} {y})'.format(x=x, op=op, y=y), True)

    class Unary(ast.Unary):
        def to_logic(self, *arg, **kw):
            x, xc = self.operands[0].to_logic(*arg, **kw)
            boolean_operators = (
                '!', '-X', '--X',
                '[]', '-[]', '<>', '-<>')
            if self.operator in ('X', '~'):
                c = xc
            elif self.operator in boolean_operators:
                c = 'bool'
            elif self.operator == '-':
                c = 'numerical'
            else:
                raise Exception(
                    'unknown operator "{op}"'.format(op=self.operator))
            s = '({op} {x})'.format(op=self.operator, x=x)
            return (s, c)

        def to_guard(self, t, pid, assume, primed, negated):
            primed = primed or (self.operator == 'X')
            if self.operator == '!':
                negated = not negated
            x, pr = self.operands[0].to_guard(
                t, pid, assume, primed, negated)
            s = '({op} {x})'.format(
                op=self.operator, x=x)
            return (s, pr)

    class Next(Unary):
        def __str__(self):
            return "{x}'".format(
                x=ast.to_str(self.operands[0]))

        def to_logic(self, *arg, **kw):
            y, yc = self.operands[0].to_logic(*arg, **kw)
            s = '(X {y})'.format(y=y)
            c = yc
            return (s, c)

    class Integer(ast.Integer):
        def to_logic(self, *arg, **kw):
            return (str(self), 'numerical')

        def to_guard(self, *arg, **kw):
            return (str(self), False)

    class Bool(ast.Bool):
        def to_logic(self, *arg, **kw):
            return (str(self), 'bool')

        def to_guard(self, *arg, **kw):
            return (str(self), False)

    class RemoteRef(ast.RemoteRef):
        def to_logic(self, t, *arg, **kw):
            # find pid
            name = self.proctype
            pid = self.pid
            assert name in t.proctypes, (name, t.proctypes)
            dproc = t.proctypes[name]
            g = dproc['program_graph']
            n = g.active
            if n == 0:
                raise Exception(
                    'No active instances of proctype "{p}"'.format(
                        p=name))
            if pid is None:
                if n > 1:
                    raise Exception(
                        'More than one active instances of '
                        'proctype "{p}"'.format(
                            p=name))
                assert n == 1, n
                inst = dproc['instances']
                assert len(inst) == 1, inst
                pid = inst[0]
            assert name == t.pids[pid]['proctype'], (name, t.pids)
            pc = pid_to_pc(pid)
            # find node with given label
            nodes = set()
            for u, d in g.nodes_iter(data=True):
                labels = d.get('labels')
                if labels is None:
                    continue
                if self.label in labels:
                    nodes.add(u)
            if not nodes:
                raise Exception(
                    'No nodes in proctype "{p}" are '
                    'labeled with "{label}".'.format(
                        p=name, label=self.label))
            elif len(nodes) > 1:
                raise Exception(
                    'Multiple nodes in proctype "{p}" '
                    'are labeled with "{label}".'.format(
                        p=name, label=self.label))
            assert len(nodes) == 1, nodes
            (u,) = nodes
            # formula
            s = '({pc} = {u})'.format(pc=pc, u=u)
            return (s, 'bool')

        def to_guard(self, *arg, **kw):
            s, c = self.to_logic(*arg, **kw)
            return (s, False)


_parser = Parser()


class Table(object):
    """Table of variables for synthesis.

    Attributes of symbol table:

      - scopes: one for each pid, a global, and an auxiliary one
      - pids: process ids
      - products: asynchronous products (universally quantified)
      - proctypes

    Attributes of each variable:

      - flatname: `str`
      - dom: range of variable
      - owner: in `{'env', 'sys'}`
      - free: `bool`

    Attributes for each process:

      - proctype: name of proctype
        `str`
      - owner: of program counter
        in `{'env', 'sys'}`
      - ps: process scheduler variable (if in async product)
        `str`
      - gid: group id of an entity inside an asynchronous product.
        An entity is either a `proctype`, or an asynchronous product.
        Asynchronous products can appear as entities inside an
        asynchronous product at the source level, but they will
        be simplified before assigning group ids.
        `int`
      - lid: local id of an entity inside an synchronous product
        `int`
      - assume: assumption or assertion
        in `{'env', 'sys'}`

    Attributes of each product:

      - owner: of process selection variable (ps*)
        in `{'env', 'sys'}`
      - dom: range of `ps*` variable
      - parent_ps: name of product containing this one
        `str` or `None`
      - gid: group id of this product inside `parent_ps`

    Attributes of each proctype:

      - program_graph
      - gid: group id
      - lid: local id inside a sync product
      - instances: `dict` that maps the order of instantiation to pids
      - parent_ps: var of async product that contains this proctype
    """

    def __init__(self):
        # self.channels = dict()
        self.scopes = {'aux': dict(), 'global': dict()}
        self.pids = dict()
        self.products = dict()
        self.proctypes = dict()
        # struct data types not supported yet

    def __str__(self):
        return (
            '\nTable of variables\n'
            '--------------------\n\n'
            '{scopes}\n\n'
            '{pids}\n\n'
            '{products}\n\n'
            '{proctypes}\n\n').format(
                scopes=pprint.pformat(self.scopes),
                pids=pprint.pformat(self.pids),
                products=pprint.pformat(self.products),
                proctypes=pprint.pformat(self.proctypes))

    def variables_iter(self):
        """Return generator over tuples `(pid, var, dict)`."""
        for pid, localvars in self.scopes.iteritems():
            for var, d in localvars.iteritems():
                yield (pid, var, d)

    def add_var(self, pid, name, flatname, dom, dtype,
                free, owner, length=None, init=None):
        """Add variable to scope."""
        self.scopes.setdefault(pid, dict())
        d = dict(
            flatname=flatname,
            dom=dom,
            type=dtype,
            length=length,
            owner=owner,
            free=free,
            init=init)
        assert name not in self.scopes[pid], (name, pid)
        self.scopes[pid][name] = d

    def add_product_id(self, owner, dom, parent_ps, gid):
        """Return a fresh process selection variable."""
        j = len(self.products)
        ps = ps_str(j)
        self.products[ps] = dict(
            owner=owner,
            dom=dom,
            parent_ps=parent_ps,
            gid=gid)
        self.add_var(
            pid='aux', name=ps, flatname=ps,
            dom=dom, dtype='saturating', free=True, owner='env')
        return ps

    def add_pid(self, proctype_name, owner, ps, gid, lid, assume):
        """Return `pid` for a freshly initialized process scope."""
        assert owner in {'env', 'sys'}
        assert assume in {'env', 'sys'}
        pid = len(self.pids)
        self.pids[pid] = {
            'proctype': proctype_name,
            'owner': owner,
            'ps': ps,
            'gid': gid,
            'lid': lid,
            'assume': assume}
        return pid

    def add_program_counter(self, pid, n, owner, init, pc=None):
        """Add program counter variable for given `pid`."""
        if pc is None:
            pc = pid_to_pc(pid)
        dom = (0, n - 1)
        assert pc not in self.scopes['aux']
        assert owner in ('env', 'sys')
        self.add_var(pid='aux', name=pc, flatname=pc,
                     dom=dom, dtype='saturating',
                     free=True, owner=owner, init=init)

    def flatten(self):
        """Return table of variables in logic formulae.

        A variable is defined for each array element.
        """
        logger.info('++ flatten table of variables')
        t = dict()
        attr = {'type', 'init', 'owner', 'dom'}
        for _, name, d in self.variables_iter():
            b = {k: d[k] for k in attr}
            # flatten arrays
            flatnames = array_to_flatnames(d['flatname'], d['length'])
            is_array = (d['length'] is not None)
            for x in flatnames:
                dx = dict(b)
                dx['array'] = is_array
                t[x] = dx
        logger.debug('result vars:\n {t}'.format(t=t))
        return t


def array_to_flatnames(flatname, length):
    """Return `list` of flatnames for variables that are elements.

    If `d` is not an array, then return the flatname.

    @type d: `dict`
    """
    if length is None:
        return [flatname]
    # array
    assert length > 0, length
    # one variable per array element
    return ['{flatname}{i}'.format(flatname=flatname, i=i)
            for i in xrange(length)]


def products_to_logic(products, global_defs):
    """Flatten process products to a logic formula."""
    t = Table()
    add_variables_to_table(t, global_defs,
                           pid='global', assume_context='sys')
    n_keys, top_ps = flatten_top_async(products, t)
    # find the players with atomic statements
    atomic = who_has_atomic(t)
    add_processes(atomic, t, global_defs)
    # define "exclusive" variables for requesting atomic execution
    for player in ('env', 'sys'):
        if player not in top_ps:
            continue
        ps = top_ps[player]
        ps_dom = t.scopes['aux'][ps]['dom']
        _, ps_max = ps_dom
        if atomic[player]:
            ex = 'ex_{player}'.format(player=player)
            ex_dom = ps_dom
            t.add_var(pid='aux', name=ex, flatname=ex,
                      dom=ex_dom, dtype='saturating',
                      free=True, owner=player,
                      init=ps_max)
            # define preemption variables for atomic execution
            # that stops also the other player
            pm = pm_str(player)
            t.add_var(pid='aux', name=pm, flatname=pm,
                      dom='bool', dtype='bool',
                      free=True, owner=player,
                      init='false')
    # add key vars to table
    # TODO: optimize key domain sizes
    max_key = 0
    for name, d in t.proctypes.iteritems():
        g = d['program_graph']
        max_key = max(max_key, g.max_key)
    for assume, d in n_keys.iteritems():
        for owner, nk in d.iteritems():
            for i in xrange(nk):
                var = key_str(assume, owner, i)
                dom = (0, max_key)
                t.add_var(pid='aux', name=var, flatname=var,
                          dom=dom, dtype='saturating', free=True,
                          owner=owner)
    #
    # symbol table not modified past this point
    #
    # flatten processes
    pids = processes_to_logic(atomic, t, global_defs)
    # assemble spec
    env_imp = constrain_imperative_vars(pids, t, 'env')
    sys_imp = constrain_imperative_vars(pids, t, 'sys')
    env_decl, sys_decl = constrain_local_declarative_vars(t)
    env_safe = [env_imp, env_decl]
    sys_safe = [sys_imp, sys_decl]
    env_init = list()
    sys_init = list()
    for player in {'env', 'sys'}:
        ei, si, e, s = add_process_scheduler(
            t, pids, player, atomic, top_ps)
        env_init.append(ei)
        sys_init.append(si)
        env_safe.append(e)
        sys_safe.append(s)
    env_init = conj(env_init)
    sys_init = conj(sys_init)
    env_safe = conj(env_safe)
    sys_safe = conj(sys_safe)
    env_prog = [y for x in pids.itervalues()
                for y in x['progress']['env']]
    sys_prog = [y for x in pids.itervalues()
                for y in x['progress']['sys']]
    return (t, env_init, sys_init, env_safe, sys_safe,
            env_prog, sys_prog, atomic, top_ps)


def flatten_top_async(products, t):
    """Collect proctypes and products."""
    top_async = split_products(products)
    # to retrieve elsewhere:
    # top 2 products are indexed 0, 1
    n_keys = dict(env=dict(env=0, sys=0),
                  sys=dict(env=0, sys=0))
    top_ps = dict()
    for owner in ('env', 'sys'):
        c = top_async[owner]
        p = AST.Product(c, sync=False, owner=owner)
        keys, ps = flatten_product(p, parent_ps=None, gid=None, t=t)
        update_n_keys(n_keys, keys)
        if ps is not None:
            top_ps[owner] = ps
    return n_keys, top_ps


def flatten_product(p, parent_ps, gid,
                    t, lid=0, max_active=None):
    """Flatten nested (a)synchronous products."""
    ps = None
    # `n_keys` is used to find number of keys needed
    # in sync product multiple program graphs mv simultaneously
    n_keys = dict(env=dict(env=0, sys=0),
                  sys=dict(env=0, sys=0))
    # gid = local id inside an async product
    if isinstance(p, AST.Proctype):
        g = proctype_to_graph(p, max_active)
        # add proctype to symbol table
        t.proctypes[g.name] = dict(
            program_graph=g,
            instances=dict(),
            parent_ps=parent_ps,
            gid=gid,
            lid=lid)
        assume = p.assume
        owner = p.owner
        n_keys[assume][owner] = 1
    elif isinstance(p, AST.Product):
        # recurse
        if p.sync:
            # lid = local id inside a sync product
            for lid, x in enumerate(p.body):
                keys, _ = flatten_product(
                    x,
                    parent_ps,
                    gid,
                    t,
                    lid=lid,
                    max_active=1)
                for assume in ('env', 'sys'):
                    for owner in ('env', 'sys'):
                        n_keys[assume][owner] += keys[assume][owner]
        else:
            # async
            # owner = p.owner  # an experiment
            owner = 'env'
            dom = (0, len(p.body))
            if p.body:
                ps = t.add_product_id(owner, dom, parent_ps, gid)
            for j, x in enumerate(p.body):
                keys, _ = flatten_product(
                    x,
                    parent_ps=ps,
                    gid=j,
                    t=t)
                update_n_keys(n_keys, keys)
        # check that all processes in group are
        # either assumptions or assertions
        c = [x.assume == 'env' for x in p.body
             if isinstance(x, AST.Proctype)]
        if not all(c) and any(c):
            raise Exception(
                'Not all processes in product '
                'constrain {assume} flow.'.format(
                    assume=assume))
    else:
        raise TypeError('group of type "{t}"'.format(t=type(p)))
    return n_keys, ps


def update_n_keys(n_keys, keys):
    for assume in ('env', 'sys'):
        for owner in ('env', 'sys'):
            n_keys[assume][owner] = max(
                keys[assume][owner],
                n_keys[assume][owner])


def split_products(products):
    """Separate top entities into two asynchronous products."""
    async = dict(env=list(), sys=list())
    for p in products:
        if isinstance(p, AST.Proctype):
            assume = p.assume
        elif isinstance(p, AST.Product):
            proc = next(iter(p.body))
            assume = proc.assume
        async[assume].append(p)
    return async


def proctype_to_graph(p, max_active=None):
    """Return control program graph for proctype `p`."""
    name = p.name
    active = p.active
    logger.info('++ translating proctype "{name}"...'.format(
        name=name))
    logger.info('proctype "{p}" has {n} active instances'.format(
        p=name, n=active))
    # too many active instances ?
    # for example inside sync product at most 1 instance allowed
    if max_active is not None:
        if active > max_active:
            raise ValueError(
                '{n} active instances > max = {maxn}'.format(
                    n=active, maxn=max_active))
    g = p.to_pg()
    # contiguous node indexing ?
    assert all(0 <= u < len(g) for u in g), g.nodes()
    # attr
    g.name = p.name
    g.owner = p.owner
    g.assume = p.assume
    g.active = p.active
    g.max_key = max_edge_multiplicity(g)
    return g


def max_edge_multiplicity(g, n=None):
    """Return the outgoing edge with most copies."""
    if n is not None:
        assert n in g
        nbunch = [n]
    else:
        nbunch = g
    return max(len(uv) for u in nbunch
               for v, uv in g.succ[u].iteritems())


def who_has_atomic(t):
    d = dict(env=0, sys=0)
    for name, dproc in t.proctypes.iteritems():
        g = dproc['program_graph']
        assume = g.assume
        if has_atomic(g):
            d[assume] += 1
    return {k: (v > 0) for k, v in d.iteritems()}


def has_atomic(g):
    """Return `True` if graph `g` contains an atomic block."""
    return any(d['context'] == 'atomic'
               for u, d in g.nodes_iter(data=True))


def add_processes(atomic, t, global_defs):
    """Instantiate processes for each proctype in `proctypes`."""
    # instantiate each proctype
    # a process is an instance of a proctype
    for name, d in t.proctypes.iteritems():
        g = d['program_graph']
        ps = d['parent_ps']
        gid = d['gid']
        lid = d['lid']
        for j in xrange(g.active):
            pid = t.add_pid(g.name, g.owner, ps,
                            gid, lid, assume=g.assume)
            add_variables_to_table(t, g.locals, pid, g.assume)
            d['instances'][j] = pid
            t.add_program_counter(pid, len(g), g.owner, g.root)
            # add "next value" program counter
            if g.assume == 'env' and g.owner == 'sys':
                pc_next = pid_to_pc_next(pid, g.assume, g.owner)
                t.add_program_counter(pid, len(g), g.owner,
                                      init=None, pc=pc_next)
            logger.info('\t instance {j}'.format(j=j))
        logger.info(
            '-- done adding instances for '
            'proctype "{name}".\n'.format(name=name))


def processes_to_logic(atomic, t, global_defs):
    """Flatten process instances in symbol table to logic formulae."""
    # init BDD manager and parser
    flat_table = t.flatten()
    aut = _symbolic.Automaton()
    aut.vars = flat_table
    aut = aut.build()
    # flatten
    pids = dict()
    for name, d in t.proctypes.iteritems():
        g = d['program_graph']
        inst = d['instances']
        for j in xrange(g.active):
            pid = inst[j]
            process_to_logic(pid, t, atomic, pids, global_defs, aut)
            logger.info('\t instance {j}'.format(j=j))
        logger.info(
            '-- done translating to logic '
            'processes of type "{name}".\n'.format(name=name))
    return pids


def process_to_logic(pid, t, atomic, pids, global_defs, aut):
    """Flatten a process instance to logic formulae."""
    proctype_name = t.pids[pid]['proctype']
    dproc = t.proctypes[proctype_name]
    g = dproc['program_graph']
    ps = dproc['parent_ps']
    _, max_gid = t.products[ps]['dom']
    pc = pid_to_pc(pid)
    # create graph annotated with formulae
    h = nx.MultiDiGraph()
    var2edges = add_edge_formulae(h, g, t, pid)
    trans = graph_to_logic(h, t, pid, max_gid, atomic)
    notexe = form_notexe_condition(g, t, pid, global_defs, aut)
    progress = collect_progress_labels(g, t, pid)
    # control flow constraints
    if g.assume != g.owner:
        pcmust = graph_to_control_flow(g, t, pid, aut)
        pc_next_init = initialize_pc_next(g, t, pid, aut)
    else:
        pcmust = None
        pc_next_init = None
    # guards used to test for granting requests for atomic execution
    if g.assume == 'sys':
        unblocked_atomic = guards_for_loss_of_atomicity(g, t, pid, aut)
    else:
        unblocked_atomic = None
    # add to dict of pids
    d = dict(
        trans=trans,  # data flow
        progress=progress,  # progress labels
        var2edges=var2edges,  # imperative var deconstraining
        notexe=notexe,  # blocked
        pcmust=pcmust,  # control flow
        pc_next_init=pc_next_init,
        unblocked_atomic=unblocked_atomic)
    pids[pid] = d
    logger.debug('transitions of process "{pc}":\n {t}'.format(
                 pc=pc, t=trans))


def add_variables_to_table(t, r, pid, assume_context):
    """Return logic formula equivalent to program graph.

    @type t: `VariablesTable`
    @type r: iterable of `VarDef`
    @param assume_context: default owner
    """
    for x in r:
        assert isinstance(x, ast.VarDef), x
        x.insert_logic_var(t, assume_context, pid)


def add_edge_formulae(h, g, t, pid):
    """Annotate edges of graph with formulae as strings."""
    logger.info('++ annotating graph with formulae...')
    v2e = dict()  # var2edges: collect deconstrained imperative vars
    for u, v, key, d in g.edges_iter(keys=True, data=True):
        logger.debug('edge: ({u}, {v}, {k})'.format(u=u, v=v, k=key))
        c = d.get('stmt')
        if c is None:
            continue
        f = None
        if isinstance(c, ast.Assignment):
            f, _ = c.to_logic(t, pid)
            var = c.var.name
            # handle arrays
            indices = set()
            if c.var.index is not None:
                # get index expr
                index = c.var.index
                indices.add(index)
            v2e.setdefault(var, list()).append((u, v, key, indices))
        elif isinstance(c, ast.Expression):
            f, _ = c.to_logic(t, pid)
            # controlled primed imperative vars
            s = collect_primed_vars(
                c.expr, t, pid, g.owner)
            idx = collect_indices(s, t)
            for varpid, var in s:
                name = var.name
                # array ?
                if name in idx:
                    indices = idx[name]
                else:
                    indices = list()
                v2e.setdefault(name, list()).append((u, v, key, indices))
            # TODO: collect freed (x = ?)
        elif isinstance(c, ast.Else):
            f, _ = c.to_logic(t, pid, assume=g.assume)
        else:
            raise NotImplementedError(c)
        h.add_edge(u, v, formula=f)
    # copy context for each node
    for u, d in g.nodes_iter(data=True):
        h.add_node(u, context=d['context'])
    if logger.getEffectiveLevel() == 1:
        ast.dump_graph(
            g, fname='pid_{pid}_pg.pdf'.format(pid=pid),
            edge_label='stmt', node_label='context')
        ast.dump_graph(
            h, fname='pid_{pid}.pdf'.format(pid=pid), edge_label='formula')
    logger.info('-- done annotating with formulae.\n')
    return v2e


def collect_progress_labels(g, t, pid):
    """Return liveness formulae for nodes labeled with "progress"."""
    nodes = set()
    for u, d in g.nodes_iter(data=True):
        labels = d.get('labels')
        if labels is None:
            continue
        # is labeled
        has_progress = False
        for label in labels:
            if 'progress' in label:
                has_progress = True
                break
        if not has_progress:
            continue
        # is progress node
        nodes.add(u)
    # format liveness conditions
    ps = pid_to_ps(t, pid)
    pc = pid_to_pc(pid)
    gid = t.pids[pid]['gid']
    progress = {'env': set(), 'sys': set()}
    progress[g.owner] = {
        '(({ps} = {gid}) & ({pc} = {u}))'.format(
            ps=ps, gid=gid, pc=pc, u=u) for u in nodes}
    return progress


def graph_to_logic(g, t, pid, max_gid, atomic):
    """Return temporal logic formula encoding edges.

    The graph vertices must be integers.

    @param k: index of key (for processes in sync products)
    """
    aux = pid_to_key(t, pid)
    dpid = t.pids[pid]
    assume = dpid['assume']
    pc_owner = dpid['owner']
    gid = dpid['gid']
    has_exclusive_vars = atomic[assume]
    pc = pid_to_pc(pid)
    pc_next = pid_to_pc_next(pid, assume, pc_owner)
    c = list()
    for u, du in g.nodes_iter(data=True):
        assert isinstance(u, int), u
        oute = list()
        for u_, v, key, d in g.out_edges_iter(u, data=True, keys=True):
            assert isinstance(v, int)
            edge = '(({pc_next} = {j}) & ({aux} = {k}))'.format(
                pc_next=pc_next, j=v, aux=aux, k=key)
            # prime ?
            if not (assume == 'env' and pc_owner == 'sys'):
                edge = '(X {edge})'.format(edge=edge)
            a = [edge]
            if 'formula' in d:
                a.append(d['formula'])
            if has_exclusive_vars:
                v_context = g.node[v]['context']
                exclusive = form_exclusive_expr(
                    v_context, assume, gid, max_gid)
                a.append(exclusive)
            b = conj(a)
            oute.append(b)
        if not oute:
            oute.append('X(False)')
        precond = '({pc} = {i})'.format(pc=pc, i=u)
        postcond = disj(oute, sep='\n\t')
        t = '{a} -> ({b})'.format(a=precond, b=postcond)
        c.append(t)
    return conj(c, sep='\n')


def form_exclusive_expr(context, assume, gid, max_gid):
    """Return assignment to exclusive execution variables."""
    ex = 'ex_' + assume
    pm = pm_str(assume)
    if context is None:
        exclusive = (
            '((X {ex} = {max_gid}) & (X ! {pm}))').format(
                ex=ex,
                max_gid=max_gid,
                pm=pm)
    elif context == 'atomic':
        exclusive = (
            '((X {ex} = {gid}) & (X {pm}))').format(
                ex=ex,
                gid=gid,
                pm=pm)
    else:
        raise Exception('Found context: {c}'.format(c=context))
    return exclusive


def form_notexe_condition(g, t, pid, global_defs, aut):
    """Return map from nodes to blocking conditions.

    @return: Map from nodes to Boolean formulae.
        Each node blocks if the formula is `True`.
    @rtype: `dict` of `str`
    """
    pc = pid_to_pc(pid)
    c = dict()
    for u, du in g.nodes_iter(data=True):
        r = list()
        # at least one outedge always executable ?
        for _, v, key, d in g.edges_iter(u, data=True, keys=True):
            stmt = d.get('stmt')
            assert isinstance(
                stmt, (AST.Assignment, AST.Expression, AST.Else))
            e, _ = stmt.to_logic(t, pid, assume=g.assume)
            guard = _expr_to_guard(e, aut, g.assume)
            r.append(guard)
            if guard == 'True':
                break
        # u blocks if no executability condition is True
        c[u] = disj(r)
    s = disj(
        '({pc} = {u}) & !({b})'.format(pc=pc, u=u, b=b)
        for u, b in c.iteritems())
    return s


def guards_for_loss_of_atomicity(g, t, pid, aut):
    """Return conditions for to test before granting exclusive execution."""
    assert g.assume == 'sys', g.assume
    pc = pid_to_pc(pid)
    bdd = aut.bdd
    c = list()
    for u, du in g.nodes_iter(data=True):
        u_in_atomic = (du['context'] == 'atomic')
        r = list()
        for _, v, key, d in g.edges_iter(u, keys=True, data=True):
            stmt = d['stmt']
            e, _ = stmt.to_logic(t, pid, assume=g.assume)
            guard = _expr_to_guard(e, aut, player=g.assume, as_bdd=True)
            # if executed, will it be an atomic transition ?
            # note: ex_s = m(r) is added in `add_process_scheduler`
            if u_in_atomic:
                # freeze env by unpriming its primed vars
                # (= they would not change if atomicity not lost)
                # sys primed vars have been quantified already
                # (use `rename` when extended to support
                # target vars that are neighbors but essential)
                support = bdd.support(guard, as_levels=False)
                assert set(support).issubset(aut.bdd.vars), (
                    support, aut.vars)
                to_rename = {var for var in support
                             if var in aut.upvars}
                # TODO: ensure neighbors, then use `bdd.rename`
                for pvar in to_rename:
                    var = aut.unprime[pvar]
                    var_node = bdd.var(var)
                    guard = bdd.compose(guard, pvar, var_node)
                # confirm rename
                new_support = bdd.support(guard, as_levels=False)
                remain = to_rename.intersection(new_support)
                assert not remain, remain
            guard = bdd.to_expr(guard)
            r.append(guard)
            if guard == 'True':
                break
        u_unblocked = disj(r)
        s = '(({pc} = {u}) & ({u_unblocked}))'.format(
            pc=pc, u=u, u_unblocked=u_unblocked)
        c.append(s)
    return disj(c)


def graph_to_control_flow(g, t, pid, aut):
    """Require that the selected edge be executable."""
    assert g.owner != g.assume, (g.owner, g.assume)
    aux = pid_to_key(t, pid)
    pc = pid_to_pc(pid)
    pc_next = pid_to_pc_next(pid, g.assume, g.owner)
    c = list()
    # transition relation for pc owner to select only
    # executable edges
    # prevent pc owner from seleting inexistent edges
    for u in g:
        # find max outgoing edge multiplicity
        n = max_edge_multiplicity(g, u)
        assert (n == 0) == (not g.succ[u])
        # collect blocking conditions
        guards = list()
        r = list()
        for _, v, key, d in g.edges_iter(u, keys=True, data=True):
            stmt = d['stmt']
            e, _ = stmt.to_logic(t, pid, assume=g.assume)
            guard = _expr_to_guard(e, aut, player=g.assume)
            # assume sys ? -> prime the guard
            if g.assume == 'env' and g.owner == 'sys':
                guard = '(X ({guard}))'.format(guard=guard)
            guards.append(guard)
            r.append((
                '(X ({pc_next} = {v})) & '
                '(X ({aux} = {key})) & '
                '({guard})').format(
                    pc_next=pc_next, aux=aux,
                    v=v, key=key, guard=guard))
        trans = disj(r)
        # selected out-edge must be unblocked
        post = '( ((X {aux}) < {n}) & ({trans}) )'.format(
            aux=aux, n=n, trans=trans)
        # if at that pc location
        if g.assume == 'env' and g.owner == 'sys':
            # sys has to eval primed "blocked" expressions
            # because env will decide in next time step
            # whether to select proc to execute, if not blocked
            unblocked = disj(guards)
            s = '( (X ({pc} = {u})) -> ({unblocked} -> {post}) )'.format(
                pc=pc, u=u, unblocked=unblocked, post=post)
        else:
            s = '( ({pc} = {u}) -> {post} )'.format(
                pc=pc, u=u, post=post)
        c.append(s)
    return conj(c)


def initialize_pc_next(g, t, pid, aut):
    """Return initial condition for auxiliary var `pc_next`."""
    root = g.root
    pc_next = pid_to_pc_next(pid, g.assume, g.owner)
    aux = pid_to_key(t, pid)
    r = list()
    guards = list()
    for u, v, key, d in g.edges_iter(root, keys=True, data=True):
        assert u == root, (u, root)
        stmt = d['stmt']
        e, _ = stmt.to_logic(t, pid, assume=g.assume)
        guard = _expr_to_guard(e, aut, player=g.assume)
        guards.append(guard)
        r.append((
            '(({pc_next} = {v}) & '
            '({aux} = {key}) & '
            '({guard}))').format(
                pc_next=pc_next, aux=aux,
                v=v, key=key, guard=guard))
    # sys doesn't lose if "assume sys" root has no out-edges
    unblocked = disj(guards)
    trans = disj(r)
    return '(({unblocked}) -> ({trans}))'.format(
        unblocked=unblocked, trans=trans)


def _expr_to_guard(e, aut, player, as_bdd=False):
    """Return expression after quantifying primed `player` vars.

    @param as_bdd: if `True`, return `bdd` node, else `str`
    """
    assert player in ('env', 'sys'), player
    if player == 'env':
        qvars = aut.upvars
    elif player == 'sys':
        qvars = aut.epvars
    # rename = aut.prime
    rename = dict()
    bdd = aut.bdd
    u = aut.add_expr(e)
    (v,) = aut.action[player]  # integer range limits
    u = _bdd.preimage(u, v, rename, qvars, bdd, forall=False)
    if u == -1:
        print('Warning: guard "{e}" evaluates to "False".'.format(e=e))
    if as_bdd:
        r = u
    else:
        r = bdd.to_expr(u)
    return r


def transform_ltl_blocks(ltl, t):
    """Return `dict` of initial, safety, liveness formulae.

    @param ltl: inline LTL blocks
    @type ltl: `list` of `str`
    @return: mapping from 'init', 'G', 'GF' to
        Boolean formulae as `str`.
    @rtype: `dict`
    """
    logger.info('++ transforming LTL blocks')
    d = {k: dict(init=list(), G=list(), GF=list())
         for k in {'assume', 'assert'}}
    for block in ltl:
        e = block.formula
        assume = block.assume
        assert assume in {'assume', 'assert'}, assume
        if not e:
            continue
        f, _ = e.to_logic(t, pid='global')
        c = gr1.split_gr1(f)
        [d[assume][k].extend(v) for k, v in c.iteritems()]
    # conjoin (except for liveness)
    for assume in {'assume', 'assert'}:
        for part in {'init', 'G'}:
            d[assume][part] = conj(d[assume][part])
    logger.debug('translated LTL blocks:\n{d}'.format(d=d))
    logger.info('-- done transforming LTL blocks.')
    return d


def is_constant_expr(expr):
    """Return `True` if `expr` contains a variable."""
    g = scaffold(expr)
    for u in g:
        if isinstance(u, AST.VarRef):
            return False
    return True


def collect_indices(controlled_primed, t):
    indices = dict()
    for varpid, u in controlled_primed:
        name = u.name
        d = t.scopes[varpid][name]
        # scalar ?
        if d['length'] is None:
            continue
        # array
        indices.setdefault(name, set()).add(u.index)
    return indices


def collect_primed_vars(expr, t, pid, player):
    """Return `set` of primed variables controlled by `player`.

    Variables included are from:
      - `pid` local scope
      - global scope
    Raise exception if variable found not in these scopes.
    """
    g = scaffold(expr)
    Q = [(expr, False)]
    p = set()
    while Q:
        u, c = Q.pop()
        if isinstance(u, AST.VarRef):
            var = u.name
            # check that variable is defined
            varpid = pid
            d = t.scopes.get(varpid, dict()).get(var)
            if d is None:
                varpid = 'global'
                d = t.scopes[varpid].get(var)
            if d is None:
                raise Exception(
                    'Syntax error: ' +
                    'Variable "{var}" not in locals of '.format(var=var) +
                    'pid {pid} nor in globals.'.format(pid=pid))
            # collect if primed and owned by player
            if c and d['owner'] == player:
                p.add((varpid, u))
        # context of next operator
        if hasattr(u, 'operator'):
            c = c or u.operator == 'X'
        Q.extend((v, c) for v in g.successors_iter(u))
    return p


def scaffold(u, g=None):
    """Return `networkx` graph over nodes of tree `u`."""
    if g is None:
        g = nx.MultiDiGraph()
    if hasattr(u, 'operands'):
        for i, v in enumerate(u.operands):
            g.add_edge(u, v, key=i)
            scaffold(v, g)
    elif isinstance(u, (ast.Terminal)):
        g.add_node(u)
    else:
        raise TypeError(
            'unknown AST node type "{t}"'.format(t=type(u)))
    return g


def constrain_imperative_vars(pids, t, player='sys'):
    """Return default constraints for imperative variables."""
    gl = list()
    # locals
    c = list()  # constraints
    for pid, localvars in t.scopes.iteritems():
        # global vars handled differently
        if pid in {'global', 'aux'}:
            continue
        # primed imperative var becomes free only if
        # proctype constrains owner
        if t.pids[pid]['assume'] != player:
            continue
        var2edges = pids[pid]['var2edges']
        for var, d in localvars.iteritems():
            flatname = d['flatname']
            # has declarative semantics ?
            if d['free']:
                continue
            # not controlled by given player ?
            if d['owner'] != player:
                logger.debug(
                    '"{var}" (flatvar "{flatname}")'.format(
                        var=var, flatname=flatname) +
                    ' not controlled by "{player}"'.format(
                        player=player))
                continue
            # has assignment edges or is primed in actions ?
            if var in var2edges:
                edges = var2edges[var]
                free_trans, array_inv = _constrain_imperative_var(
                    t, pid, var, edges)
                inv = _invariant(flatname, d['dom'], d['length'])
                r = (
                    '( ((\t {f}\n) | {invariant}) & '
                    '({array_inv}) )').format(
                        f=free_trans,
                        invariant=inv,
                        array_inv=array_inv)
            else:
                # not assigned anywhere, so always constrained
                r = _invariant(flatname, d['dom'], d['length'])
            c.append(r)
    if c:
        comment = '\n\n# local imperative var constraints\n'
        s = '{comment}{f}'.format(
            f=conj(c, sep='\n'),
            comment=comment)
        gl.append(s)
    # globals
    c = list()
    gvars = t.scopes['global']
    for var, d in gvars.iteritems():
        flatname = d['flatname']
        # not imperative ?
        if d['free']:
            continue
        # not controlled by given player ?
        if d['owner'] != player:
            logger.debug(
                '"{var}" (flatvar "{flatname}")'.format(
                    var=var, flatname=flatname) +
                ' not controlled by "{player}"'.format(
                    player=player))
            continue
        b = list()
        z = list()
        for pid in pids:
            # local var with same name exists ?
            v2e = pids[pid]['var2edges']
            localvars = t.scopes.get(pid)
            if localvars is not None and var in localvars:
                # local shadows global
                continue
            # primed imperative var becomes free only if
            # proctype constrains owner
            if t.pids[pid]['assume'] != player:
                continue
            # has assignment edges ?
            if var in v2e:
                edges = v2e[var]
                free_trans, array_inv = _constrain_imperative_var(
                    t, pid, var, edges)
                b.append(free_trans)
                z.append(array_inv)
        inv = _invariant(flatname, d['dom'], d['length'])
        w = '( ((\t {f}\n) | {invariant}) & ({array_inv}))'.format(
            f=disj(b, sep='\n'),
            invariant=inv,
            array_inv=conj(z, sep='\n'))
        c.append(w)
    if c:
        comment = '\n\n# global imperative var constraints\n'
        s = '{comment}{f}'.format(
            f=conj(c, sep='\n'),
            comment=comment)
        gl.append(s)
    return conj(gl)


def _constrain_imperative_var(t, pid, var, edges):
    logger.debug(
        'the edges for "{var}" are: {e}'.format(var=var, e=edges))
    assert edges
    dpid = t.pids[pid]
    assume = dpid['assume']
    owner = dpid['owner']
    pc = pid_to_pc(pid)
    pc_next = pid_to_pc_next(pid, assume, owner)
    ps = pid_to_ps(t, pid)
    gid = dpid['gid']
    aux = pid_to_key(t, pid)
    d = find_var_in_scope(var, t, pid)
    dom = d['dom']
    c = list()
    for u, v, key, _ in edges:
        s = edge_str(ps, gid, pc, pc_next, u, v, aux, key, assume, owner)
        c.append(s)
    _disj = disj(c, sep='\n\t')
    # scalar ?
    if d['length'] is None:
        return _disj, 'True'
    # array elements remain invariant if not referenced
    flatnames = array_to_flatnames(d['flatname'], d['length'])
    a = list()
    for u, v, key, indices in edges:
        r = list()
        for i, flat in enumerate(flatnames):
            ys = [e.to_logic(t, pid)[0] for e in indices]
            _conj = conj('{y} != {i}'.format(y=y, i=i) for y in ys)
            inv = _invariant(flat, dom)
            cond = '({conj}) -> ({inv})'.format(conj=_conj, inv=inv)
            r.append(cond)
        econj = conj(r)
        edge = edge_str(ps, gid, pc, pc_next,
                        u, v, aux, key, assume, owner)
        cond = '({edge}) -> ({econj})'.format(econj=econj, edge=edge)
        a.append(cond)
    _conj = conj(a, sep='\n\t')
    return _disj, _conj


def find_var_in_scope(name, t, pid):
    # first, look at locals:
    if pid in t.scopes:
        d = t.scopes[pid].get(name)
    else:
        d = None
    if d is None:
        # look at globals:
        d = t.scopes['global'].get(name)
    if d is None:
        if pid == 'global':
            raise Exception(
                ('Variable "{name}" not found in globals:\n'
                 '{t}').format(name=name, t=t))
        else:
            raise Exception(
                ('Variable "{name}" not found in locals '
                 'of pid {pid}, neither in globals:\n{t}').format(
                     name=name, pid=pid, t=t))
    return d


def edge_str(ps, gid, pc, pc_next, u, v, aux, key, assume, owner):
    if assume == 'env' and owner == 'sys':
        return conj([
            'X({ps} = {gid})'.format(ps=ps, gid=gid),
            '({pc} = {u})'.format(pc=pc, u=u),
            '({pc_next} = {v})'.format(pc_next=pc_next, v=v),
            '({aux} = {k})'.format(aux=aux, k=key)])
    else:
        return conj([
            'X({ps} = {gid})'.format(ps=ps, gid=gid),
            '({pc} = {u})'.format(pc=pc, u=u),
            'X({pc_next} = {v})'.format(pc_next=pc_next, v=v),
            'X({aux} = {k})'.format(aux=aux, k=key)])


def constrain_local_declarative_vars(t):
    """Return constraints for free variables when their pid is idle."""
    logger.info('++ constraining free local vars...')
    c = {'env': list(), 'sys': list()}
    for pid, scope in t.scopes.iteritems():
        # not a process ?
        if pid in {'global', 'aux'}:
            continue
        logger.debug('for pid: {pid}'.format(pid=pid))
        ps = pid_to_ps(t, pid)
        gid = t.pids[pid]['gid']
        # if pid idle, then local free vars of both players
        # must remain invariant
        for var, d in scope.iteritems():
            # not declarative ?
            if not d['free']:
                logger.debug('"{var}" not free variable'.format(var=var))
                continue
            # declarative var
            inv = _invariant(d['flatname'], d['dom'], d['length'])
            s = '((X {ps}) != {gid}) -> {invariant}'.format(
                ps=ps, gid=gid, invariant=inv)
            var_owner = d['owner']
            c[var_owner].append(s)
    for k, v in c.iteritems():
        c[k] = '\n\n# declarative var constraints\n{f}'.format(
            f=conj(v, sep='\n'))
    logger.info('-- done with free local vars.\n')
    return c['env'], c['sys']


def freeze_declarative_vars(t, player):
    """Return constraints for all free vars global or in other's pids.

    Effective when other player takes an atomic transition.
    """
    logger.info('++ constraining free global vars...')
    # freeze free vars of `player` in global scope or
    # in opponent's processes
    c = list()
    for pid, scope in t.scopes.iteritems():
        # not global or in opponent process ?
        if pid == 'aux':
            continue
        if pid != 'global' and t.pids[pid]['assume'] == player:
            continue
        for var, d in scope.iteritems():
            if not d['free']:
                logger.debug('"{var}" not free variable'.format(var=var))
                continue
            if d['owner'] != player:
                continue
            # declarative var
            s = _invariant(d['flatname'], d['dom'], d['length'])
            c.append(s)
    r = conj(c)
    logger.info('-- done with free global vars.\n')
    return r


def add_process_scheduler(t, pids, player, atomic, top_ps):
    logger.info('adding process scheduler...')
    assert player in {'env', 'sys'}
    deadlock = dict()
    init = {'env': list(), 'sys': list()}
    safety = {'env': list(), 'sys': list()}
    for pid, f in pids.iteritems():
        # pid constrains given player ?
        dpid = t.pids[pid]
        assume = dpid['assume']
        if assume != player:
            logger.debug('player "{p}" != side "{o}"'.format(
                p=player, o=assume))
            continue
        # constraint on given player
        logger.debug('scheduling pid: {pid}'.format(pid=pid))
        proctype = dpid['proctype']
        ps = pid_to_ps(t, pid)
        gid = dpid['gid']
        pc_owner = dpid['owner']
        pc = pid_to_pc(pid)
        pc_next = pid_to_pc_next(pid, assume, pc_owner)
        pc_dom = t.scopes['aux'][pc]['dom']
        comment = (
            '\n\n# pid: {pid}, gid: {gid}, '
            '{side} proctype: {prt}, pc owner: {owner}\n').format(
                ps=ps, gid=gid, pid=pid,
                prt=proctype,
                side='assumption' if assume == 'env' else 'assertion',
                owner=pc_owner)
        safety['env'].append(comment + 'True\n')
        safety['sys'].append(comment + 'True\n')
        # data flow constraint on side
        safety[assume].append((
            '\n# dataflow constraint:\n'
            '((X {ps} = {gid}) -> ({trans}))').format(
                ps=ps, gid=gid, trans=f['trans']))
        # idle program counter
        if assume == 'env' and pc_owner == 'sys':
            safety[pc_owner].append((
                '\n# program counter variables:\n'
                'ite( (X ({ps} = {gid})), '
                '(X {pc} = {pc_next}), ({invariant}))').format(
                    ps=ps, gid=gid, pc=pc, pc_next=pc_next,
                    invariant=_invariant(pc, pc_dom)))
        else:
            safety[pc_owner].append((
                '\n# idle program counter:\n'
                '((X {ps} != {gid}) -> {invariant})').format(
                    ps=ps, gid=gid, invariant=_invariant(pc, pc_dom)))
        # prevent pc_owner from selecting non-executable edge
        if assume == 'env' and pc_owner == 'sys':
            safety[pc_owner].append(
                '\n# prevent `pc` owner (sys) from selecting blocked edge\n'
                '( {pcmust} )'.format(
                    pcmust=pids[pid]['pcmust']))
            init[pc_owner].append(
                '\n# initial condition for `pc_next`\n' +
                pids[pid]['pc_next_init'])
        elif assume == 'sys' and pc_owner == 'env':
            safety[pc_owner].append(
                '\n# prevent `pc` owner (env) from selecting blocked edge\n'
                '( (X {ps} = {gid}) -> ({pcmust}) )'.format(
                    ps=ps, gid=gid, pcmust=pids[pid]['pcmust']))
        # prevent scheduler from selecting a non-executable process
        blocks_if = pids[pid]['notexe']
        safety['env'].append((
            '\n# prevent scheduler from selecting blocked process\n'
            '({nexe}) -> (X {ps} != {gid})').format(
                nexe=blocks_if, ps=ps, gid=gid))
        deadlock.setdefault(gid, list()).append(blocks_if)
        # if the player has any atomic blocks
        if atomic[player]:
            # for now only system can have atomic blocks
            assert player == 'sys', player
            unblocked_atomic = pids[pid]['unblocked_atomic']
            assert unblocked_atomic is not None
            # grant exclusive execution to requestor if executable
            ex = 'ex_{assume}'.format(assume=assume)
            safety['env'].append((
                '\n# grant request for exclusive execution\n'
                '( (({ex} = {gid}) & ({unblocked_atomic})) -> '
                '(X {ps} = {gid}) )').format(
                    ex=ex, gid=gid,
                    unblocked_atomic=unblocked_atomic, ps=ps))
    # player has no processes ?
    if player not in top_ps:
        return ('', '', '', '')
    ps = top_ps[player]
    ps_dom = t.scopes['aux'][ps]['dom']
    ps_min, ps_max = ps_dom
    assert ps_min == 0, ps_min
    assert ps_max >= 0, ps_max
    # assert contiguous gids
    # TODO: reimplement this assertion
    # last value means deadlock
    if ps_max > 0:
        if player == 'sys':
            safety[player].append((
                '\n\n# never deadlock:\n'
                '(X {ps} != {ps_max})\n').format(ps=ps, ps_max=ps_max))
        elif player == 'env':
            other_player = 'sys'
            if atomic['sys']:
                pm_sys = pm_str(other_player)
                ps_sys = top_ps['sys']
                ex_sys = 'ex_sys'
                _, ps_max_sys = t.scopes['aux'][ps_sys]['dom']
                safety[player].append((
                    '\n\n# never deadlock, unless preempted by sys:\n'
                    '((X {ps} = {ps_max}) <-> '
                    '({pm} & (X {ps_sys} = {ex_sys}) & '
                    '({ex_sys} < {ps_max_sys}) ))\n').format(
                        ps=ps, ps_max=ps_max, pm=pm_sys,
                        ps_sys=ps_sys, ex_sys=ex_sys,
                        ps_max_sys=ps_max_sys))
            else:
                safety[player].append((
                    '\n\n# never deadlock:\n'
                    '(X {ps} != {ps_max})\n').format(
                        ps=ps, ps_max=ps_max))
        else:
            raise Exception(
                'Unknown player "{player}"'.format(player=player))
    # if all processes block, signal deadlock
    # a False means that some process is always executable
    assert deadlock, deadlock
    # handle process products
    c = list()
    for gid, v in deadlock.iteritems():
        s = disj(v)
        c.append(s)
    deadlocked = conj(c, sep='\n')
    if player == 'env':
        safety['env'].append(
            '\n# deadlock\n' +
            "\n ( ({deadlocked}) -> (X {ps} = {ps_max}) )\n".format(
                deadlocked=deadlocked,
                ps=ps, ps_max=ps_max))
    elif player == 'sys':
        safety['env'].append(
            '\n# deadlock\n' +
            "\n ( ({deadlocked}) <-> (X {ps} = {ps_max}) )\n".format(
                deadlocked=deadlocked,
                ps=ps, ps_max=ps_max))
    # process scheduler vars
    for ps, d in t.products.iteritems():
        parent_ps = d['parent_ps']
        # top async ?
        if parent_ps is None:
            continue
        # async other than top
        gid = d['gid']
        _, dom_max = d['dom']
        safety['env'].append(
            '\n# nesting of async and sync products\n'
            '(({parent_ps} != {gid}) <-> ({ps} = {dom_max}))'.format(
                parent_ps=parent_ps,
                gid=gid,
                ps=ps,
                dom_max=dom_max))
    logger.info('done with process scheduler.\n')
    return (
        conj(init['env']),
        conj(init['sys']),
        conj(safety['env'], sep=2*'\n'),
        conj(safety['sys'], sep=2*'\n'))


def pid_to_ps(t, pid):
    """Return process scheduler variable.

    Assertions are selected to execute by `sys_ps`,
    assumptions by `env_ps`.
    Note that env may control the program counter of an assertion.
    """
    assert pid >= 0, pid
    return t.pids[pid]['ps']


def ps_str(product_id):
    """Return identifier of process selection variable.

    @param product_id: for each asynchronous product,
        this is a unique integer identifier.
        These integers are defined after merging
        nested products of the same type, e.g.,
        `async{ async{ ... } } = async{ ... }'
    """
    return 'ps{i}'.format(i=product_id)


def pid_to_pc(pid):
    """Return program counter variable for given `pid`.

    The process owner controls this variable.
    """
    assert pid >= 0, pid
    return 'pc{pid}'.format(pid=pid)


def pid_to_pc_next(pid, assume, pc_owner):
    """Return program counter next value variable.

    Same with `pid_to_pc`, except for `assume sys`.
    In that case, it is a different sys variable "pcN_next".
    """
    assert pid >= 0, pid
    assert assume in ('env', 'sys'), assume
    if assume == 'env' and pc_owner == 'sys':
        return 'pc{pid}_next'.format(pid=pid)
    return pid_to_pc(pid)


def pid_to_key(t, pid):
    """Return auxiliary multi-edge selector variable name.

    The process owner controls this variable.
    """
    assert pid in t.pids
    d = t.pids[pid]
    assume = d['assume']
    owner = d['owner']
    assert assume in {'env', 'sys'}
    assert owner in {'env', 'sys'}
    return key_str(assume, owner, d['lid'])


def key_str(assume, owner, lid):
    """Return identifier for multi-edge selector.

    The `owner` controls this variable.
    It determines the control flow of an assertion or assumption
    depending on `assume`.
    The `lid` is an integer index of processes in
    a synchronous product.
    """
    assert assume in ('env', 'sys'), assume
    assert owner in ('env', 'sys'), owner
    assert lid >= 0, lid
    return '{assume}{owner}key{lid}'.format(
        assume=assume, owner=owner, lid=lid)


def pm_str(player):
    """Return identifier for preemption auxiliary variable.

    When `player` wants to request that the other player
    pause while it executes atomically,
    it sets this variable to `True`.
    """
    assert player in ('env', 'sys')
    return 'pm_{player}'.format(player=player)


def _invariant(flatname, dom, length=None):
    if dom == 'bool':
        op = '<->'
    else:
        op = '='
    # scalar ?
    if length is None:
        return '((X {var}) {op} {var})'.format(var=flatname, op=op)
    # array
    assert length > 0, length
    c = list()
    for ei in array_to_flatnames(flatname, length):
        s = '((X {var}) {op} {var})'.format(var=ei, op=op)
        c.append(s)
    return conj(c)


def compile_spec(code, strict_atomic=True):
    program = _parser.parse(code)
    global_defs, products, ltl = program.to_table()
    (vartable, env_init, sys_init, env_safe,
     sys_safe, env_prog, sys_prog, atomic, top_ps) = \
        products_to_logic(products, global_defs)
    ltl_spc = transform_ltl_blocks(ltl, vartable)
    # conjoin with ltl blocks
    env_ltl_init = ltl_spc['assume']['init']
    env_ltl_safe = ltl_spc['assume']['G']
    env_ltl_prog = ltl_spc['assume']['GF']
    sys_ltl_init = ltl_spc['assert']['init']
    sys_ltl_safe = ltl_spc['assert']['G']
    sys_ltl_prog = ltl_spc['assert']['GF']
    # deactivate LTL safety during atomic transitions ?
    deactivate = (
        atomic['sys'] and
        strict_atomic and
        'ex_sys' in vartable.scopes['aux'])
    if deactivate:
        ps = top_ps['sys']
        _, max_gid = vartable.products[ps]['dom']
        freeze_free = freeze_declarative_vars(vartable, 'env')
        env_ltl_safe = (
            'ite( (pm_sys & ((X {ps}) = ex_sys) &'
            ' (ex_sys < {max_gid})), {freeze}, {safe})').format(
                max_gid=max_gid,
                safe=env_ltl_safe,
                ps=ps,
                freeze=freeze_free)
        sys_ltl_safe = (
            '( ( ((X {ps}) = ex_sys) &'
            ' (ex_sys < {max_gid})) | {safe})').format(
                max_gid=max_gid,
                safe=sys_ltl_safe,
                ps=ps)
    env_init = [env_ltl_init, env_init]
    env_safe = [env_safe, env_ltl_safe]
    env_prog = env_prog + env_ltl_prog
    env_prog = [x for x in env_prog if x != 'True']
    if not env_prog:
        env_prog = list()
    sys_init = [sys_ltl_init, sys_init]
    sys_safe = [sys_safe, sys_ltl_safe]
    sys_prog = sys_prog + sys_ltl_prog
    sys_prog = [x for x in sys_prog if x != 'True']
    if not sys_prog:
        sys_prog = list()
    # bundle
    spc = _symbolic.Automaton()
    flat_table = vartable.flatten()
    spc.vars = flat_table
    spc.init['env'] = env_init
    spc.init['sys'] = sys_init
    spc.action['env'] = env_safe
    spc.action['sys'] = sys_safe
    spc.win['env'] = env_prog
    spc.win['sys'] = sys_prog
    if logger.getEffectiveLevel() < logging.DEBUG:
        dump_ltl_to_json(spc)
    # past -> future LTL
    spc = map_to_future(spc)
    # dump table and spec to file
    s = (
        '{spc}\n\n'
        '{table}\n\n'
        'Variable types for bitblaster:\n\n'
        '{vartypes}\n').format(
            table=vartable, spc=spc,
            vartypes=pprint.pformat(flat_table))
    logger.info(s)
    return spc


def synthesize(code, strict_atomic=True, symbolic=False, **kw):
    """Call GR(1) synthesis tool and return winning transducer.

    @param strict_atomic: if `True`, then deactivate LTL safety
        properties during atomic execution.
    """
    spc = compile_spec(code, strict_atomic)
    mealy = slugs.synthesize(spc, symbolic=symbolic, **kw)
    return mealy


def map_to_future(aut):
    """Translate `Automaton` from full to future FOTL."""
    a = _symbolic.Automaton()
    a.vars = copy.deepcopy(aut.vars)
    for q in ('env', 'sys'):
        # init
        init_dvars, i, f = past.map_translate(
            aut.init[q], aut.vars)
        a.vars.update(init_dvars)
        # a.init[q].extend(i)
        # "previous" in init over-writes anchoring semantics
        a.init[q].extend(f)
        # action
        dvars, i, f = past.map_translate(
            aut.action[q], aut.vars, free_init=init_dvars)
        a.vars.update(dvars)
        a.init[q].extend(i)
        a.action[q].extend(f)
        # win
        dvars, i, f = past.map_translate(
            aut.win[q], aut.vars, free_init=init_dvars)
        a.vars.update(dvars)
        a.init[q].extend(i)
        if q == 'env':
            a.win['<>[]'].extend(f)
        elif q == 'sys':
            a.win['[]<>'].extend(f)
        else:
            raise Exception('unknown case "{q}"'.format(q=q))
    return a


def dump_ltl_to_json(spc):
    def f(x):
        return conj(x).split('\n')
    dvars = dict()
    for var, d in spc.vars.iteritems():
        b = dict(d)
        init = b.get('init')
        if init is not None:
            b['init'] = str(init)
        dvars[var] = b
    d = {
        'vars': dvars,
        'env_init': spc.init['env'],
        'env_safety': f(spc.action['env']),
        'env_prog': spc.win['env'],
        'sys_init': f(spc.init['sys']),
        'sys_safety': f(spc.action['sys']),
        'sys_prog': spc.win['sys']}
    with open(LTL_SPEC, 'w') as f:
        json.dump(d, f, indent=4)
    with open(SPEC_REPR, 'w') as f:
        s = spc.dumps()
        s = textwrap.fill(s, replace_whitespace=False)
        f.write(s)
    # with open('spec_for_gr1c.txt', 'w') as f:
    #    s = translation.translate(spc, 'gr1c')
    #    f.write(s)


def command_line_wrapper():
    """Entry point available as `ospin` script."""
    logs = {'openpromela.logic',
            'openpromela.bitvector',
            'openpromela.slugs',
            'promela.yacc.parser'}
    slugs_log_name = 'openpromela.bitvector.slugs'
    debug_log_file = 'debug_log.txt'
    p = argparse.ArgumentParser(
        description=(
            'Synthesizer from open Promela.\n\n'
            'Beware: unstable version:\n'
            'options may change.\n'))
    p.add_argument('fname', help='Promela input file')
    p.add_argument(
        '-s', '--symbolic', action='store_true',
        help='represent strategy with BDD, instead of enumerated graph')
    p.add_argument(
        '-r', '--realizability', action='store_true',
        help='check only for realizability')
    p.add_argument(
        '--pdf', action='store_true',
        help='dump Mealy graph to file as PDF')
    p.add_argument(
        '-d', '--debug', type=int, default=logging.WARNING,
        help='set python logging level. Dump log files if below DEBUG.')
    p.add_argument(
        '--version', action='version', version=_version.version)
    args = p.parse_args()
    level = args.debug
    fh = logging.FileHandler(debug_log_file, mode='w')
    for name in logs:
        log = logging.getLogger(name)
        log.setLevel(level)
        log.addHandler(fh)
    sh = logging.StreamHandler()
    sh.setLevel(level)
    slugs_log = logging.getLogger(slugs_log_name)
    slugs_log.addHandler(sh)
    with open(args.fname, 'r') as f:
        s = f.read()
    mealy = synthesize(s, symbolic=args.symbolic)
    if mealy:
        print('Realizable')
    else:
        print('Not realizable')
    if not args.symbolic:
        print('Enumerated Mealy machine has {n} nodes.'.format(
            n=len(mealy)))
    if args.pdf:
        if args.symbolic:
            print('BDD not dumped to PDF file.')
        else:
            mealy.dump('out.pdf')
    else:
        if not args.symbolic:
            print(mealy)


if __name__ == '__main__':
    yacc.rebuild_table(_parser, TABMODULE.split('.')[-1])
