"""Translate Promela to linear temporal logic (LTL)"""
from __future__ import absolute_import
import argparse
import copy
import json
import logging
import pprint
import textwrap
import warnings
import networkx as nx
from networkx.utils import misc
from promela import ast, lex, yacc
from openpromela import bitvector, version
from tulip import interfaces, spec
from tulip.spec import gr1_fragment


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
        'async': 'ASYNC'})
    operators = list(lex.Lexer.operators)
    operators.extend(['PRIME'])

    def t_PRIME(self, t):
        r"\'"
        return t


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
        ('left', 'ALWAYS', 'EVENTUALLY'),
        ('left', 'UNTIL', 'WEAK_UNTIL', 'RELEASE'),
        ('right', 'NEXT'),
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
        """sync_unit : proc
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

    class Proctype(ast.Proctype):
        def __init__(self, name, body, owner=None, assume=None, **kw):
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
            # env can't see next value of a program counter
            # controlled by sys, so an assumption process must
            # have pc controlled by env
            # (until a "previous" operator becomes available)
            assert assume == 'sys' or owner == 'env', (
                "Assumption with program counter owned by sys "
                "requires support for 'previous' operator in solver.")
            super(AST.Proctype, self).__init__(name, body, **kw)

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
                dom = 'boolean'
                dtype = 'boolean'
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
                      self.free, owner, length=self.length)

    class VarRef(ast.VarRef):
        def _context(self, d):
            if d['dom'] == 'boolean':
                return 'boolean'
            else:
                return 'numerical'

        def to_logic(self, t, pid):
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
                    s = '(ite {expr} = {i}, {element}, {s})'.format(
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
        def to_logic(self, t, pid):
            flatname, var_context = self.var.to_logic(t, pid)
            value, val_context = self.value.to_logic(t, pid)
            if var_context == 'boolean' or val_context == 'boolean':
                context = 'boolean'
                op = '<->'
            else:
                context = 'numerical'
                op = '='
                d = find_var_in_scope(self.var.name, t, pid)
                dom = d['dom']
                dtype = d['type']
                signed, width = dom_to_width(dom)
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
        def to_logic(self, t, pid, assume):
            c = [stmt.to_guard(t, pid, assume)
                 for stmt in self.other_guards]
            s = _conj('! ({s})'.format(s=s) for s in c)
            return s, 'boolean'

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
                c = 'boolean'
                if op == '==':
                    op = '='  # convert to logic
            elif op in connectives:
                assert xc == 'boolean', self
                assert yc == 'boolean', self
                c = 'boolean'
            else:
                raise Exception('Unknown operator "{op}"'.format(
                    op=op))
            # c = 'boolean'
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
            boolean_unary_operators = {'X', '!'}
            if self.operator in boolean_unary_operators:
                c = 'boolean'
            else:
                c = 'numerical'
            x, xc = self.operands[0].to_logic(*arg, **kw)
            s = '({op} {x})'.format(op=self.operator, x=x)
            if xc == 'boolean':
                c = 'boolean'
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
            return (str(self), 'boolean')

        def to_guard(self, *arg, **kw):
            return (str(self), False)


class VariablesTable(object):
    """Table of variables for synthesis.

    Distinguishes between:

      - controllable and uncontrollable variables
      - free and idle variables

    Attributes of each variable:

      - flatname: `str`
      - dom
      - owner: in `{'env', 'sys'}`
      - free: `bool`

    Attributes for each process:

      - proctype
        `str`
      - owner: of program counter
        in `{'env', 'sys'}`
      - gid: group id of sync product
        `int`
      - lid: local id inside the sync product
        `int`
      - assume: assumption or assertion
        in `{'env', 'sys'}`
    """

    def __init__(self):
        # self.channels = dict()
        self.scopes = {'aux': dict(), 'global': dict()}
        self.pids = dict()
        # struct data types not supported yet

    def __str__(self):
        free = {var
                for pid, localvars in self.scopes.iteritems()
                for var, d in localvars.iteritems()
                if d['free']}
        return (
            '\nTable of variables\n'
            '--------------------\n\n'
            'environment inputs:\n {env}\n\n'
            'system outputs:\n {sys}\n\n'
            'free variables:\n {free}\n').format(
                env=pprint.pformat(self.env),
                sys=pprint.pformat(self.sys),
                free=free)

    @property
    def env(self):
        return self._get_owned_vars('env')

    @property
    def sys(self):
        return self._get_owned_vars('sys')

    def _get_owned_vars(self, owner):
        """Return env or sys variables.

        @type owner: "env" or "sys"
        """
        return [
            (pid, var, d)
            for pid, localvars in self.scopes.iteritems()
            for var, d in localvars.iteritems()
            if d['owner'] == owner]

    @property
    def variables(self):
        return ((pid, var, d)
                for pid, scope in self.scopes.iteritems()
                for var, d in scope.iteritems())

    def add_var(self, pid, name, flatname, dom, dtype,
                free, owner, length=None):
        self.scopes.setdefault(pid, dict())
        d = dict()
        d['flatname'] = flatname
        d['dom'] = dom
        d['type'] = dtype
        d['length'] = length
        d['owner'] = owner
        d['free'] = free
        assert name not in self.scopes[pid], (name, pid)
        self.scopes[pid][name] = d

    def add_pid(self, pid, proctype_name, owner, gid, lid, assume):
        assert owner in {'env', 'sys'}
        assert assume in {'env', 'sys'}
        self.pids[pid] = {
            'proctype': proctype_name,
            'owner': owner,
            'gid': gid,
            'lid': lid,
            'assume': assume}

    def add_program_counter(self, pid, n, owner):
        pc = pid_to_pc(pid)
        dom = (0, n - 1)
        assert pc not in self.scopes['aux']
        if owner != 'env' and owner != 'sys':
            raise ValueError('unknown proctype owner: {owner}'.format(
                             owner=owner))
        self.add_var(pid='aux', name=pc, flatname=pc,
                     dom=dom, dtype='saturating', free=True, owner=owner)

    def to_grspec(self):
        env_vars = {s: copy.copy(d['dom'])
                    for pid, var, d in self.env
                    for s in array_to_flatnames(d['flatname'], d['length'])}
        sys_vars = {s: copy.copy(d['dom'])
                    for pid, var, d in self.sys
                    for s in array_to_flatnames(d['flatname'], d['length'])}
        return env_vars, sys_vars

    def to_slugs(self):
        """Return variables `dict` for `pyggyback.promela.slugs`."""
        var, env_safe = self._to_slugs(self.env, 'env')
        svar, sys_safe = self._to_slugs(self.sys, 'sys')
        var.update(svar)
        return var, env_safe, sys_safe

    def _to_slugs(self, vardefs, owner):
        logger.info(
            '++ convert {owner} vars to slugs'.format(owner=owner))
        vs = dict()
        safety = list()
        for pid, name, d in vardefs:
            dom = d['dom']
            if dom == 'boolean':
                b = {'type': 'bool', 'owner': owner}
            elif isinstance(dom, tuple):
                signed, width = dom_to_width(dom)
                b = {'type': 'int', 'owner': owner,
                     'signed': signed, 'width': width}
            else:
                raise Exception('dom not boolean or tuple')
            flatnames = array_to_flatnames(d['flatname'], d['length'])
            for x in flatnames:
                vs[x] = dict(b)
            # lower bound safety constraints
            if not isinstance(dom, tuple):
                continue
            # int var
            # saturating semantics ?
            dtype = d['type']
            if dtype != 'saturating':
                continue
            dmin, dmax = dom
            safety.extend([
                '({min} <= {x}) & ({x} <= {max})'.format(
                    min=dmin, max=dmax, x=x)
                for x in flatnames])
        logger.debug('result vars:\n {v}'.format(v=vs))
        logger.info('-- done converting vars to slugs\n')
        return vs, _conj(safety)


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


def array_to_flatnames(flatname, length):
    """Return `list` of flatnames for variables that are elements.

    If `d` is not an array, then return the flatname.

    @type d: `dict`
    """
    if length is None:
        return [flatname]
    # array
    # one variable per array element
    return ['{flatname}{i}'.format(flatname=flatname, i=i)
            for i in xrange(length)]


def products_to_logic(products, global_defs):
    max_key = 0
    init = dict()
    trans = dict()
    progress = dict()
    var2edges = dict()
    notexe = dict()
    pcmust = dict()
    t = VariablesTable()
    init['global'] = add_variables_to_table(
        t, global_defs, pid='global', assume_context='sys')
    max_gid = {'env': 0, 'sys': 0}
    for p in products:
        if isinstance(p, AST.Proctype):
            assume = p.assume
        elif isinstance(p, AST.Product):
            proc = next(iter(p.body))
            assume = proc.assume
        else:
            raise TypeError()
        max_gid[assume] += 1
    gids = {'env': 0, 'sys': 0}
    for p in products:
        if isinstance(p, AST.Proctype):
            assume = p.assume
            gid = gids[assume]
            i, tr, prog, v2e, nexe, pm, mk = proctypes_to_logic(
                gid, [p], t, max_gid[assume])
        elif isinstance(p, AST.Product):
            assert p.sync  # for now allow only sync product groups
            proc = next(iter(p.body))
            assume = proc.assume
            gid = gids[assume]
            i, tr, prog, v2e, nexe, pm, mk = proctypes_to_logic(
                gid, p.body, t, max_gid[assume], max_active=1)
            # TODO: collect group var decls
        else:
            raise TypeError('group of type "{t}"'.format(t=type(p)))
        init.update(i)
        trans.update(tr)
        progress.update(prog)
        var2edges.update(v2e)
        notexe.update(nexe)
        pcmust.update(pm)
        max_key = max(max_key, mk)
        gids[assume] += 1
    # find number of keys needed
    # in sync prod multiple program graphs mv simultaneously
    n_keys = dict(env=dict(env=1), sys=dict(env=1, sys=1))
    for p in products:
        if isinstance(p, AST.Product):
            proc = next(iter(p.body))
            assume = proc.assume
            owner = proc.owner
            k = len(p.body)
        else:
            assume = p.assume
            owner = p.owner
            k = 1
        n_keys[assume][owner] = max(n_keys[assume][owner], k)
    # check that all processes in group are
    # either assumptions or assertions
    # note: each pc though can have a different owner
    for p in products:
        if not isinstance(p, AST.Product):
            continue
        proc = next(iter(p.body))
        assume = proc.assume
        for proc in p.body:
            if proc.assume != assume:
                raise Exception(
                    'Not all processes in sync product '
                    'are {side}.'.format(
                        side='assumptions'
                        if assume == 'env' else 'assertions'))
    # add key vars to table
    init_keys = {'env': list(), 'sys': list()}
    for assume, d in n_keys.iteritems():
        for owner, nk in d.iteritems():
            for i in xrange(nk):
                var = key_str(assume, owner, i)
                dom = (0, max_key)
                t.add_var(pid='global', name=var, flatname=var,
                          dom=dom, dtype='saturating', free=True, owner=owner)
                init_keys[owner].append('{var} = 0'.format(var=var))
    # assemble spec
    env_imp = constrain_imperative_vars(var2edges, t, 'env')
    sys_imp = constrain_imperative_vars(var2edges, t, 'sys')
    env_decl, sys_decl = constrain_local_declarative_vars(t)
    env_safe = [env_imp, env_decl]
    sys_safe = [sys_imp, sys_decl]
    for player in {'env', 'sys'}:
        ei, si, e, s = add_process_scheduler(t, trans, notexe, pcmust, player)
        init_keys['env'].append(ei)
        init_keys['sys'].append(si)
        env_safe.append(e)
        sys_safe.append(s)
    env_init = _conj(
        [_conj(x['env']) for x in init.itervalues()] +
        init_keys['env'])
    sys_init = _conj(
        [_conj(x['sys']) for x in init.itervalues()] +
        init_keys['sys'])
    env_safe = _conj(env_safe)
    sys_safe = _conj(sys_safe)
    env_prog = [y for x in progress.itervalues()
                for y in x['env']]
    sys_prog = [y for x in progress.itervalues()
                for y in x['sys']]
    return (
        t, env_init, sys_init, env_safe, sys_safe,
        env_prog, sys_prog, max_gid)


def proctypes_to_logic(gid, proctypes, t, max_gid, max_active=None):
    max_key = 0
    init = dict()
    trans = dict()
    progress = dict()
    var2edges = dict()
    notexe = dict()
    pcmust = dict()
    # lid = local id inside a sync product
    for lid, p in enumerate(proctypes):
        i, tr, prog, v2e, nexe, pm, mk = proctype_to_logic(
            gid, lid, p, t, max_gid, max_active)
        init.update(i)
        trans.update(tr)
        progress.update(prog)
        var2edges.update(v2e)
        notexe.update(nexe)
        pcmust.update(pm)
        max_key = max(max_key, mk)
    return init, trans, progress, var2edges, notexe, pcmust, max_key


def proctype_to_logic(gid, lid, p, t, max_gid, max_active=None):
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
    g.name = p.name
    g.owner = p.owner
    g.assume = p.assume
    max_key = max_edge_multiplicity(g)
    # instantiate each instance
    init = dict()
    trans = dict()
    progress = dict()
    var2edges = dict()
    notexe = dict()
    pcmust = dict()
    # above it is ensured that in sync products only 1 active
    for j in xrange(active):
        logger.info('\t instance {j}'.format(j=j))
        pid, i, tr, prog, v2e, nexe, pm = process_to_logic(
            gid, lid, g, t, max_gid)
        init[pid] = i
        trans[pid] = tr
        progress[pid] = prog
        var2edges[pid] = v2e
        notexe[pid] = nexe
        if pm:
            pcmust[pid] = pm
    logger.info('-- done with proctype "{name}".\n'.format(
        name=name))
    return init, trans, progress, var2edges, notexe, pcmust, max_key


def max_edge_multiplicity(g, n=None):
    """Return the outgoing edge with most copies."""
    if n is not None:
        assert n in g
        nbunch = [n]
    else:
        nbunch = g
    return max(len(uv) for u in nbunch for v, uv in g.succ[u].iteritems())


# a process is an instance of a proctype
def process_to_logic(gid, lid, g, t, max_gid):
    pid = len(t.pids)
    t.add_pid(pid, g.name, g.owner, gid, lid, assume=g.assume)
    pc = pid_to_pc(pid)
    init = add_variables_to_table(t, g.locals, pid, g.assume)
    init[g.owner].append('({pc} = {root})'.format(pc=pc, root=g.root))
    # create graph annotated with formulae
    h = nx.MultiDiGraph()
    var2edges = add_edge_formulae(h, g, t, pid)
    trans = graph_to_logic(h, t, pid, max_gid)
    notexe = form_notexe_condition(g, t, pid)
    progress = collect_progress_labels(g, t, pid)
    t.add_program_counter(pid, len(h), g.owner)
    if g.assume == 'sys' and g.owner == 'env':
        pcmust = graph_to_guards(g, t, pid)
    else:
        pcmust = ''
    logger.debug('transitions of process "{pc}":\n {t}'.format(
                 pc=pc, t=trans))
    return pid, init, trans, progress, var2edges, notexe, pcmust


def add_variables_to_table(t, r, pid, assume_context):
    """Return logic formula equivalent to program graph.

    @type t: VariablesTable
    @type r: iterable of `VarDef`
    @param assume_context: default owner

    @rtype: `dict` of `list`
    """
    init = {'env': list(), 'sys': list()}
    for x in r:
        assert isinstance(x, ast.VarDef), x
        x.insert_logic_var(t, assume_context, pid)
        # free var decl w/o assignment ?
        if x.initial_value is None:
            continue
        # it is correct to lookup in pid because these are local defs
        d = t.scopes[pid][x.name]
        x_owner = d['owner']
        if d['dom'] == 'boolean':
            op = '<->'
        else:
            op = '='
        # handle arrays
        for name in array_to_flatnames(d['flatname'], d['length']):
            s = '{flatname} {op} {value}'.format(
                op=op,
                flatname=name,
                value=x.initial_value)
            init[x_owner].append(s)
    return init


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
    if logger.getEffectiveLevel() < logging.DEBUG:
        ast.dump_graph(
            g, fname='pid_{pid}_pg.pdf'.format(pid=pid), edge_label='stmt')
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


def graph_to_logic(g, t, pid, max_gid):
    """Return temporal logic formula encoding edges.

    The graph vertices must be integers.

    @param k: index of key (for processes in sync products)
    """
    pc = pid_to_pc(pid)
    aux = pid_to_key(t, pid)
    dpid = t.pids[pid]
    assume = dpid['assume']
    gid = dpid['gid']
    pm = pm_str(assume)
    c = list()
    for u, du in g.nodes_iter(data=True):
        assert isinstance(u, int), u
        oute = list()
        for u_, v, key, d in g.out_edges_iter(u, data=True, keys=True):
            assert isinstance(v, int)
            v_context = g.node[v]['context']
            if v_context is None:
                exclusive = ((
                    '((X ex_{assume} = {max_gid}) & (X ! {pm}))').format(
                        assume=assume,
                        max_gid=max_gid,
                        pm=pm))
            elif v_context == 'atomic':
                exclusive = ((
                    '((X ex_{assume} = {gid}) & (X {pm}))').format(
                        assume=assume,
                        gid=gid,
                        pm=pm))
            else:
                raise Exception('Found context: {c}'.format(c=v_context))
            alt = 'X(({pc} = {j}) & ({aux} = {k}))'.format(
                pc=pc, j=v, aux=aux, k=key)
            f = d.get('formula')
            if f is not None:
                alt = '{t} & ({f}) & {exclusive}'.format(
                    t=alt, f=f, exclusive=exclusive)
            oute.append(alt)
        if not oute:
            oute.append('X(False)')
        precond = '({pc} = {i})'.format(pc=pc, i=u)
        postcond = _disj(oute, sep='\n\t')
        t = '{a} -> ({b})'.format(a=precond, b=postcond)
        c.append(t)
    return _conj(c, sep='\n')


def form_notexe_condition(g, t, pid):
    """Return map from nodes to blocking conditions.

    @return: Map from nodes to Boolean formulae.
        Each node blocks if the formula is `True`.
    @rtype: `dict` of `str`
    """
    pc = pid_to_pc(pid)
    disj = dict()
    for u in g:
        r = list()
        # at least one outedge always executable ?
        for _, v, key, d in g.edges_iter(u, data=True, keys=True):
            c = d.get('stmt')
            assert isinstance(c, (AST.Assignment, AST.Expression, AST.Else))
            e = c.to_guard(t, pid, g.assume)
            r.append(e)
            if e == 'True':
                break
        # u blocks if no executability condition is True
        disj[u] = _disj(r)
    return _disj(
        '({pc} = {u}) & !({b})'.format(pc=pc, u=u, b=b)
        for u, b in disj.iteritems())


def graph_to_guards(g, t, pid):
    """Require that selected edge is executable.

    Only used for assertions with pc controlled by env.
    (so for model/module (LTL) checking)
    """
    assert g.owner == 'env', g.owner
    assert g.assume == 'sys', g.assume
    aux = pid_to_key(t, pid)
    pc = pid_to_pc(pid)
    c = list()
    # transition relation for env to select only
    # executable edges
    # prevent env from seleting inexistent edges
    for u in g:
        r = list()
        for _, v, key, d in g.edges_iter(u, keys=True, data=True):
            e = d.get('stmt').to_guard(t, pid, g.assume)
            r.append((
                '(X {pc} = {v}) & '
                '(X {aux} = {key}) & '
                '({guard})').format(
                    pc=pc, aux=aux, u=u, v=v, key=key, guard=e))
        trans = _disj(r)
        # find max outgoing edge multiplicity
        n = max_edge_multiplicity(g, u)
        assert (n == 0) == (not g.succ[u])
        c.append(
            '( ({pc} = {u}) -> '
            '( ( (X {aux}) < {n} ) & ({trans}) )'
            ')'.format(
                pc=pc, u=u, aux=aux, n=n, trans=trans))
    return _conj(c)


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
        c = gr1_fragment.split_gr1(f)
        [d[assume][k].extend(v) for k, v in c.iteritems()]
    # conjoin (except for liveness)
    for assume in {'assume', 'assert'}:
        for part in {'init', 'G'}:
            d[assume][part] = _conj(d[assume][part])
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
        c = isinstance(u, AST.Next) or c
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
    elif isinstance(u, (AST.VarRef, AST.Integer, AST.Bool)):
        g.add_node(u)
    else:
        raise TypeError(
            'unknown AST node type "{t}"'.format(t=type(u)))
    return g


def constrain_imperative_vars(var2edges, t, player='sys'):
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
            if var in var2edges[pid]:
                edges = var2edges[pid][var]
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
            f=_conj(c, sep='\n'),
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
        for pid, v2e in var2edges.iteritems():
            # local var with same name exists ?
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
            f=_disj(b, sep='\n'),
            invariant=inv,
            array_inv=_conj(z, sep='\n'))
        c.append(w)
    if c:
        comment = '\n\n# global imperative var constraints\n'
        s = '{comment}{f}'.format(
            f=_conj(c, sep='\n'),
            comment=comment)
        gl.append(s)
    return _conj(gl)


def _constrain_imperative_var(t, pid, var, edges):
    logger.debug(
        'the edges for "{var}" are: {e}'.format(var=var, e=edges))
    assert edges
    ps = pid_to_ps(t, pid)
    pc = pid_to_pc(pid)
    gid = t.pids[pid]['gid']
    aux = pid_to_key(t, pid)
    d = find_var_in_scope(var, t, pid)
    dom = d['dom']
    c = list()
    for u, v, key, _ in edges:
        s = edge_str(ps, gid, pc, u, v, aux, key)
        c.append(s)
    disj = _disj(c, sep='\n\t')
    # scalar ?
    if d['length'] is None:
        return disj, 'True'
    # array elements remain invariant if not referenced
    flatnames = array_to_flatnames(d['flatname'], d['length'])
    a = list()
    for u, v, key, indices in edges:
        r = list()
        for i, flat in enumerate(flatnames):
            ys = [e.to_logic(t, pid)[0] for e in indices]
            conj = _conj('{y} != {i}'.format(y=y, i=i) for y in ys)
            inv = _invariant(flat, dom)
            cond = '({conj}) -> ({inv})'.format(conj=conj, inv=inv)
            r.append(cond)
        econj = _conj(r)
        edge = edge_str(ps, gid, pc, u, v, aux, key)
        cond = '({edge}) -> ({econj})'.format(econj=econj, edge=edge)
        a.append(cond)
    conj = _conj(a, sep='\n\t')
    return disj, conj


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


def edge_str(ps, gid, pc, u, v, aux, key):
    return _conj([
        'X({ps} = {gid})'.format(ps=ps, gid=gid),
        '({pc} = {u})'.format(pc=pc, u=u),
        'X({pc} = {v})'.format(pc=pc, v=v),
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
            s = 'X({ps} != {gid}) -> {invariant}'.format(
                ps=ps, gid=gid, invariant=_invariant(
                    d['flatname'], d['dom'], d['length']))
            var_owner = d['owner']
            c[var_owner].append(s)
    for k, v in c.iteritems():
        c[k] = '\n\n# declarative var constraints\n{f}'.format(
            f=_conj(v, sep='\n'))
    logger.info('-- done with free local vars.\n')
    return c['env'], c['sys']


def add_process_scheduler(t, trans, notexe, pcmust, player):
    logger.info('adding process scheduler...')
    assert player in {'env', 'sys'}
    # env controls both selectors:
    # selector among env pids
    # envps = 'env_ps'
    # selector among sys pids
    # sysps = 'sys_ps'
    #
    # clauses
    ps = ps_str(player)
    deadlock = dict()
    init = {'env': list(), 'sys': list()}
    safety = {'env': list(), 'sys': list()}
    gids = set()
    for pid, f in trans.iteritems():
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
        ps_pid = pid_to_ps(t, pid)
        assert ps_pid == ps
        gid = dpid['gid']
        gids.add(gid)
        pc = pid_to_pc(pid)
        pc_dom = t.scopes['aux'][pc]['dom']
        pc_owner = dpid['owner']
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
                ps=ps, gid=gid, trans=f))
        # idle program counter
        safety[pc_owner].append((
            '\n# idle program counter:\n'
            '((X {ps} != {gid}) -> {invariant})').format(
                ps=ps, gid=gid, invariant=_invariant(pc, pc_dom)))
        # prevent env from selecting non-executable edge
        if pc_owner == 'env' and assume == 'sys':
            safety[pc_owner].append(
                '\n# prevent env from selecting blocked edge\n'
                '( (X {ps} = {gid}) -> ({pcmust}) )'.format(
                    ps=ps, gid=gid, pcmust=pcmust[pid]))
        # prevent scheduler from selecting a non-executable process
        blocks_if = notexe[pid]
        safety['env'].append((
            '\n# prevent scheduler from selecting blocked process\n'
            '({nexe}) -> (X {ps} != {gid})').format(
                nexe=blocks_if, ps=ps, gid=gid))
        deadlock.setdefault(gid, list()).append(blocks_if)
        # grant exclusive execution to requestor if executable
        ex = 'ex_{assume}'.format(assume=assume)
        safety['env'].append((
            '\n# grant request for exclusive execution\n'
            '( (({ex} = {gid}) & !({nexe})) -> '
            '(X {ps} = {gid}) )').format(
                ex=ex, gid=gid, nexe=blocks_if, ps=ps))
    # player has no processes ?
    if not gids:
        return ('', '', '', '')
    # assert contiguous gids
    max_gid = len(gids)
    assert gids == set(xrange(max_gid)), gids
    # last value means deadlock
    if max_gid:
        if player == 'sys':
            safety[player].append((
                '\n\n# never deadlock:\n'
                '(X {ps} != {max_gid})\n').format(ps=ps, max_gid=max_gid))
        elif player == 'env':
            other_player = 'sys'
            pm_env = pm_str(other_player)
            safety[player].append((
                '\n\n# never deadlock, unless preempted by sys:\n'
                '((X {ps} = {max_gid}) <-> {pm})\n').format(
                    ps=ps, max_gid=max_gid, pm=pm_env))
        else:
            raise Exception('Unknown player "{player}"'.format(player=player))
    # define ps variable
    ps_dom = (0, max_gid)
    t.add_var(pid='global', name=ps, flatname=ps,
              dom=ps_dom, dtype='saturating', free=True, owner='env')
    # define "exclusive" variables for requesting atomic execution
    ex = 'ex_{player}'.format(player=player)
    ex_dom = ps_dom
    t.add_var(pid='aux', name=ex, flatname=ex,
              dom=ex_dom, dtype='saturating', free=True, owner=player)
    init[player].append('({ex} = {max_gid})'.format(
        ex=ex,
        max_gid=max_gid))
    # define preemption variables for atomic execution
    # that stops also the other player
    pm = pm_str(player)
    t.add_var(pid='aux', name=pm, flatname=pm,
              dom='boolean', dtype='saturating', free=True, owner=player)
    init[player].append('(! {pm})'.format(pm=pm))
    # if all processes block, signal deadlock
    # a False means that some process is always executable
    assert deadlock, deadlock
    # handle process products
    c = list()
    for gid, v in deadlock.iteritems():
        s = _disj(v)
        c.append(s)
    deadlocked = _conj(c, sep='\n')
    if player == 'env':
        safety['env'].append(
            '\n# deadlock\n' +
            "\n ( ({deadlocked}) -> (X {ps} = {max_gid}) )\n".format(
                deadlocked=deadlocked,
                ps=ps, max_gid=max_gid))
    elif player == 'sys':
        safety['env'].append(
            '\n# deadlock\n' +
            "\n ( ({deadlocked}) <-> (X {ps} = {max_gid}) )\n".format(
                deadlocked=deadlocked,
                ps=ps, max_gid=max_gid))
    logger.info('done with process scheduler.\n')
    return (
        _conj(init['env']),
        _conj(init['sys']),
        _conj(safety['env'], sep=2*'\n'),
        _conj(safety['sys'], sep=2*'\n'))


def pid_to_ps(t, pid):
    """Return process scheduler variable.

    Assertions are selected to execute by `sys_ps`,
    assumptions by `env_ps`.
    Note that env may control the program counter of an assertion.
    """
    assume = t.pids[pid]['assume']
    assert assume in {'env', 'sys'}
    return ps_str(assume)


def ps_str(player):
    """Return identifier of process selection variable."""
    return '{player}_ps'.format(player=player)


def pid_to_pc(pid):
    """Return program counter variable for given `pid`.

    The process owner controls this variable.
    """
    return 'pc{pid}'.format(pid=pid)


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
    return '{assume}{owner}key{lid}'.format(
        assume=assume, owner=owner, lid=lid)


def pm_str(player):
    """Return identifier for preemption auxiliary variable.

    When `player` wants to request that the other player
    pause while it executes atomically,
    it sets this variable to `True`.
    """
    return 'pm_{player}'.format(player=player)


def _conj(iterable, sep=''):
    return _associative_op(iterable, '&', sep)


def _disj(iterable, sep=''):
    return _associative_op(iterable, '|', sep)


def _associative_op(iterable, op, sep):
    """Apply associative binary operator `op`, using `sep` as separator."""
    if op not in {'&', '|'}:
        raise Exception('operator "{op}" not supported.'.format(op=op))
    true = 'True'
    false = 'False'
    if op == '&':
        true, false = false, true
    glue = ') ' + sep + op + ' ('
    # avoid consuming a generator
    h = [x for x in iterable if x]
    return _recurse_op(0, len(h), h, true, false, glue)


def _recurse_op(a, b, h, true, false, glue):
    """Apply binary operator recursively.

    @param a: start of sublist
    @type a: int in [0, len(h)]
    @param b: end of sublist
    @type b: int in [0, len(h)]
    @param h: `list`
    @param true, false: permutation of 'True', 'False'
    @param glue: used to concatenate a, b
    """
    n = b - a
    # empty ?
    if not n:
        return false
    # singleton ?
    if n == 1:
        return h[a]
    # power of 2 ?
    m = (n - 1).bit_length() - 1
    c = a + 2**m
    x = _recurse_op(a, c, h, true, false, glue)
    y = _recurse_op(c, b, h, true, false, glue)
    # controlling value ?
    # don't care ?
    if x == true or y == true:
        return true
    if x == false:
        return y
    if y == false:
        return x
    return '(' + x + glue + y + ')'


def _paren(iterable):
    return ('(' + x + ')' for x in iterable)


def _invariant(flatname, dom, length=None):
    if dom == 'boolean':
        op = '<->'
    else:
        op = '='
    # scalar ?
    if length is None:
        return '((X {var}) {op} {var})'.format(var=flatname, op=op)
    # array
    c = list()
    for ei in array_to_flatnames(flatname, length):
        s = '((X {var}) {op} {var})'.format(var=ei, op=op)
        c.append(s)
    return _conj(c)


def synthesize(code, strict_atomic=True, symbolic=False, **kw):
    """Call GR(1) synthesis tool and return winning transducer.

    @param strict_atomic: if `True`, then deactivate LTL safety
        properties during atomic execution.
    """
    parser = Parser()
    program = parser.parse(code)
    global_defs, products, ltl = program.to_table()
    (vartable, env_init, sys_init, env_safe,
     sys_safe, env_prog, sys_prog, max_gid) = \
        products_to_logic(products, global_defs)
    ltl_spc = transform_ltl_blocks(ltl, vartable)
    vartypes, env_lim_safe, sys_lim_safe = vartable.to_slugs()
    # conjoin with ltl blocks
    env_init = _conj([env_init, ltl_spc['assume']['init']])
    env_safe = _conj([env_safe, ltl_spc['assume']['G'], env_lim_safe])
    env_prog = env_prog + ltl_spc['assume']['GF']
    env_prog = [x for x in env_prog if x != 'True']
    if not env_prog:
        env_prog = list()
    sys_init = _conj([sys_init, ltl_spc['assert']['init']])
    # deactivate LTL safety during atomic transitions ?
    safe_ltl = ltl_spc['assert']['G']
    if strict_atomic and 'ex_sys' in vartable.scopes['aux']:
        safe_ltl = '((ex_sys < {max_gid}) | {safe})'.format(
            max_gid=max_gid['sys'], safe=safe_ltl)
    sys_safe = _conj([sys_safe, safe_ltl, sys_lim_safe])
    sys_prog = sys_prog + ltl_spc['assert']['GF']
    sys_prog = [x for x in sys_prog if x != 'True']
    if not sys_prog:
        sys_prog = list()
    env_vars, sys_vars = vartable.to_grspec()
    spc = spec.GRSpec(env_vars=env_vars, sys_vars=sys_vars,
                      env_init=env_init, sys_init=sys_init,
                      env_safety=env_safe, sys_safety=sys_safe,
                      env_prog=env_prog, sys_prog=sys_prog)
    # dump table and spec to file
    s = (
        '{spc}\n\n'
        '{table}\n\n'
        'Variable types for bitblaster:\n\n'
        '{vartypes}\n').format(
            table=vartable, spc=spc.pretty(),
            vartypes=pprint.pformat(vartypes))
    logger.info(s)
    if logger.getEffectiveLevel() < logging.DEBUG:
        dump_ltl_to_json(spc, vartypes)
    return bitvector.synthesize(spc, vartypes,
                                symbolic=symbolic, **kw)


def dump_ltl_to_json(spc, vartypes):
    f = lambda x: _conj(x).split('\n')
    d = {
        'env_vars': spc.env_vars,
        'env_init': spc.env_init,
        'env_safety': f(spc.env_safety),
        'env_prog': spc.env_prog,
        'sys_vars': spc.sys_vars,
        'sys_init': f(spc.sys_init),
        'sys_safety': f(spc.sys_safety),
        'sys_prog': spc.sys_prog}
    d['vartypes'] = vartypes
    with open(LTL_SPEC, 'w') as f:
        json.dump(d, f, indent=4)
    with open(SPEC_REPR, 'w') as f:
        s = repr(spc)
        s = textwrap.fill(s, replace_whitespace=False)
        f.write(s)
    # with open('spec_for_gr1c.txt', 'w') as f:
    #    s = translation.translate(spc, 'gr1c')
    #    f.write(s)


def synthesize_using_slugs_own_compiler(
    vartable, env_init, sys_init, env_safe, sys_safe
):
    """Useful for cross-testing for correctness."""
    env_vars, sys_vars = vartable.to_grspec()
    spc = spec.GRSpec(env_vars=env_vars, sys_vars=sys_vars,
                      env_init=env_init, sys_init=sys_init,
                      env_safety=env_safe, sys_safety=sys_safe)
    logger.info(spc.to_canon())
    g = interfaces.slugs.synthesize(spc)
    pprint.pprint(g.nodes(data=True))
    pprint.pprint(g.edges(data=True))
    return g


def command_line_wrapper():
    """Entry point available as `ospin` script."""
    logs = {'openpromela.logic',
            'openpromela.bitvector'}
    slugs_log_name = 'openpromela.bitvector.slugs'
    parser = argparse.ArgumentParser(
        description=(
            'Synthesizer from open Promela.\n\n'
            'Beware: unstable version:\n'
            'options may change.\n'))
    parser.add_argument('fname', help='Promela input file')
    parser.add_argument(
        '-s', '--symbolic', action='store_true',
        help='represent strategy with BDD, instead of enumerated graph')
    parser.add_argument(
        '-r', '--realizability', action='store_true',
        help='check only for realizability')
    parser.add_argument(
        '--pdf', action='store_true',
        help='dump Mealy graph to file as PDF')
    parser.add_argument(
        '-d', '--debug', type=int, default=logging.WARNING,
        help='set python logging level. Dump log files if below DEBUG.')
    parser.add_argument(
        '--version', action='version', version=version.version)
    args = parser.parse_args()
    for name in logs:
        log = logging.getLogger(name)
        log.setLevel(args.debug)
    sh = logging.StreamHandler()
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
            print('BDD not dumped to file yet.')
        else:
            mealy.dump('out.pdf')
    else:
        if not args.symbolic:
            print(mealy)


if __name__ == '__main__':
    parser = Parser()
    yacc.rebuild_table(parser, TABMODULE.split('.')[-1])
