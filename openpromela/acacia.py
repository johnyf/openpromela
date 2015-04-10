"""Interface to Acacia+ synthesizer."""
from __future__ import absolute_import
import logic.symbolic
from openpromela.bdd import Nodes as _Nodes
from openpromela.bdd import Parser
from openpromela import bitvector as bv


LTL_FILE = 'ltl_acacia.txt'
VAR_FILE = 'io_acacia.txt'
BDD_FILE = 'bdd.txt'
OPMAP = {'&': '&&', '|': '||'}


def synthesize(spec):
    aut = logic.symbolic._bitblast(spec)
    bits = dumps_bits(aut.vars)
    spec = dumps_ltl(aut)
    # TODO: write to files
    # TODO: call Acacia+
    # TODO: load result
    return mealy


def _dumps_bits(dvars):
    dbits = bv.list_bits(dvars)
    env = [var for var, d in dbits.iteritems()
           if d['owner'] == 'env']
    sys = [var for var, d in dbits.iteritems()
           if d['owner'] == 'sys']
    s = (
        '.inputs {env}\n'
        '.outputs {sys}\n').format(
            env=' '.join(env),
            sys=' '.join(sys))
    return s


def _dumps_ltl(spec):
    c = list()
    for owner in ('env', 'sys'):
        r = _dumps_owner(spec, owner)
        c.append(r)
    return '\n\n'.join(c)


def _dumps_owner(spec, owner):
    c = list()
    c.extend(translate(s) for s in spec.init[owner])
    c.extend(
        '[]({r})'.format(r=translate(s))
        for s in spec.action[owner])
    c.extend(
        '[]<>({r})'.format(r=translate(s))
        for s in spec.win[owner])
    # assumtions ?
    if owner == 'env':
        c = list('assume {s}'.format(s=s) for s in c)
    c.append('')
    r = ';\n'.join(c)
    return r


def translate(s):
    """Return LTL2BA formula from SLUGSIN `s`."""
    tree = _parser.parse(s)
    r = tree.flatten()
    return r


class Nodes(_Nodes):
    """Flattening of slugsin to LTL2BA syntax."""

    class Operator(_Nodes.Operator):
        def flatten(self, *arg, **kw):
            op = OPMAP.get(self.operator, self.operator)
            if len(self.operands) == 1:
                return ' '.join([
                    '(',
                    op,
                    self.operands[0].flatten(*arg, **kw),
                    ')'])
            assert len(self.operands) == 2, self.operands
            return ' '.join([
                '(',
                self.operands[0].flatten(*arg, **kw),
                op,
                self.operands[1].flatten(*arg, **kw),
                ')'])

    class Var(_Nodes.Var):
        def flatten(self, *arg, **kw):
            var = self.value
            # primed ?
            # (prefix parser doesn't know about "next")
            if var.endswith("'"):
                return '(X {var})'.format(var=var[:-1])
            return var

    class Num(_Nodes.Num):
        def flatten(self, *arg, **kw):
            assert self.value in ('0', '1'), self.value
            if self.value == '0':
                return 'false'
            return 'true'


_parser = Parser(nodes=Nodes())
