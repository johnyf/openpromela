"""Interface to `gr1c` synthesizer."""
from __future__ import absolute_import
from omega.symbolic import symbolic
from openpromela.bdd import Nodes as _Nodes
from openpromela.bdd import Parser
from openpromela import bitvector as bv


_SPEC_FILE = 'gr1c_spec.txt'
_JSON_FILE = 'gr1c_mealy.json'


def synthesize(spec):
    aut = symbolic._bitblast(spec)
    return aut


def _dumps_bits(dvars):
    dbits = bv.list_bits(dvars)
    env = [var for var, d in dbits.iteritems()
           if d['owner'] == 'env']
    sys = [var for var, d in dbits.iteritems()
           if d['owner'] == 'sys']
    s = (
        'ENV: {env}\n'
        'SYS: {sys}\n').format(
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
    assert owner in ('env', 'sys'), owner
    c = list()
    c.append('{owner}INIT:'.format(owner=owner.upper()))
    c.extend(translate(s) for s in spec.init[owner])
    c.append('{owner}TRANS:'.format(owner=owner.upper()))
    c.extend(
        '[]({r})'.format(r=translate(s))
        for s in spec.action[owner])
    c.append('{owner}GOAL:'.format(owner=owner.upper()))
    c.extend(
        '[]<>({r})'.format(r=translate(s))
        for s in spec.win[owner])
    c.append('')
    r = '\n'.join(c)
    return r


def translate(s):
    """Return bitblasted formula."""
    tree = _parser.parse(s)
    r = tree.flatten()
    return r


class Nodes(_Nodes):
    """Flattening of slugsin to `gr1c` syntax."""

    class Num(_Nodes.Num):
        def flatten(self, *arg, **kw):
            assert self.value in ('0', '1'), self.value
            if self.value == '0':
                return 'False'
            return 'True'


_parser = Parser(nodes=Nodes())
