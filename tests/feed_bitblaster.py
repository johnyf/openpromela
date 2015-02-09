#!/usr/bin/env python
import json
import logging
from openpromela import bitvector as bv
from tulip.spec import GRSpec


logger = logging.getLogger(__name__)
logging.getLogger('tulip.ltl_parser_log').setLevel(logging.WARNING)
h = logging.StreamHandler()
log = logging.getLogger('openpromela.bitvector')
log.setLevel(logging.ERROR)
log.addHandler(h)


LTL_SPEC = 'spec_ltl.txt'


def load():
    with open(LTL_SPEC, 'r') as f:
        d = json.load(f)
    f = lambda x: ' \n '.join(s for s in x)
    env_vars = d['env_vars']
    sys_vars = d['sys_vars']

    env_init = f(d['env_init'])
    sys_init = f(d['sys_init'])
    env_safety = f(d['env_safety'])
    sys_safety = f(d['sys_safety'])
    env_prog = f(d['env_prog'])
    sys_prog = f(d['sys_prog'])

    vartypes = d['vartypes']
    for d in [env_vars, sys_vars]:
        for k, v in d.iteritems():
            if vartypes[k]['type'] != 'int':
                continue
            # restore tuples
            d[k] = tuple(v)
    gr1 = GRSpec(env_vars=env_vars, sys_vars=sys_vars,
                 env_init=[env_init], sys_init=[sys_init],
                 env_safety=[env_safety], sys_safety=[sys_safety],
                 env_prog=[env_prog], sys_prog=[sys_prog])
    return gr1, vartypes


if __name__ == '__main__':
    gr1, vartypes = load()
    g = bv.synthesize(gr1, vartypes)
    print g
