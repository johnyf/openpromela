#!/usr/bin/env python
import argparse
import datetime
import logging
import re
import shutil
import time
import matplotlib as mpl
from matplotlib import pyplot as plt
import numpy as np
from openpromela import logic
import psutil


INPUT_FILE = 'amba.pml'
DEBUG = False  # for this script only
N = 2
M = 17


logger = logging.getLogger(__name__)
mpl.rc('xtick', labelsize=7)
mpl.rc('ytick', labelsize=7)
mpl.rc('font', size=7)


def form_progress(i):
    """Return conjunction of LTL formulae for progress."""
    prog = ' && '.join(
        '[]<>(request[{k}] -> (master == {k}))'.format(k=k)
        for k in xrange(i))
    return 'assert ltl { ' + prog + ' }'


if __name__ == '__main__':
    # args
    p = argparse.ArgumentParser()
    p.add_argument('--min', default=N, type=int,
                   help='from this # of masters')
    p.add_argument('--max', default=M, type=int,
                   help='to this # of masters')
    p.add_argument('--debug', type=int, default=logging.ERROR,
                   help='python logging level')
    p.add_argument('--log', action='store_true',
                   help='dump debug log file')
    p.add_argument('--plotonly', action='store_true',
                   help='use existing log files to generate plots')
    args = p.parse_args()
    n = args.min
    m = args.max + 1
    # config logging
    # log to file
    level = args.debug
    # slugs memory log files
    level = logging.DEBUG - 1
    log = logging.getLogger('openpromela.slugs')
    log.setLevel(level)
    log = logging.getLogger('openpromela.slugs.slugs')
    log.setLevel(level)
    log = logging.getLogger('openpromela.slugs.details')
    log.setLevel(level)
    # own logger to screen
    if DEBUG:
        sh = logging.StreamHandler()
        logger.addHandler(sh)
        logger.setLevel(logging.DEBUG)
    all_vars = list()
    env_vars = list()
    strategy_sizes = list()
    total_time = list()
    realizability_time = list()
    for i in xrange(n, m):
        # check if other users
        users = psutil.get_users()
        if len(users) > 1:
            print('warning: other users logged in'
                  '(may start running expensive jobs).')
        # input and iter
        #
        # use this for revised AMBA spec
        input_file = INPUT_FILE
        #
        # use this for original AMBA spec
        # input_file = 'amba_{i}.txt'.format(i=i)
        #
        # use this for original AMBA spec with fairness as BA
        # input_file = 'amba_{i}_merged.txt'.format(i=i)
        with open(input_file) as f:
            s = f.read()
        # prep input
        j = i - 1
        newline = '#define N {j}'.format(j=j)
        code = re.sub('#define N.*', newline, s)
        logger.debug(code)
        # add multiple weak fairness assumptions
        # c += form_progress(i)
        # log and strategy file names
        bdd_file = 'bdd_{i}_masters.txt'.format(i=i)
        time_file = 'log_{i}_masters.txt'.format(i=i)
        logged_details_file = 'slugs_details.txt'
        details_file = 'details_{i}_masters.txt'.format(i=i)
        if not args.plotonly:
            print('starting {i} masters...'.format(i=i))
            # assign log file for timing
            fh_time = logging.FileHandler(time_file)
            log = logging.getLogger('openpromela.slugs.slugs')
            log.addHandler(fh_time)
            # run
            t0 = time.time()
            r = logic.synthesize(code, symbolic=True, bddfile=bdd_file)
            t1 = time.time()
            dt = datetime.timedelta(seconds=t1 - t0)
            # close log files
            log = logging.getLogger('openpromela.slugs.slugs')
            log.removeHandler(fh_time)
            fh_time.close()
            assert r is not None, 'NOT REALISABLE !!!'
            print('Done synthesizing {i} masters in {dt}.'.format(i=i, dt=dt))
            # copy log file
            shutil.copy(logged_details_file, details_file)
        # parse and plot the details
        expr = (
            'time \(ms\): ([\d.]+), '
            'reordering \(ms\): ([\d.]+), '
            'sysj: ([\d]+), '
            'envi: ([\d]+), '
            'nodes: all: ([\d]+), '
            'Z: ([\d]+), '
            'Y: ([\d]+), '
            'X: ([\d]+)')
        expr2 = (
            'time \(ms\): ([\d.]+), '
            'reordering \(ms\): ([\d]+), '
            'goal: ([\d]+), '
            'onion_ring: ([\d]+), '
            'nodes: all: ([\d]+), '
            'strategy: ([\d]+), '
            'cases_covered: ([\d]+), '
            'new_cases: ([\d]+)\n')
        expr3 = (
            'time \(ms\): ([\d.]+), '
            'reordering \(ms\): ([\d]+), '
            'goal: ([\d]+), '
            'nodes: all: ([\d]+), '
            'combined_strategy: ([\d]+)')
        times = list()
        reorder = list()
        sys = list()
        env = list()
        nodes = list()
        x_nodes = list()
        y_nodes = list()
        z_nodes = list()
        # strategy construction
        strategy_time = list()
        strategy_reorder = list()
        strategy_goal = list()
        strategy_onion = list()
        strategy_nodes = list()
        strategy_strategy = list()
        strategy_cases = list()
        strategy_new_cases = list()
        # conj construction
        conj_time = list()
        conj_reorder = list()
        conj_goal = list()
        conj_nodes = list()
        conj_strategy = list()
        with open(details_file, 'r') as f:
            for line in f:
                c = re.findall(expr, line)
                if c:
                    t, r, sys_j, env_i, n, z, y, x = c[0]
                    times.append(t)
                    reorder.append(r)
                    sys.append(sys_j)
                    env.append(env_i)
                    nodes.append(n)
                    x_nodes.append(x)
                    y_nodes.append(y)
                    z_nodes.append(z)
                else:
                    c = re.findall(expr2, line)
                    if c:
                        t, r, g, ring, n, strategy, nc, nn = c[0]
                        strategy_time.append(t)
                        strategy_reorder.append(r)
                        strategy_goal.append(g)
                        strategy_nodes.append(n)
                        strategy_strategy.append(strategy)
                        strategy_cases.append(nc)
                        strategy_new_cases.append(nn)
                    else:
                        c = re.findall(expr3, line)
                        if not c:
                            continue
                        t, r, g, n, strategy = c[0]
                        conj_time.append(t)
                        conj_reorder.append(r)
                        conj_goal.append(g)
                        conj_nodes.append(n)
                        conj_strategy.append(strategy)
        times = np.array(times, dtype=float)
        strategy_time = np.array(strategy_time, dtype=float) + times[-1]
        conj_time = np.array(conj_time, dtype=float) + times[-1]
        # print list(zip(times, reorder, sys, env,
        #            nodes, x_nodes, y_nodes, z_nodes))
        n = 7
        fig = plt.figure()
        fig.set_size_inches(5, 10)
        plt.clf()
        plt.subplots_adjust(hspace=0.3)
        ax = plt.subplot(n, 1, 1)
        ax.set_aspect('equal')
        plt.plot(times, reorder)
        plt.plot(strategy_time, strategy_reorder)
        plt.plot([strategy_time[-1], conj_time[0]],
                 [strategy_reorder[-1], conj_reorder[0]], '--')
        plt.plot(conj_time, conj_reorder)
        plt.axvspan(strategy_time[0], strategy_time[-1],
                    facecolor='g', alpha=0.2, edgecolor='none',
                    zorder=10)
        x_bisector = [0, conj_time[-1]]
        plt.plot(x_bisector, x_bisector, 'k:')
        plt.locator_params(nbins=4)
        plt.ylabel('Reordering (ms)')
        plt.grid()
        ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # goals
        ax = plt.subplot(n, 1, 2)
        plt.plot(times, sys)
        plt.plot(strategy_time, strategy_goal)
        plt.plot(conj_time, conj_goal)
        plt.axvspan(strategy_time[0], strategy_time[-1],
                    facecolor='g', alpha=0.2, edgecolor='none',
                    zorder=10)
        plt.ylabel('Goal $j$')
        plt.grid()
        ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # assumptions
        ax = plt.subplot(n, 1, 3)
        plt.plot(times, env)
        plt.plot(conj_time, 0 * conj_time)
        plt.axvspan(strategy_time[0], strategy_time[-1],
                    facecolor='g', alpha=0.2, edgecolor='none',
                    zorder=10)
        plt.ylabel('Assumption $i$')
        plt.grid()
        ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # total number of nodes
        ax = plt.subplot(n, 1, 4)
        plt.plot(times, nodes)
        plt.plot(strategy_time, strategy_nodes)
        plt.plot([strategy_time[-1], conj_time[0]],
                 [strategy_nodes[-1], conj_nodes[0]], '--')
        plt.axvspan(strategy_time[0], strategy_time[-1],
                    facecolor='g', alpha=0.2, edgecolor='none',
                    zorder=10)
        plt.plot(conj_time, conj_nodes)
        plt.ylabel('Total BDD Nodes')
        plt.grid()
        ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # nodes for each fixed point set
        ax = plt.subplot(n, 1, 5)
        plt.plot(times, x_nodes, 'b--', label='$X$')
        line, = plt.plot(times, y_nodes, 'g-.', label='$Y$')
        line.set_dashes([8, 4, 2, 4, 2, 4])
        plt.plot(times, z_nodes, 'r-', label='$Z$')
        plt.legend(bbox_to_anchor=(0.3, 1.1),
                   loc='upper center', fontsize=5, ncol=3,
                   handlelength=5)
        plt.ylabel('Fixed points\n(BDD nodes)')
        plt.grid()
        ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # individual strategies
        ax = plt.subplot(n, 1, 6)
        plt.plot(strategy_time, strategy_strategy,
                 'b-', label='$i^{th}$ strategy')
        plt.plot(strategy_time, strategy_cases,
                 'g--', label='cases')
        plt.plot(strategy_time, strategy_new_cases,
                 'r-.', label='new cases')
        plt.ylabel('Individual strategies\n(BDD nodes)')
        plt.grid()
        plt.legend(bbox_to_anchor=(0.5, 1.15),
                   loc='upper center', fontsize=5, ncol=3)
        ax.set_yscale('log')
        # ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # combined strategy
        ax = plt.subplot(n, 1, 7)
        plt.plot(conj_time, conj_strategy, 'o--', label='combined')
        plt.xlabel('time (milliseconds)')
        plt.ylabel('Combined strategy\n(BDD nodes)')
        plt.grid()
        ax.ticklabel_format(style='sci', scilimits=(0, 0))
        # save
        fname = 'details_{i}.pdf'.format(i=i)
        plt.savefig(fname, bbox_inches='tight')
        print('Done ploting {i} masters\n'.format(i=i))
        # accumulate results for ploting vs #masters
        #
        # TODO: fix to use adapted strategy,
        # even if not synthesizing
        aut = logic.compile_spec(code, strict_atomic=True)
        # var numbers
        e = {bit for bit, d in aut.vars.iteritems()
             if d['owner'] == 'env'}
        all_vars.append(len(aut.vars))
        env_vars.append(len(e))
        # strategy size
        strategy_sizes.append(conj_strategy[-1])
        # times
        total_time.append(conj_time[-1])
        realizability_time.append(times[-1])
    all_vars = np.array(all_vars)
    env_vars = np.array(env_vars)
    strategy_sizes = np.array(strategy_sizes)
    total_time = np.array(total_time)
    realizability_time = np.array(realizability_time)
    # plot collected results vs #masters
    masters = np.arange(args.min, args.max + 1)
    plt.clf()
    # numbers of variables
    plt.subplot(4, 1, 1)
    plt.plot(masters, all_vars, 'b-o', label='all')
    plt.plot(masters, all_vars - env_vars, 'g-+', label='sys')
    plt.plot(masters, env_vars, 'r--o', label='env')
    plt.xlabel('Number of masters')  # should it be capitalized ?
    plt.ylabel('Number of variables')
    plt.grid()
    plt.legend()
    # plt.savefig('number_of_variables.pdf', bbox_inches='tight')
    # strategy sizes (and so BDD file memory)
    plt.subplot(4, 1, 2)
    plt.plot(masters, strategy_sizes, 'b--o')
    plt.xlabel('Number of masters')
    plt.ylabel('Strategy size (BDD nodes)')
    plt.grid()
    # times
    plt.subplot(4, 1, 3)
    plt.plot(masters, total_time, '-+', label='total')
    plt.plot(masters, realizability_time, '--o', label='realizability')
    plt.xlabel('Number of masters')
    plt.ylabel('Time (msec)')
    plt.legend()
    plt.grid()
    # time comparison
    ax = plt.subplot(4, 1, 4)
    plt.plot(total_time, realizability_time, 'o')
    plt.xlabel('Total time (msec)')
    plt.ylabel('Realizability time (msec)')
    plt.grid()
    ax.set_aspect('equal')
    plt.savefig('strategy_sizes_and_variable_bumbers.pdf', bbox_inches='tight')
