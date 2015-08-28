#!/usr/bin/env python
"""Run AMBA AHB case study for increasing number of masters.

Process logs and plot results.
"""
import argparse
import datetime
import importlib
from itertools import cycle
import json
import logging
import re
import shutil
import subprocess
import time
import git
import matplotlib as mpl
# matplotlib.use('Agg')
from matplotlib import pyplot as plt
import numpy as np
from openpromela import logic
import psutil


logger = logging.getLogger(__name__)
DEBUG = False  # for this script only
if DEBUG:
    sh = logging.StreamHandler()
    logger.addHandler(sh)
    logger.setLevel(logging.DEBUG)
mpl.rc('xtick', labelsize=7)
mpl.rc('ytick', labelsize=7)
mpl.rc('font', size=7)
col_gen = cycle('bgrcmk')
JSON_FILE = 'details.json'
INPUT_FILE = 'amba.pml'
CONFIG_FILE = 'config.json'
N = 2
M = 17


def git_version(path):
    """Return SHA-dirty for repo under `path`."""
    repo = git.Repo(path)
    sha = repo.head.commit.hexsha
    dirty = repo.is_dirty()
    return sha + ('-dirty' if dirty else '')


def snapshot_versions():
    """Log versions of software used."""
    # existing log ?
    try:
        with open(CONFIG_FILE, 'r') as f:
            d_old = json.load(f)
    except IOError:
        d_old = None
    # get SHA
    paths = [
        '~/github/openpromela',
        '~/github/omega']
    d = dict()
    for path in paths:
        sha = git_version(path)
        d[path] = sha
    # slugs binary version
    cmd = ['slugs', '--version']
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE)
    p.wait()
    if p.returncode != 0:
        print p.returncode
        raise Exception('`slugs` not found on path')
    slugs_version = p.stdout.read().strip()
    d['slugs'] = slugs_version
    # versions of python packages
    packages = ['dd', 'omega', 'promela', 'openpromela']
    for s in packages:
        pkg = importlib.import_module(s)
        d[s] = pkg.__version__
    t_now = time.strftime('%Y-%b-%d-%A-%T-%Z')
    d['time'] = t_now
    # check versions
    compare = list(packages)
    compare.append('slugs')
    if d_old is not None:
        for k in compare:
            assert d[k] == d_old[k]
    # dump
    with open(CONFIG_FILE, 'w') as f:
        json.dump(d, f, indent=4)
    return d


def run(args):
    n = args.min
    m = args.max + 1
    # config logging
    level = args.debug
    loggers = ['openpromela.slugs']
    for logname in loggers:
        log = logging.getLogger(logname)
        log.setLevel(level)
    # capture execution environment
    snapshot_versions()
    # run
    psutil_file = 'psutil.txt'
    details_file = 'details.txt'
    for i in xrange(n, m):
        print('starting {i} masters...'.format(i=i))
        bdd_file = 'bdd_{i}_masters.txt'.format(i=i)
        # log
        h_psutil = add_logfile(psutil_file, 'openpromela.slugs')
        # run
        t0 = time.time()
        code = generate_code(i)
        r = logic.synthesize(code, symbolic=True, filename=bdd_file)
        t1 = time.time()
        dt = datetime.timedelta(seconds=t1 - t0)
        # close log files
        close_logfile(h_psutil, 'openpromela.slugs')
        assert r is not None, 'NOT REALISABLE !!!'
        print('Done with {i} masters in {dt}.'.format(i=i, dt=dt))
        # copy log file
        i_psutil_file = 'log_{i}_masters.txt'.format(i=i)
        i_details_file = 'details_{i}_masters.txt'.format(i=i)
        shutil.copy(psutil_file, i_psutil_file)
        shutil.copy(details_file, i_details_file)


def add_logfile(fname, logger_name):
    h = logging.FileHandler(fname, mode='w')
    log = logging.getLogger(logger_name)
    log.addHandler(h)
    return h


def close_logfile(h, logger_name):
    log = logging.getLogger(logger_name)
    log.removeHandler(h)
    h.close()


def generate_code(i):
    # check if other users
    users = psutil.users()
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
    code += form_progress(i)
    return code


def form_progress(i):
    """Return conjunction of LTL formulae for progress."""
    prog = ' && '.join(
        '[]<>(request[{k}] -> (master == {k}))'.format(k=k)
        for k in xrange(i))
    return 'assert ltl { ' + prog + ' }'


def plot_all_experiments(args):
    """Dump a plot for each experiment, plus summary."""
    n = args.min
    m = args.max + 1
    # capture execution environment
    # TODO: check snapshot versions
    # run
    all_vars = list()
    env_vars = list()
    peak_total_nodes = list()
    strategy_sizes = list()
    total_time = list()
    realizability_time = list()
    reordering_time = list()
    for i in xrange(n, m):
        details_file = 'details_{i}_masters.txt'.format(i=i)
        code = generate_code(i)
        w = plot_single_experiment(code, details_file, i)
        all_vars.append(w[0])
        env_vars.append(w[1])
        # strategy size
        peak_total_nodes.append(w[2])
        strategy_sizes.append(w[3])
        # times
        total_time.append(w[4])
        realizability_time.append(w[5])
        reordering_time.append(w[6])
    # dump as JSON
    data = dict(
        all_vars=all_vars,
        env_vars=env_vars,
        peak_total_nodes=peak_total_nodes,
        strategy_sizes=strategy_sizes,
        total_time=total_time,
        realizability_time=realizability_time,
        reordering_time=reordering_time)
    with open(JSON_FILE, 'w') as f:
        json.dump(data, f)
    plot_overall_summary(data, args.min, args.max)


def plot_single_experiment(code, details_file, i):
    """Parse and plot the details."""
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
             'g--', label='covered states')
    plt.plot(strategy_time, strategy_new_cases,
             'r-.', label='new states')
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
    from omega.logic import bitvector as bv
    from omega.symbolic import symbolic
    bitblasted_aut = symbolic._bitblast(aut)
    dbits = bv.list_bits(bitblasted_aut.vars)
    all_vars = len(dbits)
    e = {bit for bit, d in dbits.iteritems()
         if d['owner'] == 'env'}
    env_vars = len(e)
    # strategy size
    peak_total_nodes = conj_nodes[-1]
    strategy_sizes = conj_strategy[-1]
    # times
    total_time = conj_time[-1]
    realizability_time = times[-1]
    reordering_time = conj_reorder[-1]
    r = (
        all_vars, env_vars, peak_total_nodes,
        strategy_sizes, total_time, realizability_time,
        reordering_time)
    return r


def plot_overall_summary(data, n_min, n_max):
    """Plot results over number of masters."""
    all_vars = data['all_vars']
    env_vars = data['env_vars']
    peak_total_nodes = data['peak_total_nodes']
    strategy_sizes = data['strategy_sizes']
    total_time = data['total_time']
    realizability_time = data['realizability_time']
    reordering_time = data['reordering_time']
    # convert to numpy arrays
    all_vars = np.array(all_vars)
    env_vars = np.array(env_vars)
    peak_total_nodes = np.array(peak_total_nodes)
    strategy_sizes = np.array(strategy_sizes)
    total_time = np.array(total_time)
    realizability_time = np.array(realizability_time)
    reordering_time = np.array(reordering_time)
    # plot collected results vs #masters
    masters = np.arange(n_min, n_max + 1)
    plt.clf()
    # numbers of variables
    plt.subplot(4, 1, 1)
    plt.plot(masters, all_vars, 'b-o', label='all')
    plt.plot(masters, all_vars - env_vars, 'g-+', label='sys')
    plt.plot(masters, env_vars, 'r--o', label='env')
    plt.xlabel('Number of masters')  # should it be capitalized ?
    plt.ylabel('Number of variables')
    plt.grid()
    plt.legend(loc='upper left')
    # plt.savefig('number_of_variables.pdf', bbox_inches='tight')
    # strategy sizes (and so BDD file memory)
    ax = plt.subplot(4, 1, 2)
    plt.plot(masters, peak_total_nodes, 'r-+', label='Max total nodes')
    plt.plot(masters, strategy_sizes, 'b--o', label='Strategy size')
    plt.xlabel('Number of masters')
    plt.ylabel('BDD nodes')
    ax.set_yscale('log')
    plt.grid()
    plt.legend(loc='upper left')
    # times
    ax = plt.subplot(4, 1, 3)
    plt.plot(masters, total_time, '-+', label='total')
    plt.plot(masters, realizability_time, '--o', label='realizability')
    plt.plot(masters, reordering_time, '-*', label='reordering')
    plt.xlabel('Number of masters')
    plt.ylabel('Time (msec)')
    ax.ticklabel_format(style='sci', axis='y', scilimits=(0, 0))
    plt.legend(loc='upper left')
    plt.grid()
    # time comparison
    ax = plt.subplot(4, 1, 4)
    plt.plot(total_time, total_time, '--k')
    plt.plot(total_time, realizability_time, 'o', label='realizability')
    plt.plot(total_time, reordering_time, '*', label='reordering')
    plt.xlabel('Total time (msec)')
    plt.ylabel('Constituent times (msec)')
    ax.set_aspect('equal')
    ax.set_xscale('log')
    ax.set_yscale('log')
    plt.grid()
    plt.legend(loc='center left', bbox_to_anchor=(1, 0.5))
    plt.savefig('strategy_sizes_and_variable_numbers.pdf',
                bbox_inches='tight')


def parse_logs(n, m):
    """Plot time and memory for repeated experiments over range."""
    masters = range(n, m + 1)
    fontsize = 15
    # parse logs
    all_data = dict()
    for i in masters:
        print('parsing master {i}'.format(i=i))
        all_data[i] = parse_log(i)
    # dump JSON file
    fname = 'times.json'
    with open(fname, 'w') as f:
        json.dump(all_data, f)
    # time vs memory per #masters
    plt.figure(0)
    plt.hold('on')
    for i in masters:
        print('ploting master {i}'.format(i=i))
        d = all_data[i]
        for t, rss in zip(d['time'], d['rss']):
            color = col_gen.next()
            plt.plot(t, rss, color=color)
            total_time = t[-1]
            mem = rss[-1]
            plt.plot(total_time, mem, marker='o', color=color)
            plt.text(total_time, mem, str(i))
    ax = plt.gca()
    ax.set_xscale('log')
    ax.set_yscale('log')
    plt.xlabel('time (sec)', fontsize=fontsize)
    plt.ylabel('memory (MB)', fontsize=fontsize)
    plt.grid()
    fname = 'memory.pdf'
    plt.savefig(fname)
    # (time, memory) vs #masters
    plt.figure(1)
    data = dict(time=list(), memory=list())
    num_of_samples = list()
    for i in masters:
        d = all_data[i]
        t = [max(c) for c in d['time']]
        m = [max(c) for c in d['rss']]
        data['time'].append(t)
        data['memory'].append(m)
        num_of_samples.append(len(d['time']))
    x = masters
    plt.subplot(3, 1, 1)
    plt.boxplot(data['time'], positions=x, manage_xticks=False)
    mean_time = [np.mean(a) for a in data['time']]
    plt.plot(x, mean_time, '--b')
    ax = plt.gca()
    ax.tick_params(labelsize=fontsize)
    ax.set_yscale('log')
    plt.ylabel('Total time (sec)', fontsize=fontsize)
    plt.grid()
    plt.subplot(3, 1, 2)
    plt.boxplot(data['memory'], positions=x, manage_xticks=False)
    ax = plt.gca()
    ax.tick_params(labelsize=fontsize)
    ax.set_yscale('log')
    plt.ylabel('Max RSS\nmemory (MB)', fontsize=fontsize)
    plt.grid()
    plt.subplot(3, 1, 3)
    plt.plot(x, num_of_samples, '--o')
    ax = plt.gca()
    ax.tick_params(labelsize=fontsize)
    ya = ax.get_yaxis()
    ya.set_major_locator(plt.MaxNLocator(integer=True))
    plt.xlabel('Number of masters', fontsize=fontsize)
    plt.ylabel('Number of\nsamples', fontsize=fontsize)
    plt.grid()
    if abs(M - N) > 16:
        ticks = [i for i in x if (i % 4 == 0)]
        plt.xticks(ticks)
    # save file
    fname = 'time.pdf'
    plt.savefig(fname, bbox_inches='tight')


def parse_log(i):
    fname = './log_{i}_masters.txt'.format(i=i)
    with open(fname, 'r') as f:
        s = f.read()
    data = dict(time=list(), rss=list(), vms=list())
    for line in s.splitlines():
        if 'call slugs' in line:
            times = list()
            rss_memory = list()
            vms_memory = list()
        elif 'slugs returned' in line:
            data['time'].append(times)
            data['rss'].append(rss_memory)
            data['vms'].append(vms_memory)
        elif 'time:' in line:
            (t,) = re.findall('time:\s([\d\.:]+)', line)
            c = re.findall('rss:\s([\d.]+)\s([kMG])B', line)
            if c:
                ((rss, size),) = c
            else:
                (rss,) = re.findall('rss:\s([\d.]+)\sBytes', line)
            (vms,) = re.findall('vms:\s([\d]+)', line)
            if '.' in t:
                x = time.strptime(t, '%H:%M:%S.%f')
            else:
                x = time.strptime(t, '%H:%M:%S')
            sec = datetime.timedelta(
                hours=x.tm_hour, minutes=x.tm_min,
                seconds=x.tm_sec).total_seconds()
            rss = float(rss)
            if size == 'k':
                rss = 10**-3 * rss
            elif size == 'G':
                rss = 10**3 * rss
            vms = float(vms)
            if rss < 0.1:
                print('warning: read ~0 rss, discarding')
                continue
            times.append(sec)
            rss_memory.append(rss)
            vms_memory.append(vms)
        else:
            print('ignored line')
    return data


def main():
    # args
    p = argparse.ArgumentParser()
    p.add_argument('--min', default=N, type=int,
                   help='from this # of masters')
    p.add_argument('--max', default=M, type=int,
                   help='to this # of masters')
    p.add_argument('--debug', type=int, default=logging.ERROR,
                   help='python logging level')
    p.add_argument('--run', default=False, action='store_true',
                   help='synthesize')
    p.add_argument('--repeat', default=1, type=int,
                   help='multiple runs from min to max')
    p.add_argument('--solver', default='slugs', type=str,
                   choices=['slugs'])
    p.add_argument('--plot', action='store_true',
                   help='generate plots')
    p.add_argument('--plot-stats', action='store_true',
                   help='plot time and memory for logged repeated runs')
    args = p.parse_args()
    if args.plot_stats:
        parse_logs(args.min, args.max)
    # multiple runs should be w/o plots
    assert args.repeat == 1 or not args.plot
    # multiple runs
    if args.run:
        for i in xrange(args.repeat):
            print('run: {i}'.format(i=i))
            if args.solver == 'slugs':
                run(args)
            else:
                raise Exception(
                    'unknown solver: {s}'.format(s=args.solver))
    # plot
    if args.plot:
        plot_all_experiments(args)


if __name__ == '__main__':
    main()
