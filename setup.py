import pip
from setuptools import setup
import sys


description = (
    'Generalized reactive(1) synthesis from Promela specifications.')
README = 'README.md'
VERSION_FILE = 'openpromela/_version.py'
MAJOR = 0
MINOR = 0
MICRO = 1
version = '{major}.{minor}.{micro}'.format(
    major=MAJOR, minor=MINOR, micro=MICRO)
s = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n").format(version=version)
install_requires = [
    'dd >= 0.0.3',
    'humanize >= 0.5.1',
    'natsort >= 3.5.3',
    'networkx >= 1.9.1',
    'omega >= 0.0.1',
    'ply == 3.4',
    'promela >= 0.0.1'
    'psutil >= 2.2.0',
    'subprocess32 >= 3.2.6']


def build_parser_table():
    from openpromela import logic
    tabmodule = logic.TABMODULE.split('.')[-1]
    outputdir = 'openpromela/'
    parser = logic.Parser()
    parser.build(tabmodule, outputdir=outputdir, write_tables=True)


if __name__ == '__main__':
    with open(VERSION_FILE, 'w') as f:
        f.write(s)
    if 'egg_info' not in sys.argv:
        pip.main(['install'] + install_requires)
        build_parser_table()
    setup(
        name='openpromela',
        version=version,
        description=description,
        long_description=open(README).read(),
        author='Ioannis Filippidis',
        author_email='jfilippidis@gmail.com',
        url='https://github.com/johnyf/openpromela',
        license='BSD',
        install_requires=install_requires,
        tests_require=['nose'],
        packages=['openpromela'],
        package_dir={'openpromela': 'openpromela'},
        entry_points={
            'console_scripts':
                ['ospin = openpromela.logic:command_line_wrapper']})
