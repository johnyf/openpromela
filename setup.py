import pip
from setuptools import setup


description = (
    'Generalized reactive(1) synthesis from Promela specifications.')
README = 'README.md'
VERSION_FILE = 'openpromela/version.py'
MAJOR = 0
MINOR = 0
MICRO = 1
version = '{major}.{minor}.{micro}'.format(
    major=MAJOR, minor=MINOR, micro=MICRO)
s = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n").format(version=version)


def build_parser_table():
    from openpromela import logic
    tabmodule = logic.TABMODULE.split('.')[-1]
    outputdir = 'openpromela/'
    parser = logic.Parser()
    parser.build(tabmodule, outputdir=outputdir, write_tables=True)


if __name__ == '__main__':
    pip.main([
        'install',
        '--allow-unverified', 'promela == 0.0.1',
        'https://github.com/johnyf/promela/archive/master.zip',
        '--allow-unverified', 'tulip >= 1.2.dev',
        'https://github.com/johnyf/tulip-control/archive/easysetup.zip',
        'psutil >= 2.2.0'])
    with open(VERSION_FILE, 'w') as f:
        f.write(s)
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
        install_requires=[
            'promela >= 0.0.1',
            'networkx >= 1.9.1',
            'tulip >= 1.2.dev',
            'psutil >= 2.2.0'],
        tests_require=['nose'],
        packages=['openpromela'],
        package_dir={'openpromela': 'openpromela'},
        entry_points={
            'console_scripts':
                ['ospin = openpromela.logic:command_line_wrapper']})
