from setuptools import setup
# inline:
# from openpromela import logic


description = (
    'Generalized reactive(1) synthesis from Promela specifications.')
README = 'README.md'
VERSION_FILE = 'openpromela/_version.py'
MAJOR = 0
MINOR = 0
MICRO = 2
version = '{major}.{minor}.{micro}'.format(
    major=MAJOR, minor=MINOR, micro=MICRO)
s = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n").format(version=version)
install_requires = [
    'dd >= 0.1.3',
    'gitpython >= 1.0.1',
    'humanize >= 0.5.1',
    'natsort >= 3.5.3',
    'networkx >= 1.9.1',
    'omega >= 0.0.3',
    'ply >= 3.4',
    'promela >= 0.0.1',
    'psutil >= 3.1.1',
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
    try:
        build_parser_table()
    except ImportError:
        print('WARNING: `openpromela` could not cache parser tables '
              '(ignore this if running only for "egg_info").')
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
