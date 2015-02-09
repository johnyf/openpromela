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


if __name__ == '__main__':
    with open(VERSION_FILE, 'w') as f:
        f.write(s)
    # build parser table
    try:
        from openpromela import logic
        tabmodule = logic.TABMODULE.split('.')[-1]
        outputdir = 'openpromela/'
        parser = logic.Parser()
        parser.build(tabmodule, outputdir=outputdir, write_tables=True)
        plytable_build_failed = False
    except ImportError:
        plytable_build_failed = True
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
            'networkx >= 1.9.1', 'promela', 'tulip >= 1.2.dev'],
        tests_require=['nose'],
        packages=['openpromela'],
        package_dir={'openpromela': 'openpromela'},
        entry_points={
            'console_scripts':
                ['ospin = openpromela.logic:command_line_wrapper']})
    if plytable_build_failed:
        print(
            'ERROR: failed to build parser table.'
            'Please run setup.py again.')
