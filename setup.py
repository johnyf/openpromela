from setuptools import setup
# inline:
# from openpromela import logic
# import git


description = (
    'Generalized reactive(1) synthesis from Promela specifications.')
README = 'README.md'
VERSION_FILE = 'openpromela/_version.py'
MAJOR = 0
MINOR = 1
MICRO = 0
VERSION = '{major}.{minor}.{micro}'.format(
    major=MAJOR, minor=MINOR, micro=MICRO)
VERSION_TEXT = (
    '# This file was generated from setup.py\n'
    "version = '{version}'\n")
install_requires = [
    'dd >= 0.3.0',
    'networkx >= 1.9.1',
    'omega >= 0.0.7',
    'ply >= 3.4',
    'promela >= 0.0.1']


def git_version(version):
    import git
    repo = git.Repo('.git')
    repo.git.status()
    sha = repo.head.commit.hexsha
    if repo.is_dirty():
        return '{v}.dev0+{sha}.dirty'.format(
            v=version, sha=sha)
    # commit is clean
    # is it release of `version` ?
    try:
        tag = repo.git.describe(
            match='v[0-9]*', exact_match=True,
            tags=True, dirty=True)
    except git.GitCommandError:
        return '{v}.dev0+{sha}'.format(
            v=version, sha=sha)
    assert tag[1:] == version, (tag, version)
    return version


def build_parser_table():
    from openpromela import logic
    tabmodule = logic.TABMODULE.split('.')[-1]
    outputdir = 'openpromela/'
    parser = logic.Parser()
    parser.build(tabmodule, outputdir=outputdir, write_tables=True)


if __name__ == '__main__':
    # version
    try:
        version = git_version(VERSION)
    except:
        print('No git info: Assume release.')
        version = VERSION
    s = VERSION_TEXT.format(version=version)
    with open(VERSION_FILE, 'w') as f:
        f.write(s)
    # build parsers
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
