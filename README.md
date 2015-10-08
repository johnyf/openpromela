[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]


About
=====

A synthesizer from open Promela specifications. It:

- translates open Promela to linear temporal logic
- calls the `slugs` synthesizer to check if the resulting formula is realizable and construct a transducer realizing a winning strategy
- return the winning strategy as a Mealy machine

The language and implementation are documented in:

Filippidis I., Murray R.M., Holzmann G.J.;
A multi-paradigm language for reactive synthesis, 4th Workshop on Synthesis (SYNT'15), Electronic Proceedings in Theoretical Computer Science (EPTCS), San Francisco, CA, USA, July 2015

Filippidis I., Murray R.M., Holzmann G.J.;
[Synthesis from multi-paradigm specifications](http://resolver.caltech.edu/CaltechCDSTR:2015.003), California Institute of Technology, Pasadena, CA, 2015 (CDSTR:2015.003)


Usage
=====

The package can be used both as a library and from the command line. A script named `ospin` is created as entry point. It is placed where `setuptools` installs new executables, e.g., whre `python` itself resides. To learn how to use the script, invoke it with:

```
ospin --help
```


Installation
============

Use `pip` for `openpromela` itself:

```
pip install openpromela
```

The only non-Python dependency is the synthesizer [`slugs`](https://github.com/LTLMoP/slugs). It can be installed by either running `install_slugs.sh`, or following its installation instructions.


License
=======
[BSD-3](http://opensource.org/licenses/BSD-3-Clause), see `LICENSE` file.


[build_img]: https://travis-ci.org/johnyf/openpromela.svg?branch=master
[travis]: https://travis-ci.org/johnyf/openpromela
[coverage]: https://coveralls.io/repos/johnyf/openpromela/badge.svg?branch=master
[coveralls]: https://coveralls.io/r/johnyf/openpromela?branch=master