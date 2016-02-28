[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]


About
=====

A synthesizer from open Promela specifications. It:

- translates open Promela to linear temporal logic (LTL)
- compiles the LTL formula to an implementation using the GR(1) game solver [`omega.games.gr1`](https://github.com/johnyf/omega/blob/master/omega/games/gr1.py)
- dumps a transition relation that implements the open Promela specification.

The language and implementation are documented in:

Filippidis I., Murray R.M., Holzmann G.J.<br>
  [A multi-paradigm language for reactive synthesis](http://dx.doi.org/10.4204/EPTCS.202.6)<br>
  4th Workshop on Synthesis (SYNT) 2015<br>
  Electronic Proceedings in Theoretical Computer Science (EPTCS)<br>
  vol.202, pp.73-97, 2016

Filippidis I., Murray R.M., Holzmann G.J.<br>
  [Synthesis from multi-paradigm specifications](http://resolver.caltech.edu/CaltechCDSTR:2015.003)<br>
  California Institute of Technology, Pasadena, CA, 2015<br>
  CDSTR:2015.003


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

Pure Python dependencies suffice, unless you have a demanding problem.
In that case, build `dd.cudd` to interface to CUDD.


License
=======
[BSD-3](http://opensource.org/licenses/BSD-3-Clause), see `LICENSE` file.


[build_img]: https://travis-ci.org/johnyf/openpromela.svg?branch=master
[travis]: https://travis-ci.org/johnyf/openpromela
[coverage]: https://coveralls.io/repos/johnyf/openpromela/badge.svg?branch=master
[coveralls]: https://coveralls.io/r/johnyf/openpromela?branch=master