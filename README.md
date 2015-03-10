[![Build Status][build_img]][travis]
[![Coverage Status][coverage]][coveralls]

About
=====

A synthesizer from open Promela specifications. It:

- translates open Promela to linear temporal logic
- encodes bounded linear arithmetic in bitvector logic
- calls the `slugs` synthesizer to check if the resulting formula is realizable and construct a transducer realizing a winning strategy
- return the winning strategy as a Mealy machine


Installation
============

You can install from PyPI using `pip`:

```
pip install openpromela
```

or locally using `setuptools`:

```
python setup.py install
```


License
=======
[BSD-3](http://opensource.org/licenses/BSD-3-Clause), see `LICENSE` file.

[build_img]: https://travis-ci.org/johnyf/openpromela.svg?branch=travis
[travis]: https://travis-ci.org/johnyf/openpromela
[coverage]: https://coveralls.io/repos/johnyf/openpromela/badge.svg?branch=travis
[coveralls]: https://coveralls.io/r/johnyf/openpromela?branch=travis