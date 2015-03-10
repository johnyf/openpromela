"""Synthesizer of Mealy transducers from open Promela."""
from .logic import synthesize
try:
    from .version import version as __version__
except:
    __version__ = None
