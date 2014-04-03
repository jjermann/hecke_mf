#!/usr/local/bin/sage

from sage.doctest.control import DocTestDefaults, DocTestController
from sys import argv

args=argv
args.pop(0)
args = [ arg for arg in args if not "run_test.py" in arg ]

DD = DocTestDefaults()
DC = DocTestController(DD, args)
DC.run()
