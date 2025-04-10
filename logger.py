#!/usr/bin/env python3

"""Logging function using decorators
Usage: decorate monitored function with '@logger'"""


def logger(f):
    def wrapped(*args, **kwargs):
        print('start', f)
        res = f(*args, **kwargs)
        print('end', f)
        return res

    return wrapped
