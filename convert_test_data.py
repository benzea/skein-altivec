#! /usr/bin/env python

import sys

def get_hex(input):
    assert len(input) % 2 == 0
    result = ""
    while len(input):
        result += "\\x"
        result += input[:2]
        input = input[2:]
    return result

for line in sys.stdin.readlines():
    if line.startswith('Len = '):
        length = line[6:-1].strip()
    elif line.startswith('Msg = '):
        msg = line[6:-1].strip()
    elif line.startswith('MD = '):
        md = line[5:-1].strip()

        msg = get_hex(msg)
        md = get_hex(md)
        print "\tTN(%s, \"%s\",\n\t   \"%s\"),\n" % (length, msg, md)