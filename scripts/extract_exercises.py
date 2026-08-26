#!/usr/bin/env python3
# Authors: Niklas Halonen (xhalo32)
# NOTE: This is fully human-written code (unlike many other scripts in this directory)
# Usage: python scripts/extract_exercises.py <FILE>
import re, sys

def extract_exercises(text):
    extracts = []
    offset = 0
    while True:
        m = re.search(r'^(::::*)exercise.*$', text[offset:], re.MULTILINE)
        if m == None:
            return extracts
        depth = len(m.group(1))
        start = (m.start(), m.end())
        m = re.search(rf'^:{{{depth}}}$', text[offset + start[1]:], re.MULTILINE)
        if m is None:
            print("Error: could not find closing fence")
            break
        end = (m.start(), m.end())
        extract = {
            "outer": text[offset + start[0]:offset + start[1] + end[1]],
            "inner": text[offset + start[1]:offset + start[1] + end[0]],
        }
        extracts.append(extract)
        offset = offset + start[1] + end[1]
    return extracts

if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        extracts = extract_exercises(f.read())
        for extract in extracts:
            print(extract["outer"])