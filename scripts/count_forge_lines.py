#!/usr/bin/python3
import collections
import itertools
import argparse

TESTS = [
    (lambda l: l.startswith('open'), 'Import'),
    (lambda l: l.startswith('//') or l.startswith('--'), 'Comment'),
    (lambda l: len(l) == 0, 'Empty'),
    (lambda l: l.startswith('#'), 'Other')
]

mkdict = lambda: collections.defaultdict(lambda: 0)

def main(args):

    total = mkdict()

    filenames = args.FILE

    def print_result(d):
        for t in itertools.chain(['Code'], map(lambda v: v[1], TESTS), ['Total']):
            print(f"  {t:8} {d[t]:>6}")

    for filename in filenames:
        d = mkdict()
        print(f"{filename}")
        with open(filename, 'r') as file:
            for line in file.readlines():
                line = line.lstrip()
                cls = None
                for (t, v) in TESTS:
                    if t(line):
                        cls = v
                        break
                else:
                    cls = 'Code'
                for tracker in [d, total]:
                    tracker[cls] += 1
                    tracker['Total'] += 1
            print_result(d)

    if len(filenames) > 1:
        print("All Files")
        print_result(total)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Count the number lines of a forge file by category")
    parser.add_argument("FILE", nargs='+', help="A file to include")
    main(parser.parse_args())