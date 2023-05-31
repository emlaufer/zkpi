#!/usr/bin/env python3

import argparse
import subprocess
import sys

parser = argparse.ArgumentParser(
            prog='zkPiDriver',
            description='Run one-shot proofs from zkpi in a single command')
parser.add_argument('-l', '--lean_file')
parser.add_argument('-e', '--export_file')
parser.add_argument('theorem_name')
args = parser.parse_args()

if args.lean_file is None and args.export_file is None:
    print("You must specify either a lean source file, or a file in the lean export format (by running `lean --export`)!")
    parser.print_usage()
    exit(1)

if args.lean_file is not None:
    # check lean version
    p = subprocess.run("lean --version", capture_output=True)
    print(p.stdout.decode())
    # run lean exporter on the file
    #subprocess.run("
