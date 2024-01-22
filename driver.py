#!/usr/bin/env python3

import argparse
import subprocess
import sys
import os
import time
from timeit import Timer

parser = argparse.ArgumentParser(
            prog='zkPiDriver',
            description='Run one-shot proofs from zkpi in a single command')
parser.add_argument('-l', '--lean-file')
parser.add_argument('-e', '--export-file')
parser.add_argument('-n', '--no-cleanup', action=argparse.BooleanOptionalAction)
parser.add_argument('--lean_cmd', default='lean')
parser.add_argument('-c', '--circuit-directory', default='zok')
parser.add_argument('--circ-exe', default='circ')
parser.add_argument('--time', action=argparse.BooleanOptionalAction)
parser.add_argument('theorem_name')
args = parser.parse_args()

if args.lean_file is None and args.export_file is None:
    print('You must specify either a lean source file, or a file in the lean export format (by running `lean --export`)!')
    parser.print_usage()
    exit(1)

export_file = args.export_file

if args.lean_file is not None:
    # check lean version
    p = subprocess.run([args.lean_cmd, '--version'], capture_output=True)
    
    if not 'version 3.' in p.stdout.decode().lower():
        print('The tool only works for Lean3. Please specify either a lean cmd or elan cmd with appropriate version!')
        parser.print_usage()
        exit(1)

    print("Exporting from {}...".format(args.lean_file))
    lean_filename_no_ext = args.lean_file.removesuffix(".lean").removesuffix(".lean3")
    export_file = "{}.out".format(lean_filename_no_ext)
    # run lean exporter on the file
    cmd = [args.lean_cmd, "--export={}".format(export_file), args.lean_file]
    p = subprocess.run(cmd, stdout=subprocess.DEVNULL)
    if p.returncode != 0:
        print('Lean failed to export the file...')
        print('You may run the same command to debug:')
        print(' '.join(cmd))
        exit(1)
        

print("Running zkpi converter on theorem {}...".format(args.theorem_name))
# run zkpi on the file
p = subprocess.run(["cargo", "run", "--release", export_file, "count", args.theorem_name], capture_output=True)
if p.returncode != 0:
    print('Failed to convert theorem {}...'.format(args.theorem_name))
    print("output: ", p.stderr.decode("utf-8"))
    exit(p.returncode)

sizes = p.stdout.decode().split(',')

# write sizes to meta file
meta_file = open("{}/meta.zok".format(args.circuit_directory), "w+")
meta_file_template = open("{}/meta.zok.template".format(args.circuit_directory), "r")
template = meta_file_template.read()
template = template.replace("__PROOF_SIZE", sizes[0])
template = template.replace("__NUM_TERMS", sizes[1])
template = template.replace("__CONTEXT_SIZE", sizes[2])
template = template.replace("__NUM_LIFTS", sizes[3])
template = template.replace("__NUM_INDS", sizes[4])
template = template.replace("__NUM_PUB_TERMS", sizes[5])
template = template.replace("__NUM_RULES", sizes[6])
template = template.replace("__NUM_NNRS", sizes[7])
template = template.replace("__NUM_NRS", sizes[8])
template = template.replace("__NUM_AXIOMS", sizes[9])
meta_file.write(template)

meta_file_template.close()
meta_file.close()

# write pin file
pin_file = "{}/{}.pin".format(args.circuit_directory, args.theorem_name)
input_file = open(pin_file, "w+");
start = time.time_ns()
p = subprocess.run(["cargo", "run", "--release", export_file, "export", args.theorem_name], capture_output=True)
if p.returncode != 0:
    print('Failed to convert theorem {}...'.format(args.theorem_name))
    exit(1)
duration = time.time_ns() - start
if args.time is not None:
    print(f"Simplify/Export time: {duration}")

input_file.write(p.stdout.decode())
input_file.close()

# cleanup
if not args.no_cleanup and args.lean_file is not None:
    os.remove(export_file)


# oneshot proof
print('Running oneshot zkpi proof')

circ_exe = os.path.abspath(args.circ_exe)
os.chdir(args.circuit_directory)
p = subprocess.Popen([circ_exe, '--language', 'Zsharp', 'eval.zok', 'r1cs', '--proof-system', 'mirage', '--action', 'oneshot', '--inputs', "{}.pin".format(args.theorem_name)], stdout=subprocess.PIPE)
while p.poll() is None:
    l = p.stdout.readline()
    print(l)
print(p.stdout.decode("utf-8"))

# cleanup
if not args.no_cleanup:
    os.remove("{}.pin".format(args.theorem_name))

