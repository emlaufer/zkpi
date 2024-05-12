#!/usr/bin/env python3

import argparse
import subprocess
import sys
import os
import time
import re
import csv
from timeit import Timer

parser = argparse.ArgumentParser(
            prog='zkPiDriver',
            description='Run one-shot proofs from zkpi in a single command')
parser.add_argument('--circ-exe', default='circ')
args = parser.parse_args()
circ_exe = os.path.abspath(args.circ_exe)

keys = ["PROOF_SIZE","NUM_TERMS","CONTEXT_SIZE","NUM_LIFTS","NUM_INDS","NUM_RULES","NUM_NNRS","NUM_NRS","NUM_AXIOMS"]

outfile = open(f"param_sweep.csv", "w+")
writer = csv.writer(outfile)
writer.writerow(keys + ["constraints"])

os.chdir("../zok")
for (i, key) in enumerate(keys):
    for p in range(1, 4):
        sizes = [1] * len(keys)
        sizes[i] = 10 ** p

        meta_file = open("meta.zok", "w+")
        meta_file_template = open("meta.zok.template", "r")
        template = meta_file_template.read()
        template = template.replace("__PROOF_SIZE", str(sizes[0]))
        template = template.replace("__NUM_TERMS", str(sizes[1]))
        template = template.replace("__CONTEXT_SIZE", str(sizes[2]))
        template = template.replace("__NUM_LIFTS", str(sizes[3]))
        template = template.replace("__NUM_INDS", str(sizes[4]))
        template = template.replace("__NUM_PUB_TERMS", str(1))
        template = template.replace("__NUM_RULES", str(sizes[5]))
        template = template.replace("__NUM_NNRS", str(sizes[6]))
        template = template.replace("__NUM_NRS", str(sizes[7]))
        template = template.replace("__NUM_AXIOMS", str(sizes[8]))
        meta_file.write(template)
        
        meta_file_template.close()
        meta_file.close()
     
        p = subprocess.run(["../circ/target/release/examples/circ", '--language', 'Zsharp', 'eval.zok', 'r1cs', '--proof-system', 'mirage', '--action', 'count'], stdout=subprocess.PIPE)
        outstr = p.stdout
        reg = re.search(b"Final R1cs size: (\\d*)", outstr)
        constraints = int(reg.group(1).decode("utf-8"))
        sizes.append(constraints)
        print(sizes)
        writer.writerow(sizes)
        outfile.flush()

#sizes = p.stdout.decode().split(',')
#
## write sizes to meta file
#meta_file = open("{}/meta.zok".format(args.circuit_directory), "w+")
#meta_file_template = open("{}/meta.zok.template".format(args.circuit_directory), "r")
#template = meta_file_template.read()
#template = template.replace("__PROOF_SIZE", sizes[0])
#template = template.replace("__NUM_TERMS", sizes[1])
#template = template.replace("__CONTEXT_SIZE", sizes[2])
#template = template.replace("__NUM_LIFTS", sizes[3])
#template = template.replace("__NUM_INDS", sizes[4])
#template = template.replace("__NUM_PUB_TERMS", sizes[5])
#template = template.replace("__NUM_RULES", sizes[6])
#template = template.replace("__NUM_NNRS", sizes[7])
#template = template.replace("__NUM_NRS", sizes[8])
#template = template.replace("__NUM_AXIOMS", sizes[9])
#meta_file.write(template)
#
#meta_file_template.close()
#meta_file.close()
#
## write pin file
#pin_file = "{}/{}.pin".format(args.circuit_directory, args.theorem_name)
#input_file = open(pin_file, "w+");
#start = time.time_ns()
#p = subprocess.run(["cargo", "run", "--release", export_file, "export", args.theorem_name], capture_output=True)
#if p.returncode != 0:
#    print('Failed to convert theorem {}...'.format(args.theorem_name))
#    exit(1)
#duration = time.time_ns() - start
#if args.time is not None:
#    print(f"Simplify/Export time: {duration}")
#
#input_file.write(p.stdout.decode())
#input_file.close()
#
## cleanup
#if not args.no_cleanup and args.lean_file is not None:
#    os.remove(export_file)
#
#
## oneshot proof
#print('Running oneshot zkpi proof')
#
#circ_exe = os.path.abspath(args.circ_exe)
#os.chdir(args.circuit_directory)
#p = subprocess.Popen([circ_exe, '--language', 'Zsharp', 'eval.zok', 'r1cs', '--proof-system', 'mirage', '--action', 'oneshot', '--inputs', "{}.pin".format(args.theorem_name)], stdout=subprocess.PIPE)
#while p.poll() is None:
#    l = p.stdout.readline()
#    print(l)
#print(p.stdout.decode("utf-8"))
#
## cleanup
#if not args.no_cleanup:
#    os.remove("{}.pin".format(args.theorem_name))
#
#
