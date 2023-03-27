
from typing import NamedTuple, List, Tuple, Optional
import subprocess
import csv
import signal
import sys
import re
import os
import time

proven = []
failed = []
sizes = []

filename = "stdlib.csv"

def log(*args, **kwargs):
    print(*args, file=sys.stderr, **kwargs)

def handler(signum, frame):
    print("Proven: ", proven)
    print("Failed: ", failed)
    print("Sizes: ", sizes)
    exit(1)

def crabpi(filename, command, name):
    process = subprocess.run(["cargo", "run", "--release", filename, command, name], capture_output=True)
    return process.stdout

sed_template = "s/__PROOF_SIZE/{}/g; s/__NUM_TERMS/{}/g; s/__CONTEXT_SIZE/{}/g; s/__NUM_LIFTS/{}/g; s/__NUM_INDS/{}/g; s/__NUM_PUB_TERMS/{}/g; s/__NUM_RULES/{}/g; s/__NUM_NNRS/{}/g; s/__NUM_NRS/{}/g; s/__NUM_AXIOMS/{}/g;"
meta_file = "meta.zok"
compile_sizes = [
        (1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        (10, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        (100, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        (1000, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        #(10000, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        #(1, 10, 1, 1, 1, 1, 1, 1, 1, 1),
        #(1, 100, 1, 1, 1, 1, 1, 1, 1, 1),
        #(1, 1000, 1, 1, 1, 1, 1, 1, 1, 1),
        #(1, 10000, 1, 1, 1, 1, 1, 1, 1, 1),
        #(1, 1, 10, 1, 1, 1, 1, 1, 1, 1),
        #(1, 1, 100, 1, 1, 1, 1, 1, 1, 1),
        #(1, 1, 1000, 1, 1, 1, 1, 1, 1, 1),
        #(1, 1, 10000, 1, 1, 1, 1, 1, 1, 1),
        #(1, 1, 1, 10, 1, 1, 1, 1, 1, 1),
        #(1, 1, 1, 100, 1, 1, 1, 1, 1, 1),
        #(1, 1, 1, 1000, 1, 1, 1, 1, 1, 1),
        #(1, 1, 1, 10000, 1, 1, 1, 1, 1, 1),
        #(1, 1, 1, 1, 10, 1, 1, 1, 1, 1),
        #(1, 1, 1, 1, 100, 1, 1, 1, 1, 1),
        #(1, 1, 1, 1, 1000, 1, 1, 1, 1, 1),
        #(1, 1, 1, 1, 10000, 1, 1, 1, 1, 1),
        #(1, 1, 1, 1, 1, 10, 1, 1, 1, 1),
        #(1, 1, 1, 1, 1, 100, 1, 1, 1, 1),
        #(1, 1, 1, 1, 1, 1000, 1, 1, 1, 1),
        #(1, 1, 1, 1, 1, 10000, 1, 1, 1, 1),
        #(1, 1, 1, 1, 1, 1, 10, 1, 1, 1),
        #(1, 1, 1, 1, 1, 1, 100, 1, 1, 1),
        #(1, 1, 1, 1, 1, 1, 1000, 1, 1, 1),
        #(1, 1, 1, 1, 1, 1, 10000, 1, 1, 1),
        #(1, 1, 1, 1, 1, 1, 1, 10, 1, 1),
        #(1, 1, 1, 1, 1, 1, 1, 100, 1, 1),
        #(1, 1, 1, 1, 1, 1, 1, 1000, 1, 1),
        #(1, 1, 1, 1, 1, 1, 1, 10000, 1, 1),
        #(1, 1, 1, 1, 1, 1, 1, 1, 10, 1),
        #(1, 1, 1, 1, 1, 1, 1, 1, 100, 1),
        #(1, 1, 1, 1, 1, 1, 1, 1, 1000, 1),
        #(1, 1, 1, 1, 1, 1, 1, 1, 10000, 1),
        #(1, 1, 1, 1, 1, 1, 1, 1, 1, 10),
        #(1, 1, 1, 1, 1, 1, 1, 1, 1, 100),
        #(1, 1, 1, 1, 1, 1, 1, 1, 1, 1000),
        #(1, 1, 1, 1, 1, 1, 1, 1, 1, 10000),
        #(10, 10, 10, 10, 10, 10, 10, 10, 10, 10),
        #(100, 100, 100, 100, 100, 100, 100, 100, 100, 100),
        #(1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000, 1000),
        #(10000, 10000, 10000, 10000, 10000, 10000, 10000, 10000, 10000, 10000),
    ]

os.chdir("../zok")

library = "stdlib"
lib_out_file = library + ".out"

def set_compile_size(size_tuple):
    proof_size, num_terms, context_size, num_lifts, num_inds, num_pub_terms, num_rules, num_nnrs, num_nrs, num_axs = size_tuple
    sed_full = sed_template.format(proof_size, num_terms, context_size, num_lifts, num_inds, num_pub_terms, num_rules, num_nnrs, num_nrs, num_axs)
    process = subprocess.run(["sed", sed_full, "meta.zok.template"], capture_output=True)
    with open(meta_file, 'w') as meta:
        meta.write(process.stdout.decode("utf-8"))

def compile_local(size_tuple, writer):
    log("Compile local")
    set_compile_size(size_tuple)
    start_time = time.time()
    try:
        process = subprocess.run(["circ", "eval.zok", "r1cs", "--proof-system", "mirage", "--action", "setup"], capture_output=True, timeout=108000)
    except subprocess.TimeoutExpired:
        row = list(size_tuple)
        row.append("timeout")
        log("got timeout")
        writer.writerow(row)
        return
    end_time = time.time()
    if process.returncode == 0:
        row = list(size_tuple)
        row.append(end_time - start_time)
        log("got ", row)
        writer.writerow(row)
    else:
        row = list(size_tuple)
        row.append(-1 * process.returncode)
        writer.writerow(row)

def r1cs_size_local(size_tuple, writer):
    log("r1cs local")
    set_compile_size(size_tuple)
    try:
        process = subprocess.run(["circ", "eval.zok", "r1cs", "--proof-system", "mirage", "--action", "count"], capture_output=True, timeout=108000)
    except subprocess.TimeoutExpired:
        row = list(size_tuple)
        row.append("timeout")
        log("got timeout")
        writer.writerow(row)
        return
    if process.returncode == 0:
        out_string = process.stdout.decode("utf-8")
        r1cs_size_pattern = "Final R1cs size: (\d*)"
        m = re.search(r1cs_size_pattern, out_string)
        row = list(size_tuple)
        row.append(m.group(1))
        log("got ", row)
        writer.writerow(row)
    else:
        row = list(size_tuple)
        row.append(-1 * process.returncode)
        writer.writerow(row)

def sizes():
    with open("../data/proof_sizes_"+library+".csv", mode="w+") as csvfile:
        csv_writer = csv.writer(csvfile)
        run_over_all("count", "../"+library+".csv", csv_writer)

def oneshot(name):
    print(crabpi("stdlib.out", "count", name))

def run_over_all(cmd, filename, writer):
    with open(filename, newline='') as csvfile:
        log("Counting all in", filename)
        reader = csv.reader(csvfile, delimiter=',', quotechar='|')
        for row in list(reader):
            log("Counting: ", row[0])
            try:
                process = subprocess.run(["cargo", "run", "--release", "../"+lib_out_file, cmd, row[0]], capture_output=True, timeout=108000)
            except subprocess.TimeoutExpired:
                row = list(size_tuple)
                row.append("timeout")
                log("got timeout")
                writer.writerow(row.u)
                continue
            if process.returncode == 0:
                writer.writerow([row[0]] + process.stdout.decode("utf-8").strip().split(","))
            else:
                log("error...", process.returncode, process.stderr)
                writer.writerow([row[0],-1*process.returncode])
#print(sys.argv[1])
#if sys.argv[1] == "count":
#    sizes()

if sys.argv[1] == "r1cs":
    with open("../data/r1cs.csv", mode="w+") as csvfile:
        csv_writer = csv.writer(csvfile)
        for sizes in compile_sizes:
            r1cs_size_local(sizes, csv_writer)
elif sys.argv[1] == "count":
    sizes()
elif sys.argv[1] == "compile":
    with open("../data/compile_times.csv", mode="w+") as csvfile:
        csv_writer = csv.writer(csvfile)
        for sizes in compile_sizes:
            compile_local(sizes, csv_writer)


#set_compile_size(3, 4, 3, 4, 3, 4)
#signal.signal(signal.SIGINT, handler)
#oneshot("and.comm")
#
#with open(filename, newline='') as csvfile:
#    log("Counting all in", filename)
#    reader = csv.reader(csvfile, delimiter=',', quotechar='|')
#    for row in list(reader):
#        log("Counting: ", row[0])
#        process = subprocess.run(["cargo", "run", "--release", "stdlib.out", "count", row[0]], capture_output=True)
#        if process.returncode == 0:
#            sizes.append(process.stdout)

    #log("Proving all in", filename)
    #reader = csv.reader(csvfile, delimiter=',', quotechar='|')
    #for row in list(reader):
    #    log("Proving: ", row[0])
    #    process = subprocess.run(["cargo", "run", "--release", "stdlib.out", row[0]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    #    if process.returncode == 0:
    #        proven.append(row[0])

        #print(', '.join(row))
