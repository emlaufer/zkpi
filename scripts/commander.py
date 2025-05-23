
from typing import NamedTuple, List, Tuple, Optional

from concurrent.futures import ThreadPoolExecutor

import os
import sys
import shutil as sh
import subprocess as sub
import argparse
import tempfile
import threading
import queue
import time
import traceback
import re
import csv
import pandas as pd

# CHANGE STRING TO DO EITHER MATHLIB OR STDLIB
username = "evan"
library = "mathlib"

class Binary(object):
    path: str

    def __init__(self, name: str):
        if os.access(name, os.EX_OK):
            self.path = os.path.abspath(name)
        elif sh.which(name) is not None:
            self.path = sh.which(name)
        else:
            assert False, f"Could not find executable {name}"


ssh = Binary("ssh")
scp = Binary("scp")

def check_ssh(ip: str):
    print("check ssh to " + ip)
    out = sub.run(
        ["gcloud", "compute", "ssh", "--zone","us-west1-b","--project", "gcp-zkpi", ip], stderr=sub.PIPE, stdout=sub.PIPE, input=""
    )
    assert (
        out.returncode == 0
    ), f"Could not run 'ls' on '{ip}'. Got STDOUT\n{out.stdout.decode()}\nSTDERR\n{out.stderr.decode()}"

class Machine(object):
    name: str

    def __init__(self, name: str):
        #check_ssh(name)
        self.name = name
        #self.disable_threading()

    def str(self):
        return f"{self.name}"

def hosts_from_file(path: str) -> List[Machine]:
    out = []
    with open(path) as f:
        for line in f.read().strip().splitlines(keepends=False):
            out.append(Machine(line))
    return out

def search_or_default(search, outstr, default):
    if search is None:
        return default
    if outstr is None:
        return default

    reg = re.search(search, outstr)
    if reg is not None:
        return reg.group(1).decode("utf-8")
    else:
        return str(default)


parser = argparse.ArgumentParser()
parser.add_argument(
    "hosts", metavar="HOSTS", type=str, help="Hosts to use for testing. One IP per line"
)
parser.add_argument(
    "thms",
    metavar="BENCHMARKS",
    type=str,
    help="Benchmarks to run. One PROOF,ALG,PARTIES,NET,SIZE,TRIAL per trial",
)
parser.add_argument(
    "--output",
    metavar="PATH",
    type=str,
    help="Where to write the output CSV to",
    default="out.csv",
)

args = parser.parse_args()

machines = []
with open(args.hosts) as f:
    for line in f.read().strip().splitlines(keepends=False):
        machines.append(line)

free_machines = queue.Queue()
[free_machines.put(m) for m in machines]
results = queue.Queue()

def run_thread(thm_name, vm_name):
    thm_name = thm_name.replace("'", "\\'")
    try:
        out = sub.run(
            [f"gcloud compute ssh --zone us-west1-b --project gcp-zkpi {username}@{vm_name} -- \"cd crabpi; ./driver.py -e Lean4Examples/{library}.out --circ-exe circ/target/release/examples/circ --time {thm_name}\""], timeout=1800, stderr=sub.PIPE, stdout=sub.PIPE, input="", shell=True
        )
        print("running: ", out.args)
        outstr = out.stdout
        print(outstr)

        r1cs = search_or_default(b"Final R1cs size: (\d*)", outstr, -1)
        simplify_time = search_or_default(b"Simplify/Export time: (\d*)", outstr, -1)
        compile_time = search_or_default(b"Compile Time: (\d*)", outstr, -1)
        gen_time = search_or_default(b"Setup: (\d*)", outstr, -1)
        precompute_time = search_or_default(b"Precomp: (\d*)", outstr, -1)
        prove_time = search_or_default(b"Prove: (\d*)", outstr, -1)
        verify_time = search_or_default(b"Verify: (\d*)", outstr, -1)

        outstrstr = outstr.decode("utf-8")
        if "inductive families with recursive params are unsupported" in str(outstrstr):
            ret_code = -1234 # inductive fams
        elif "Quot" in str(outstrstr):
            ret_code = -1235 # quot sound
        elif "Quotient" in str(outstrstr):
            ret_code = -1235
        elif "eta unsupported" in str(outstrstr):
            ret_code = -1236 # eta expansion
        elif "Typing error" in str(outstrstr):
            ret_code = -1237
        elif "Gigantic NAT..." in str(outstrstr):
            ret_code = -1238
        elif "ELS not impl" in str(outstrstr):
            ret_code = -1239
        else:
            ret_code = out.returncode

        if out.returncode != 0:
            print(r1cs, simplify_time, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code, "\nOut: ", out.stdout.decode("utf-8"), "\nErr: ", out.stderr.decode("utf-8"))
        else:
            print(r1cs, simplify_time, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code)
            
    except sub.TimeoutExpired as e:
        outstr = e.stdout
        r1cs = search_or_default(b"Final R1cs size: (\d*)", outstr, -1)
        simplify_time = search_or_default(b"Simplify/Export time: (\d*)", outstr, -1)
        compile_time = search_or_default(b"Compile Time: (\d*)", outstr, -1)
        gen_time = search_or_default(b"Setup: (\d*)", outstr, -1)
        precompute_time = search_or_default(b"Precomp: (\d*)", outstr, -1)
        prove_time = search_or_default(b"Prove: (\d*)", outstr, -1)
        verify_time = search_or_default(b"Verify: (\d*)", outstr, -1)
        ret_code = -1000
        print(r1cs, simplify_time, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code)
    except Exception as e:
        traceback.print_exc()
        free_machines.put(vm_name)
        return
    free_machines.put(vm_name)
    results.put([thm_name, r1cs, simplify_time, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code])

print(f"{len(machines)} machines")
thms = pd.read_csv(args.thms, header=None)
thms = list(thms[0])
#print(list(thms[0]))
done = pd.read_csv(f"{library}_times_lean4_nat3.csv")
thms = list(pd.Series(thms)[~pd.Series(thms).isin(done["name"])])
rerun = done[(done.returncode == 101)] 
print(rerun)
#done = done[done["name"].str.contains("'")]
#thms = list(done["name"])
#thms = list(rerun["name"])
#merged = thms.merge(done, on="name", how="left", indicator=True)
#thms = list(merged[merged["_merge"] == "left_only"]["name"])
#done = pd.read_csv("stdlib_times_downsampled.csv")
#thms.reverse()
#print(thms)
###thms = thms.sample(1000)
###thms = thms.sort_values("size")
###thms.to_csv("../mathlib_downsampled.csv")
###print(thms)
##

def update_binary(machine):
    out = sub.run(
        [f"gcloud compute ssh --zone us-west1-b --project gcp-zkpi {username}@{machine} -- \"cd crabpi; git pull; cargo build --release\""], timeout=1800, stderr=sub.PIPE, stdout=sub.PIPE, input="", shell=True
    )

threads = []
for machine in machines:
    print("Update Machine:", machine)
    t = threading.Thread(target=update_binary, args=[machine])
    t.start()
    threads.append(t)

for t in threads:
    t.join()
#
outfile = open(f"{library}_times_lean4_nat4.csv", "w+")
writer = csv.writer(outfile)
writer.writerow(["name","r1cs_size","simplify_time","compile_time","gen_time","precompute_time","prove_time","verify_time","returncode"])

threads = []
while len(thms) > 1:
    thm = thms.pop()
    machine = free_machines.get()
    print(f"proving {thm} on machine {machine} (~{len(thms)} remaining)",)
    t = threading.Thread(target=run_thread, args=(thm, machine))
    t.start()
    threads.append(t)
    while not results.empty():
        writer.writerow(results.get())
        outfile.flush()

for t in threads:
    t.join()

while not results.empty():
    writer.writerow(results.get())
    outfile.flush()
