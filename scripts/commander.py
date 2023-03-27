
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
        ["gcloud", "compute", "ssh", "--zone","us-central1-a","--project", "soe-collaborative-proof", ip], stderr=sub.PIPE, stdout=sub.PIPE, input=""
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
parser.add_argument("--user", metavar="USERNAME", default=os.getenv("USER"))

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
            ["gcloud", "compute", "ssh", "--zone","us-central1-a","--project", "soe-collaborative-proof", vm_name, "--", "bash", "oneshot.sh", thm_name], timeout=1800, stderr=sub.PIPE, stdout=sub.PIPE, input=""
        )
        outstr = out.stdout
        r1cs = search_or_default(b"Final R1cs size: (\d*)", outstr, -1)
        compile_time = search_or_default(b"COMPILE TIME: (\d*)", outstr, -1)
        gen_time = search_or_default(b"GEN PARAMS TIME: (\d*)", outstr, -1)
        precompute_time = search_or_default(b"PRECOMPUTE TIME: (\d*)", outstr, -1)
        prove_time = search_or_default(b"PROVE: (\d*)", outstr, -1)
        verify_time = search_or_default(b"VERIFY: (\d*)", outstr, -1)
        ret_code = out.returncode
        print(r1cs, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code)
    except sub.TimeoutExpired as e:
        outstr = e.stdout
        r1cs = search_or_default(b"Final R1cs size: (\d*)", outstr, -1)
        compile_time = search_or_default(b"COMPILE TIME: (\d*)", outstr, -1)
        gen_time = search_or_default(b"GEN PARAMS TIME: (\d*)", outstr, -1)
        precompute_time = search_or_default(b"PRECOMPUTE TIME: (\d*)", outstr, -1)
        prove_time = search_or_default(b"PROVE: (\d*)", outstr, -1)
        verify_time = search_or_default(b"VERIFY: (\d*)", outstr, -1)
        ret_code = -1000
        print(r1cs, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code)
    except Exception as e:
        traceback.print_exc()
        free_machines.put(vm_name)
        return
    free_machines.put(vm_name)
    results.put([thm_name, r1cs, compile_time, gen_time, precompute_time, prove_time, verify_time, ret_code])
username = args.user

print(f"{len(machines)} machines")
thms = pd.read_csv(args.thms)
done = pd.read_csv("stdlib_times_downsampled.csv")
done = done[done["name"].str.contains("'")]
thms = list(done["name"])
#merged = thms.merge(done, on="name", how="left", indicator=True)
#thms = list(merged[merged["_merge"] == "left_only"]["name"])
#done = pd.read_csv("stdlib_times_downsampled.csv")
thms.reverse()
print(thms)
###thms = thms.sample(1000)
###thms = thms.sort_values("size")
###thms.to_csv("../mathlib_downsampled.csv")
###print(thms)
##
outfile = open("stdlib_times_downsampled_appostroph.csv", "w+")
writer = csv.writer(outfile)
writer.writerow(["name","r1cs_size","compile_time","gen_time","precompute_time","prove_time","verify_time","returncode"])

threads = []
while len(thms) > 1:
    thm = thms.pop()
    machine = free_machines.get()
    print(f"proving {thm} on machine {machine}")
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
