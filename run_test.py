
import subprocess

f = open("theorems_sample", "r")
for line in f.readlines():
    line = line.strip()
    p = subprocess.run(["cargo", "run", "--release", "init.out", "sim", line], capture_output=True)
    
    print(p.stdout.decode())
    print(p.stderr.decode())
