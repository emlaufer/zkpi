
import subprocess
import csv
import signal
import sys

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
    process = subprocess.run(["cargo", "run", "--release", "stdlib.out", "count", name], capture_output=True)
    return process.stdout

sed_template = "s/__PROOF_SIZE/{}/g; s/__NUM_TERMS/{}/g; s/__CONTEXT_SIZE/{}/g; s/__NUM_LIFTS/{}/g; s/__NUM_INDS/{}/g; s/__NUM_PUB_TERMS/{}/g"
meta_file = "zok/meta.zok"

def set_compile_size(proof_size, num_terms, context_size, num_lifts, num_inds, num_pub_terms):
    sed_full = sed_template.format(proof_size, num_terms, context_size, num_lifts, num_inds, num_pub_terms)
    print(sed_full)
    process = subprocess.run(["sed", sed_full, "zok/meta.zok.template"], capture_output=True)
    with open(meta_file, 'w') as meta:
        meta.write(process.stdout.decode("utf-8"))

def sizes():
    run_over_all("count", "stdlib_sizes.csv")

def oneshot(name):
    print(crabpi("stdlib.out", "count", name))

def run_over_all(cmd, outfile):
    with open(filename, newline='') as csvfile:
        with open(outfile, "w") as out:
            log("Counting all in", filename)
            reader = csv.reader(csvfile, delimiter=',', quotechar='|')
            for row in list(reader):
                log("Counting: ", row[0])
                process = subprocess.run(["cargo", "run", "--release", "stdlib.out", cmd, row[0]], capture_output=True, timeout=108000)
                if process.returncode == 0:
                    out.write(row[0]+","+process.stdout.decode("utf-8"))
                else:
                    print("error...", process.returncode)
print(sys.argv[1])
if sys.argv[1] == "count":
    sizes()


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
