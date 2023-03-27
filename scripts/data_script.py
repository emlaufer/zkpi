
import pandas as pd

#a = pd.read_csv("stdlib_times.csv")
#b = pd.read_csv("stdlib_times.csv.new")
#c = pd.read_csv("stdlib_times.csv.even_newer")
#
#merged = pd.concat([a, b, c])
#print(merged["returncode"].value_counts())
hi = pd.read_csv("stdlib_times_downsampled.csv")
hi2 = pd.read_csv("stdlib_times_downsampled_appostroph.csv")
hi = hi[~hi["name"].str.contains("'")]
hi = pd.concat([hi, hi2])
hi.to_csv("stdlib_downsized_FULL.csv")
print(hi)
#hi = hi.sort_values("size")
#hi.to_csv("../mathlib_downsized.csv")
