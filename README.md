# zkPi

zkPi is a research project for turning exported Lean proofs into inputs for a
zero-knowledge proof-checking circuit. It includes a Rust proof checker and
exporter, a ZSharp circuit, and a Python driver that runs the circuit through
the bundled CirC compiler's Mirage backend.

The workflow is: **Lean export → zkPi proof conversion → ZSharp circuit →
CirC/Mirage proof**. You can also inspect and simulate proofs without running
the cryptographic backend.

## Requirements

- Rust and Cargo through `rustup`. The repository pins
  `nightly-2023-12-03` in `rust-toolchain` and uses nightly Rust features.
- A native C/C++ build toolchain for the `rug`/GMP dependencies.
- Python 3.9 or newer for `driver.py`; it uses only the standard library.
- A compatible Lean installation to produce an export file. The driver's
  `--lean-file` mode explicitly requires **Lean 3**.
- For the full proving pipeline, the bundled CirC compiler built with the
  `smt`, `zok`, and `mirage` features. See [CirC's README](circ/README.md)
  for its native dependencies and solver setup.

The source also contains Lean 4 export support and examples. The
`Lean4Examples/` project pins Lean `v4.8.0-rc1`; Lean 4 exports are produced
separately using the `lean4export` submodule and supplied via `--export-file`.
The driver does not export Lean 4 source files itself.

## Build

Run commands from the repository root:

```sh
rustup toolchain install nightly-2023-12-03
cargo build --release --locked
```

The executable is written to `target/release/zkpi`. The pinned compiler is
historical; dependency/compiler compatibility may need attention when
reproducing this checkout on a new machine.

To build the optional proving backend:

```sh
cargo build --manifest-path circ/Cargo.toml --release --example circ \
  --features smt,zok,mirage
```

This produces `circ/target/release/examples/circ`.

If you need the Lean 4 exporter, initialize its submodule:

```sh
git submodule update --init --recursive
```

## Inspect and check a proof

The Rust CLI takes a **Lean export file**, rather than a `.lean` source file:

```text
zkpi <PATH> <COMMAND> [theorem]
```

For an existing export named `proof.out`:

```sh
# Find theorem names in the export.
./target/release/zkpi proof.out list

# Replace THEOREM with a name from the list.
./target/release/zkpi proof.out prove THEOREM
./target/release/zkpi proof.out sim THEOREM
./target/release/zkpi proof.out tree THEOREM
./target/release/zkpi proof.out export THEOREM > theorem.pin
```

| Command | Purpose |
| --- | --- |
| `list` | List available theorem names. |
| `prove` | Run the Rust theorem checker. |
| `sim` | Simulate the exported proof-checking rules in Rust. |
| `export` | Serialize inputs for the circuit. |
| `count` | Print ten comma-separated circuit sizing values used by the driver. |
| `term-size` | Report the combined size of the proof term and its type. |
| `tree` | Display theorem trees. |
| `tree-tui` | Explore theorem trees interactively in a terminal. |

`prove` runs the local checker; cryptographic proof generation uses the CirC
pipeline below. Supply a theorem for commands other than `list`: omitting it
currently enters a batch-checking path over up to 200 exported theorems.

## Run the full proving pipeline

With an existing export:

```sh
python3 driver.py --export-file proof.out \
  --circ-exe ./circ/target/release/examples/circ THEOREM
```

With a Lean 3 source file containing `my_theorem`:

```sh
python3 driver.py --lean-file proof.lean \
  --circ-exe ./circ/target/release/examples/circ my_theorem
```

Use `--lean_cmd /path/to/lean` to select a Lean 3 executable. If `circ` is
already on `PATH`, you can omit `--circ-exe`.

The driver runs the Rust converter, writes circuit sizes to `zok/meta.zok`,
writes `zok/<theorem>.pin`, then invokes CirC on `zok/eval.zok` with the Mirage
`oneshot` action. It streams backend output and propagates the backend's exit
status.

Useful options:

- `--time`: print the proof export duration in nanoseconds.
- `--no-cleanup`: retain generated export and `.pin` files.
- `--circuit-directory PATH`: use a circuit directory other than `zok`.

By default, the driver removes the `.pin` file after the backend finishes and
removes a Lean export it generated itself. An export supplied with
`--export-file` is retained. `meta.zok` is overwritten and left in place, so
use separate circuit directories for concurrent runs.

## Prover and verifier: who needs what?

There are two different proofs involved:

- The **original Lean proof** is the private evidence (the witness) used to
  generate the zero-knowledge proof.
- The **zero-knowledge proof** is a cryptographic artifact that a verifier
  should be able to check without receiving that original Lean proof.

A person without the original Lean proof can verify a supplied zero-knowledge
proof. They cannot generate a fresh proof from the theorem statement alone;
they need a valid witness, such as their own proof of the same statement.
Someone with neither proof must first obtain a zero-knowledge proof from a prover.

| Requirement | Prover | Verifier |
| --- | --- | --- |
| Original Lean proof/export and private circuit inputs | Required | Not required; should not be shared |
| Exact public statement and accepted axioms/definitions | Required | Required |
| Agreed circuit version and sizing configuration | Required | Needed to establish what the verification key checks |
| Proving key from setup | Required for a separated proving workflow | Not required |
| Authentic verification key from the same setup | Used for a local check | Required |
| Generated zero-knowledge proof | Produces it | Receives it |
| Compatible verifier software | Useful for a local check | Required |

The public statement is more than a theorem name. In [the circuit](zok/eval.zok),
public inputs include `public_terms`, `expected_type`, `inductives`, `rules`,
`rule_nnrs`, `rule_nrs`, and `axioms`. The verifier must establish that these
encode the intended theorem and acceptable assumptions. Accepting arbitrary
axioms from the prover would change what has been established. The private
inputs include `proof`, `terms`, `lifts`, `proving_rule`, and `contexts`;
`alpha` and `beta` are protocol randomness.

Verification also depends on the correctness of the circuit and backend, and
on trustworthy setup parameters. A verification key supplied by an unknown
prover is not, by itself, evidence that the intended circuit was used or that
setup was performed securely. Circuit dimensions in `meta.zok` are also shared
configuration, so hiding the Lean proof does not imply hiding its size.

### Steps for someone who has the Lean proof

The currently implemented driver supports a local generate-and-check run:

1. Install the requirements and build zkPi and CirC as described above.
2. Prepare a Lean export containing the proof, or use `--lean-file` with
   Lean 3. Use `zkpi proof.out list` to identify the theorem name.
3. Optionally run `zkpi proof.out sim THEOREM` to check the converted inputs
   before paying the cost of cryptographic proving.
4. Run:

   ```sh
   python3 driver.py --export-file proof.out \
     --circ-exe ./circ/target/release/examples/circ THEOREM
   ```

5. CirC's Mirage `oneshot` path generates parameters, generates a proof, and
   calls the cryptographic verifier in the same process. A completed run
   prints `Setup`, `Prove`, and `Verify` timings followed by `Success!`.

**This run does not save a portable zero-knowledge proof or verification key.**
`--no-cleanup` preserves converter inputs, not a shareable cryptographic proof.
Do not send the `.pin` file or the original Lean export to someone who should
not see the proof: those files contain private witness information.

### Steps for someone without the Lean proof

The intended independent verification workflow is:

1. Obtain an authentic verification key for the agreed circuit and setup,
   along with its version and sizing configuration.
2. Receive the cryptographic proof and public inputs from the prover, without
   receiving the private witness.
3. Check that the public inputs represent the desired theorem, definitions,
   and accepted axioms, and that the circuit's success condition is enforced.
4. Run a compatible verifier on the verification key, public inputs, and
   cryptographic proof. Accept only if the cryptographic check succeeds.

**This independent workflow is not currently complete in this checkout.**
In [the Mirage backend](circ/src/target/r1cs/mirage.rs):

- `oneshot` performs a real verification but keeps the keys and proof in memory.
- `gen_params` has its key-writing calls commented out.
- The standalone `verify` function has proof loading and `verify_proof`
  commented out and returns `Ok(())` after reading/preparing the key.
  A successful exit from that standalone command is **not proof verification**.

To support a prover sending a proof to another person, implementation work is
needed to persist setup keys, save the proof, export a public-input-only
package, and restore standalone verification with the same input ordering
and unused-input handling as the one-shot path. Tests must check rejection of
modified proofs, wrong public inputs, and mismatched keys. Until then, a
prover's `Success!` log is a report of their local run, not an independently
verifiable artifact.

## Repository layout

| Path | Contents |
| --- | --- |
| `src/lean.rs` | Lean export parser and theorem conversion. |
| `src/term.rs` | Term representation, evaluation, and checking. |
| `src/zk/` | Circuit input export and Rust simulation. |
| `src/display.rs` | Tree output and interactive viewer. |
| `zok/` | ZSharp proof-checking circuit and sizing template. |
| `circ/` | Bundled circuit compiler and proving backends. |
| `driver.py` | End-to-end proof driver. |
| `lean-examples/`, `Lean4Examples/` | Example Lean sources and a Lean 4 Lake project. |
| `lean4export/` | Lean 4 exporter submodule. |
| `tests/` | Python driver regression tests. |
| `scripts/`, `data/` | Benchmark tooling and recorded results. |

## Development

Run the Python driver tests without installing Lean or CirC:

```sh
python3 -m unittest discover -s tests -v
```

These tests mock proof conversion and backend execution; they do not validate
an end-to-end cryptographic proof. Rust tests can be run with `cargo test
--locked`. The older `run_test.py` script expects external `theorems_sample`
and `init.out` files and is not a self-contained test suite.

## License

The root project is licensed under the [MIT License](LICENSE). Bundled
third-party components retain their own licenses.
