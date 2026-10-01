# veles

Kernel-checked certificates for Erdős Problem 835, in Lean 4.

Erdős Problem 835 asks whether, for some k > 2, the k-subsets of a 2k-set can be coloured with
k + 1 colours so that every (k+1)-subset sees all colours. It is open. This repository proves in
Lean 4, against the formal-conjectures statement, the known part of its resolution:

- `Property k ↔ χ(J(2k,k)) = k+1 ↔` a large set of Steiner systems `LS(k-1, k, 2k)`;
- Ma and Tang's theorem for every k (k + 1 composite rules k out), and Johnson's bound;
- k = 4 and k = 6 by kernel-checked large-set certificates;
- no Steiner system S(4,5,15), hence k = 10, by a kernel-checked certificate;
- the frontier: `Property 16` gives an S(4,5,21), and `Property k` for 7 ≤ k ≤ 192 gives a
  solution of Epoch AI's FrontierMath problem "Large Steiner Systems".

k = 12 rests on Östergård and Pottonen's non-existence of S(4,5,17), which is cited, not checked.
The paper is `paper/main.tex`.

## Layout

- `Veles/`: Lean sources. `Results.lean` collects the theorems; `AxiomCheck.lean` and
  `AxiomAudit.lean` are the axiom gate; `Tests/` holds edge cases, the upstream statement test and
  checks of the S(3,4,9) test certificate.
- `certgen/`: certificate generator (C), independent second generator and replay (Python), Lean
  emitter.
- `certs/`: the six certificates (xz) and their SHA-256 sums.
- `scripts/`: the gate and the checks (see below).
- `upstream/`: verbatim copies of five files of
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
  137aec5c7abd3aa61f7a73138a97279acfc79e93 (Apache-2.0, notices kept), with that commit's
  `lean-toolchain` and `lake-manifest.json`; `scripts/check_upstream.py` pins their hashes.
- `docs/ledger/`: one append-only ledger per certificate, and `facts.json` (the numbers the paper
  states).
- `docs/verification/gate_freeze.log`: the log of the final run of the gate.

## Checking

Toolchain: `lean-toolchain` (Lean v4.34.0-rc2) and `lakefile.toml` (Mathlib 85e3a25). Set up Mathlib
once with `lake exe cache get` in this directory (or any project requiring the same Mathlib), then
`export LEAN_PATH=$(lake env printenv LEAN_PATH)` and put the toolchain's `bin` (with `lean` and
`leanchecker`) on `PATH`.

1. `scripts/pod_gate.sh [P]` is the gate, meant for a large machine. It deletes `build/`, checks the
   toolchain and Mathlib pins, scans every source (`scripts/scan_sources.py`), checks the upstream
   copies (`scripts/check_upstream.py`), decompresses `certs/` and checks `certs/SHA256SUMS`, emits
   the generated certificate modules, builds all modules P at a time, checks the axiom manifest
   (`Veles/AxiomCheck.lean`) and the library-wide audit (`Veles/AxiomAudit.lean`), and replays the
   44 modules outside the three large certificates with `leanchecker`. `--dev` reuses an existing
   build and marks the result DEV.
2. `scripts/regen_certs.sh` regenerates the six certificates with `certgen/gen_cert.c` and compares
   them byte for byte with `certs/`; `--both` also runs the independent Python generator
   `certgen/gen_cert_b.py` (needs numpy; hours for S(4,5,15)) and the independent replay
   `certgen/verify_cert.py`.
3. `scripts/freeze_check.sh` (minutes) runs the checks that need no Lean build: the source scan,
   the upstream test, `scripts/lean_index.py` (every Lean name and file the paper cites exists),
   `scripts/verify_paper_claims.py` (every number the paper states, against `docs/ledger/facts.json`)
   and `scripts/check_reps.py` (the phase representatives of the S(4,5,15) certificate). It also
   checks that the gate log passed in freeze mode and records the source hash of this tree
   (`scripts/src_hash.sh`).

`scripts/cert_facts.py` and `scripts/make_ledger.py` write `docs/ledger/` on the build machine from a
gate run; `scripts/build_parallel.py` and `scripts/gen_hash.sh` are used by the gate.

Trusted base: the Lean kernel, with axioms `propext`, `Classical.choice`, `Quot.sound` only; no
`sorry`, no `native_decide`, no solver. The certificate programs are not trusted: the final
statements are written by hand in `Veles/Results.lean`.

Cost: the S(4,5,15) certificate replays 1,944,980 search nodes in 1,498 modules; building all
modules took 16.3 module build hours in the final gate, and the largest module needs 55 GiB of
memory, so run them in parallel on a large machine.

## License

Apache License 2.0 (`LICENSE`). The files in `upstream/` and the definitions copied from them into
`Veles/Upstream.lean` and `Veles/UpstreamComposite.lean` are © The Formal Conjectures Authors,
under the same license.
