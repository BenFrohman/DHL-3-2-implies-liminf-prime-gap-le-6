# Kernel certificate: DHL-3-2-implies-liminf-prime-gap-le-6

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/DHL-3-2-implies-liminf-prime-gap-le-6 |
| Certified commit | `0546ab9f808799c91e6748548398092071f8c6f0` (branch `chore/kernel-certificate`) |
| Lean sources | identical to `master` at `cb162607825d58286d123284bcb8c7b73e8d81bc`: no `.lean`, lakefile, manifest or toolchain file differs; the certified commit only adds CI and the scripts in `certificates/tools/` |
| lean-toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Mathlib | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json; inputRev `v4.30.0-rc1`) |
| Date (UTC) | 2026-11-16T19:22:36Z |
| CI run | https://github.com/BenFrohman/DHL-3-2-implies-liminf-prime-gap-le-6/actions/runs/43937997202 |
| `lake build` | `Build completed successfully (8267 jobs).` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` ([sorry-scan.txt](sorry-scan.txt)) |
| `#print axioms` | `AUDIT PASS: 29 theorems in 2 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 3 of 3 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 3 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (29 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: leanchecker source shipped with v4.30.0-rc1 (src/lean/LeanChecker.lean), prefix match -> exact match, run with lean --run. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

Full `#print axioms` output (verbatim from `axioms.txt`):

```
'DHL32.H1Le_three_iff_twin' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.H1Le_three_iff_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.admissible_026' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.admissible_046' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.dhl32_H1Le_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.gap_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.gap_le_of_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.not_H1Le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.p_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.p_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.p_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.p_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.residues_small' depends on axioms: [propext, Quot.sound]
'DHL32.two_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.DHLfor.congr_simp' depends on axioms: [propext, Quot.sound]
'DHL32.DHLfor_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.ParityBarrier.bound' does not depend on any axioms
'DHL32.Ptoy.eq_1' does not depend on any axioms
'DHL32.Ptoy_DHL32' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.Ptoy_hit' depends on axioms: [propext, Quot.sound]
'DHL32.Ptoy_hit'' depends on axioms: [propext, Quot.sound]
'DHL32.Ptoy_iff_mod_four_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.Ptoy_no_twin' depends on axioms: [propext, Quot.sound]
'DHL32.admissible_02' depends on axioms: [propext, Quot.sound]
'DHL32.admissible_three_diam_ge_six' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.dhl32_not_implies_dhl22_combinatorially' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.min_diam_admissible_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'DHL32.parity_floor' depends on axioms: [propext, Quot.sound]
'DHL32.parity_two_needs_three' depends on axioms: [propext, Quot.sound]
```

## Rebuild

```
git clone https://github.com/BenFrohman/DHL-3-2-implies-liminf-prime-gap-le-6.git && cd DHL-3-2-implies-liminf-prime-gap-le-6 && git checkout 0546ab9f808799c91e6748548398092071f8c6f0 && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
