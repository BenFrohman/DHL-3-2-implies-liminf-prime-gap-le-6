# dhl32-lean — DHL[3,2] ⇒ H₁ ≤ 6, formalized in Lean 4 + Mathlib

Lean formalization of the elementary parts of Benjamin Frohman's note
*"Resolving a category error: DHL[3,2] yields H₁ ≤ 6, not H₁ = 2"* (Sept 2026).
**No `sorry`, no new axioms.** Every theorem depends only on Lean's standard
axioms `propext`, `Classical.choice`, `Quot.sound` (see `AxiomAudit.lean`).

This repo does **not** prove DHL[3,2], the Twin Prime Conjecture, or any
unconditional gap bound. DHL[3,2] appears only as a hypothesis.

## Definitions (`DHL32/Basic.lean`)
| Lean | Meaning |
|---|---|
| `p n := Nat.nth Nat.Prime n` | n-th prime, **0-indexed** (`p 0 = 2`, `p 1 = 3`) |
| `gap n := p (n+1) - p n` | consecutive prime gap |
| `H1Le c := ∀ N, ∃ n ≥ N, gap n ≤ c` | encodes `H₁ = liminf gap ≤ c` |
| `Admissible H` | finite `H ⊆ ℕ` misses a residue class mod every prime |
| `DHL k j` | every admissible `H` with `|H| = k` has infinitely many `n` with ≥ j primes among `n + H` |

**Why `H1Le` instead of `liminf`:** for an ℕ-valued sequence and natural `c`,
`liminf gap ≤ c` is equivalent to "gap ≤ c infinitely often". Stating it this
way avoids `liminf` over `ℕ∞`/conditionally complete lattices; it is not a weakening.

Tuples are modeled as `Finset ℕ` (non-negative shifts), which covers the
tuples in the note. The note's "linear forms" generality is not modeled — only
translates `n + h`, which is all the argument uses.

## Theorems
- `two_le_gap : 1 ≤ n → 2 ≤ gap n` — Theorem 1 (with 0-indexing, `n ≥ 1` = all gaps after `3 − 2`).
- `not_H1Le_one : ¬ H1Le 1` — i.e. H₁ ≥ 2.
- `H1Le_three_iff_two : H1Le 3 ↔ H1Le 2`
- `H1Le_three_iff_twin : H1Le 3 ↔ ∀ N, ∃ n ≥ N, gap n = 2` — H₁ ≤ 3 is exactly the Twin Prime Conjecture.
- `admissible_046`, `admissible_026` — {0,4,6} and {0,2,6} are admissible.
- `dhl32_H1Le_six : DHL 3 2 → H1Le 6` — Theorem 2.

Theorem 2's last step is proved directly (no pigeonhole): if primes `a < b`
with `b − a ≤ 6`, then the next prime after `a` is ≤ `b`, so the gap at `a` is ≤ 6.

## Theorems 3 and 4 (honest versions, `DHL32/Theorems34.lean`)
- `DHLfor P k j` — DHL with an abstract decidable predicate `P` in place of primality;
  `DHLfor_prime : DHLfor Nat.Prime k j ↔ DHL k j`.
- **Theorem 3** `dhl32_not_implies_dhl22_combinatorially`: there is a `P`
  (`Ptoy n := n % 4 < 2`) with `DHLfor P 3 2` — for **every** 3-set, hence
  `{0,2,6}` and `{0,4,6}` — yet `P n ∧ P (n+2)` never holds and `DHLfor P 2 2` fails
  (`{0,2}` is admissible, `admissible_02`).
  *Meaning:* `DHL[3,2] ⇒ DHL[2,2]` cannot be derived from the combinatorial form of
  DHL[3,2] alone. **This is not an independence result for the actual primes.**
- **Theorem 4.** The parity barrier is an explicit hypothesis `ParityBarrier Proves`
  (`Proves k j → j ≤ ⌈k/2⌉`), **not an axiom and not proved**.
  - `parity_two_needs_three`: under it, `Proves k 2 → 3 ≤ k`.
  - `admissible_three_diam_ge_six` (unconditional): no admissible 3-set fits in an
    interval `[a, a+5]`; with `min_diam_admissible_three` ({0,2,6}, {0,4,6} admissible)
    the minimal diameter of admissible 3-sets is exactly 6.

Literature claims (Polymath8b's 246, the Stadlmann preprint, the "Tao–Brady" name)
are not formalized.

## Paper
`paper/DHL32_note.tex` and compiled `paper/DHL32_note.pdf` (build: `tectonic paper/DHL32_note.tex`).

## Build
Requires elan. Toolchain `leanprover/lean4:v4.30.0-rc1`, Mathlib `v4.30.0-rc1`.
```
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean AxiomAudit.lean   # prints axioms used
```

Copyright © 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the [Apache License, Version 2.0](LICENSE); see [NOTICE](NOTICE).
