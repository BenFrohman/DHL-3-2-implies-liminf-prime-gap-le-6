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

## Not formalized
Theorems 3 and 4 of the note (non-implication DHL[3,2] ⇏ DHL[2,2]; parity /
sieve-limit discussion; literature bounds such as Polymath8b's 246) are
meta-mathematical or literature claims, not formal statements, so they are omitted.

## Build
Requires elan. Toolchain `leanprover/lean4:v4.30.0-rc1`, Mathlib `v4.30.0-rc1`.
```
lake exe cache get   # download prebuilt Mathlib
lake build
lake env lean AxiomAudit.lean   # prints axioms used
```
