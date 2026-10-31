import Mathlib

/-!
# DHL[3,2] ⇒ H₁ ≤ 6 (formalization of B. Frohman's note)
-/

namespace DHL32

/-- `p n` is the `n`-th prime, **0-indexed**: `p 0 = 2`, `p 1 = 3`, … -/
noncomputable def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Consecutive prime gap `p (n+1) - p n`. -/
noncomputable def gap (n : ℕ) : ℕ := p (n + 1) - p n

/-- `H1Le c` encodes `H₁ = liminf (p_{n+1} - p_n) ≤ c` for natural `c`:
there are infinitely many `n` with `gap n ≤ c`. (For an ℕ-valued sequence this is
exactly `liminf ≤ c`, and avoids `liminf` / `ℕ∞` bookkeeping.) -/
def H1Le (c : ℕ) : Prop := ∀ N, ∃ n ≥ N, gap n ≤ c

/-- A finite set `H ⊆ ℕ` is admissible if for every prime `q` it misses some
residue class mod `q`. -/
def Admissible (H : Finset ℕ) : Prop :=
  ∀ q, q.Prime → ∃ r < q, ∀ h ∈ H, h % q ≠ r

/-- `DHL k j`: every admissible `k`-tuple `H` has infinitely many translates
`n + H` containing at least `j` primes. -/
def DHL (k j : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → Admissible H →
    ∀ N, ∃ n ≥ N, j ≤ (H.filter (fun h => (n + h).Prime)).card

lemma p_strictMono : StrictMono p := Nat.nth_strictMono Nat.infinite_setOf_prime

lemma p_prime (n : ℕ) : (p n).Prime := Nat.prime_nth_prime n

lemma p_zero : p 0 = 2 := Nat.nth_prime_zero_eq_two

lemma p_odd {n : ℕ} (hn : 1 ≤ n) : Odd (p n) := by
  rcases (p_prime n).eq_two_or_odd' with h | h
  · have := p_strictMono (show 0 < n by omega)
    rw [p_zero, h] at this; omega
  · exact h

/-- **Theorem 1.** For `n ≥ 1` (i.e. after the gap `3 - 2 = 1`), every consecutive
prime gap is at least 2. -/
theorem two_le_gap {n : ℕ} (hn : 1 ≤ n) : 2 ≤ gap n := by
  have h1 := p_odd hn
  have h2 : Odd (p (n + 1)) := p_odd (show 1 ≤ n + 1 by omega)
  have hlt : p n < p (n + 1) := p_strictMono (Nat.lt_succ_self n)
  unfold gap
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  omega

lemma gap_even {n : ℕ} (hn : 1 ≤ n) : Even (gap n) := by
  have h1 := p_odd hn
  have h2 : Odd (p (n + 1)) := p_odd (show 1 ≤ n + 1 by omega)
  have hlt : p n < p (n + 1) := p_strictMono (Nat.lt_succ_self n)
  unfold gap
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2
  exact ⟨b - a, by omega⟩

/-- No `H₁ < 2`: only finitely many gaps (just `n = 0`) are `≤ 1`. -/
theorem not_H1Le_one : ¬ H1Le 1 := by
  intro h
  obtain ⟨n, hn, hg⟩ := h 1
  have := two_le_gap hn; omega

/-- **Theorem 1, consequence.** `H₁ ≤ 3 ↔ H₁ ≤ 2`. -/
theorem H1Le_three_iff_two : H1Le 3 ↔ H1Le 2 := by
  constructor
  · intro h N
    obtain ⟨n, hn, hg⟩ := h (max N 1)
    have h1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨k, hk⟩ := gap_even h1
    exact ⟨n, le_trans (le_max_left _ _) hn, by omega⟩
  · intro h N
    obtain ⟨n, hn, hg⟩ := h N
    exact ⟨n, hn, by omega⟩

/-- **Theorem 1, consequence.** `H₁ ≤ 3` iff infinitely many gaps equal exactly 2
(the Twin Prime Conjecture). -/
theorem H1Le_three_iff_twin : H1Le 3 ↔ ∀ N, ∃ n ≥ N, gap n = 2 := by
  rw [H1Le_three_iff_two]
  constructor
  · intro h N
    obtain ⟨n, hn, hg⟩ := h (max N 1)
    have h1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have := two_le_gap h1
    exact ⟨n, le_trans (le_max_left _ _) hn, by omega⟩
  · intro h N
    obtain ⟨n, hn, hg⟩ := h N
    exact ⟨n, hn, by omega⟩

lemma residues_small {q : ℕ} (hq : 7 ≤ q) (h : ℕ) (hh : h ≤ 6) : h % q = h :=
  Nat.mod_eq_of_lt (by omega)

/-- `{0,4,6}` is admissible. -/
theorem admissible_046 : Admissible {0, 4, 6} := by
  intro q hq
  have h2 := hq.two_le
  by_cases h7 : 7 ≤ q
  · refine ⟨1, by omega, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl <;> rw [residues_small h7 _ (by omega)] <;> omega
  · interval_cases q
    · exact ⟨1, by omega, by decide⟩
    · exact ⟨2, by omega, by decide⟩
    · exact absurd hq (by decide)
    · exact ⟨2, by omega, by decide⟩
    · exact absurd hq (by decide)

/-- `{0,2,6}` is admissible. -/
theorem admissible_026 : Admissible {0, 2, 6} := by
  intro q hq
  have h2 := hq.two_le
  by_cases h7 : 7 ≤ q
  · refine ⟨1, by omega, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl <;> rw [residues_small h7 _ (by omega)] <;> omega
  · interval_cases q
    · exact ⟨1, by omega, by decide⟩
    · exact ⟨1, by omega, by decide⟩
    · exact absurd hq (by decide)
    · exact ⟨3, by omega, by decide⟩
    · exact absurd hq (by decide)

/-- Key lemma: if `a < b` are primes, then the consecutive gap starting at `a`
is at most `b - a`, and its index is `≥ N` whenever `a ≥ p N`. -/
lemma gap_le_of_primes {a b N : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a < b)
    (hN : p N ≤ a) : ∃ m ≥ N, gap m ≤ b - a := by
  set m := Nat.count Nat.Prime a
  have hpa : p m = a := Nat.nth_count ha
  have hpb : p (Nat.count Nat.Prime b) = b := Nat.nth_count hb
  have hc : m + 1 ≤ Nat.count Nat.Prime b := by
    have : Nat.count Nat.Prime (a + 1) = m + 1 :=
      (Nat.count_succ_eq_succ_count_iff).2 ha
    rw [← this]; exact Nat.count_monotone _ (by omega)
  have hle : p (m + 1) ≤ b := hpb ▸ p_strictMono.monotone hc
  refine ⟨m, ?_, ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    have := p_strictMono hlt
    omega
  · unfold gap; omega

/-- **Theorem 2.** `DHL[3,2]` implies `H₁ ≤ 6`. -/
theorem dhl32_H1Le_six (h : DHL 3 2) : H1Le 6 := by
  intro N
  obtain ⟨n, hn, hcard⟩ := h {0, 4, 6} (by decide) admissible_046 (p N)
  -- at least two of n, n+4, n+6 are prime
  have key : ∃ a b, a.Prime ∧ b.Prime ∧ n ≤ a ∧ a < b ∧ b ≤ a + 6 := by
    by_cases h0 : (n + 0).Prime <;> by_cases h4 : (n + 4).Prime <;>
      by_cases h6 : (n + 6).Prime
    all_goals first
      | exact ⟨n, n + 4, by simpa using h0, h4, le_rfl, by omega, by omega⟩
      | exact ⟨n + 4, n + 6, h4, h6, by omega, by omega, by omega⟩
      | exact ⟨n, n + 6, by simpa using h0, h6, le_rfl, by omega, by omega⟩
      | (exfalso
         simp only [add_zero] at h0
         simp [Finset.filter_insert, Finset.filter_singleton, h0, h4, h6] at hcard)
  obtain ⟨a, b, ha, hb, hna, hab, hb6⟩ := key
  obtain ⟨m, hm, hg⟩ := gap_le_of_primes ha hb hab (le_trans hn hna)
  exact ⟨m, hm, by omega⟩

end DHL32
