import DHL32.Basic

/-!
# Honest versions of Theorems 3 and 4

* Theorem 3 is a **relative-consistency / model** statement for an *abstract*
  predicate `P`. It shows that `DHL[2,2]` (twin-type hits) cannot be derived from
  the *combinatorial form* of `DHL[3,2]` alone. It says **nothing** about
  independence for the actual primes.
* Theorem 4 takes the parity barrier as an explicit **hypothesis structure**
  (`ParityBarrier`), never as an axiom.
-/

namespace DHL32

/-- `DHL[k,j]` for an arbitrary predicate `P` in place of primality. -/
def DHLfor (P : ℕ → Prop) [DecidablePred P] (k j : ℕ) : Prop :=
  ∀ H : Finset ℕ, H.card = k → Admissible H →
    ∀ N, ∃ n ≥ N, j ≤ (H.filter (fun h => P (n + h))).card

theorem DHLfor_prime (k j : ℕ) : DHLfor Nat.Prime k j ↔ DHL k j := Iff.rfl

/-- The toy "prime predicate": residues 0 and 1 mod 4. It never contains two
numbers differing by 2, yet it contains pairs at every difference `≢ 2 (mod 4)`. -/
def Ptoy (n : ℕ) : Prop := n % 4 < 2

instance : DecidablePred Ptoy := fun n => inferInstanceAs (Decidable (n % 4 < 2))

lemma Ptoy_no_twin (n : ℕ) : ¬ (Ptoy n ∧ Ptoy (n + 2)) := by
  unfold Ptoy; omega

lemma Ptoy_hit {x y : ℕ} (_hxy : x < y) (hd : (y + 3 * x) % 4 ≠ 2) (N : ℕ) :
    ∃ n ≥ N, Ptoy (n + x) ∧ Ptoy (n + y) := by
  unfold Ptoy
  by_cases h3 : (y + 3 * x) % 4 = 3
  · exact ⟨4 * (N + x) + 1 - x, by omega, by omega, by omega⟩
  · exact ⟨4 * (N + x) - x, by omega, by omega, by omega⟩

lemma Ptoy_hit' {x y : ℕ} (hxy : x ≠ y) (hd : (y + 3 * x) % 4 ≠ 2) (N : ℕ) :
    ∃ n ≥ N, Ptoy (n + x) ∧ Ptoy (n + y) := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact Ptoy_hit h hd N
  · obtain ⟨n, hn, a, b⟩ := Ptoy_hit h (by omega) N
    exact ⟨n, hn, b, a⟩

/-- `Ptoy` satisfies the 3-tuple / 2-hit property for **every** 3-element set
(admissible or not), in particular for `{0,2,6}` and `{0,4,6}`. -/
theorem Ptoy_DHL32 : DHLfor Ptoy 3 2 := by
  intro H hH _ N
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hH
  have pair : ∀ a b, a ∈ ({x, y, z} : Finset ℕ) → b ∈ ({x, y, z} : Finset ℕ) →
      a ≠ b → (b + 3 * a) % 4 ≠ 2 →
      ∃ n ≥ N, 2 ≤ (({x, y, z} : Finset ℕ).filter (fun h => Ptoy (n + h))).card := by
    intro a b ha hb hab hd
    obtain ⟨n, hn, pa, pb⟩ := Ptoy_hit' hab hd N
    refine ⟨n, hn, ?_⟩
    have hsub : ({a, b} : Finset ℕ) ⊆ ({x, y, z} : Finset ℕ).filter (fun h => Ptoy (n + h)) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp_all [Finset.mem_filter]
    calc 2 = ({a, b} : Finset ℕ).card := (Finset.card_pair hab).symm
      _ ≤ _ := Finset.card_le_card hsub
  by_cases h1 : (y + 3 * x) % 4 = 2
  · by_cases h2 : (z + 3 * y) % 4 = 2
    · exact pair x z (by simp) (by simp) hxz (by omega)
    · exact pair y z (by simp) (by simp) hyz h2
  · exact pair x y (by simp) (by simp) hxy h1

/-- `{0,2}` is admissible. -/
theorem admissible_02 : Admissible {0, 2} := by
  intro q hq
  have h2 := hq.two_le
  by_cases h3 : 3 ≤ q
  · refine ⟨1, by omega, ?_⟩
    intro h hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl
    · simp
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · exact ⟨1, by omega, by interval_cases q; decide⟩

/-- **Theorem 3 (honest version).** There is a predicate `P` satisfying the
combinatorial `DHL[3,2]` (indeed for all 3-sets, so in particular `{0,2,6}` and
`{0,4,6}`) for which only finitely many (in fact zero) `n` have `P n ∧ P (n+2)`,
and `DHL[2,2]` fails.

Hence `DHL[3,2] → DHL[2,2]` (or `→` twin primes) is **not provable from the
combinatorial form of `DHL[3,2]` alone**; any proof must use more about the
primes. This is **not** an independence result for the actual primes. -/
theorem dhl32_not_implies_dhl22_combinatorially :
    ∃ (P : ℕ → Prop) (_ : DecidablePred P), DHLfor P 3 2 ∧ (∀ n, ¬ (P n ∧ P (n + 2))) ∧ ¬ DHLfor P 2 2 := by
  refine ⟨Ptoy, inferInstance, Ptoy_DHL32, Ptoy_no_twin, ?_⟩
  intro h
  obtain ⟨n, -, hc⟩ := h {0, 2} (by decide) admissible_02 0
  have := Ptoy_no_twin n
  by_cases a : Ptoy n <;> by_cases b : Ptoy (n + 2) <;>
    simp_all [Finset.filter_insert, Finset.filter_singleton]

/-- **Parity barrier, as an explicit hypothesis** (not an axiom, and not proved).
`Proves k j` stands for "the sieve method under consideration establishes
`DHL[k,j]`"; the hypothesis says it can detect at most `⌈k/2⌉ = (k+1)/2` primes. -/
structure ParityBarrier (Proves : ℕ → ℕ → Prop) : Prop where
  bound : ∀ k j, Proves k j → j ≤ (k + 1) / 2

/-- **Theorem 4(a).** Under the parity hypothesis, getting `j = 2` needs `k ≥ 3`. -/
theorem parity_two_needs_three {Proves : ℕ → ℕ → Prop} (hP : ParityBarrier Proves)
    {k : ℕ} (h : Proves k 2) : 3 ≤ k := by
  have := hP.bound k 2 h; omega

/-- **Theorem 4(b)** (unconditional). Every admissible 3-set has diameter `≥ 6`:
it is not contained in any interval `[a, a+5]`. -/
theorem admissible_three_diam_ge_six {H : Finset ℕ} (hA : Admissible H)
    (hH : H.card = 3) (a : ℕ) : ¬ ∀ h ∈ H, a ≤ h ∧ h ≤ a + 5 := by
  intro hI
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hH
  obtain ⟨r2, hr2, h2⟩ := hA 2 Nat.prime_two
  obtain ⟨r3, hr3, h3⟩ := hA 3 Nat.prime_three
  have hx := hI x (by simp); have hy := hI y (by simp); have hz := hI z (by simp)
  have a2 := h2 x (by simp); have b2 := h2 y (by simp); have c2 := h2 z (by simp)
  have a3 := h3 x (by simp); have b3 := h3 y (by simp); have c3 := h3 z (by simp)
  have p1 : x % 2 = y % 2 := by interval_cases r2 <;> omega
  have p2 : x % 2 = z % 2 := by interval_cases r2 <;> omega
  have q1 : x % 3 ≠ y % 3 := by omega
  have q2 : x % 3 ≠ z % 3 := by omega
  have q3 : y % 3 ≠ z % 3 := by omega
  have := Nat.mod_lt x (show 0 < 3 by norm_num)
  have := Nat.mod_lt y (show 0 < 3 by norm_num)
  have := Nat.mod_lt z (show 0 < 3 by norm_num)
  interval_cases r3 <;> omega

/-- Diameter 6 is attained, so 6 is the minimal diameter of admissible 3-sets. -/
theorem min_diam_admissible_three :
    Admissible ({0, 2, 6} : Finset ℕ) ∧ Admissible ({0, 4, 6} : Finset ℕ) ∧
    ∀ H : Finset ℕ, Admissible H → H.card = 3 → ∀ a, ¬ ∀ h ∈ H, a ≤ h ∧ h ≤ a + 5 :=
  ⟨admissible_026, admissible_046, fun _ hA hH a => admissible_three_diam_ge_six hA hH a⟩

/-- Under the parity hypothesis, the best sieve-reachable two-prime statement uses
`k ≥ 3`, whose admissible sets have diameter `≥ 6`. -/
theorem parity_floor {Proves : ℕ → ℕ → Prop} (hP : ParityBarrier Proves)
    {k : ℕ} (h : Proves k 2) : 3 ≤ k := parity_two_needs_three hP h

end DHL32
