import Erdos291.SecondMoment
import Erdos291.BadSetGrowth
import Erdos291.BadSet
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Finset.Prod

/-!
# Erdős #291 — the second-moment double count

This file re-expresses the second factorial moment

  `M x = Σ_{p ≤ x} f_p (f_p - 1) / (p - 1)`,   `f_p = |E p|`,

as a sum over *distances* `d` of the number of bad-residue pairs `{r, r + d}` at that
distance.  The key identity is

  `f_p (f_p - 1) = 2 · Σ_{d = 1}^{p - 2} #{r | r, r + d ∈ E p}`,

a purely combinatorial double count: `f_p (f_p - 1)` counts *ordered* pairs of distinct
bad residues, which is twice the number of *unordered* pairs, and unordered pairs are
classified bijectively by their distance `d ∈ [1, p - 2]`.

With this in hand we obtain two consequences.

* `M_eq_two_mul_sum_dist`: `M x` as a double sum over primes and distances.
* `M_le_pair_wall`: `M x ≤ Σ_{p ≤ x} (p - 2)(p - 3) / (p - 1)`, obtained by bounding
  each distance-fibre `#{r | r, r + d ∈ E p} ≤ d - 1` (the spacing bound) and summing the
  arithmetic series `Σ_{d=1}^{p-2} (d - 1) = (p - 2)(p - 3) / 2`.

The wall `Σ_{p ≤ x} (p - 2)(p - 3) / (p - 1) ≍ x² / log x` is strictly worse than the
trivial `x^{4/3} / log x`, so the spacing/pair bound alone cannot reach `O(log log x)`;
this file makes that negative result machine-checkable.

There are no unproved declarations in this file.
-/

open scoped BigOperators

namespace Erdos291

/-! ## Small auxiliary facts -/

/-- The product of a natural number with its predecessor is even, i.e. `2 ∣ n (n - 1)`. -/
lemma two_dvd_mul_pred (n : ℕ) : 2 ∣ n * (n - 1) :=
  even_iff_two_dvd.mp (Nat.even_mul_pred_self n)

/-- The arithmetic-series identity `Σ_{d=1}^{n-1} (d - 1) = (n - 1)(n - 2) / 2`, proved by
reindexing `d ↦ d - 1` to `Finset.range (n - 1)` and applying `Finset.sum_range_id`. -/
lemma sum_Icc_one_pred_eq (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 (n - 1), (d - 1)) = (n - 1) * (n - 2) / 2 := by
  calc
    (∑ d ∈ Finset.Icc 1 (n - 1), (d - 1)) = ∑ e ∈ Finset.range (n - 1), e := by
      refine Finset.sum_bij (fun d _ => d - 1) ?_ ?_ ?_ ?_
      · intro d hd
        rw [Finset.mem_range]
        have hd' : 1 ≤ d ∧ d ≤ n - 1 := Finset.mem_Icc.mp hd
        omega
      · intro d₁ hd₁ d₂ hd₂ h
        have hd₁' : 1 ≤ d₁ ∧ d₁ ≤ n - 1 := Finset.mem_Icc.mp hd₁
        have hd₂' : 1 ≤ d₂ ∧ d₂ ≤ n - 1 := Finset.mem_Icc.mp hd₂
        omega
      · intro e he
        have he' : e < n - 1 := Finset.mem_range.mp he
        refine ⟨e + 1, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      · intro d hd
        rfl
    _ = (n - 1) * (n - 2) / 2 := by
        simpa [show (n - 1) - 1 = n - 2 by omega] using Finset.sum_range_id (n - 1)

/-- Real-valued version: `Σ_{d=1}^{p-2} (d - 1) = (p - 2)(p - 3) / 2` in `ℝ`. -/
lemma sum_Icc_one_pred_eq_real (p : ℕ) :
    (∑ d ∈ Finset.Icc 1 (p - 2), ((d - 1 : ℕ) : ℝ))
      = (((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / 2 := by
  have hnat : (∑ d ∈ Finset.Icc 1 (p - 2), (d - 1)) = (p - 2) * (p - 3) / 2 := by
    simpa [show (p - 1) - 1 = p - 2 by omega, show (p - 1) - 2 = p - 3 by omega]
      using sum_Icc_one_pred_eq (p - 1)
  have hdvd : 2 ∣ (p - 2) * (p - 3) := by
    simpa [show (p - 2) - 1 = p - 3 by omega] using two_dvd_mul_pred (p - 2)
  rw [← Nat.cast_sum, hnat, Nat.cast_div_charZero hdvd, Nat.cast_mul]
  norm_num

/-! ## Theorem 1: the pair double count -/

/-- **The pair double count.** For every `p`, the number of ordered pairs of distinct bad
residues `f_p (f_p - 1)` equals twice the sum over distances `d ∈ [1, p - 2]` of the number
`#{r | r, r + d ∈ E p}` of bad-residue pairs at distance `d`. -/
lemma E_pairs_card_eq_two_mul_sum_dist (p : ℕ) :
    (E p).card * ((E p).card - 1) =
      2 * ∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card := by
  have hsum : (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card)
      = (upPairs (E p) (p - 1)).card := by
    simpa [show (p - 1) - 1 = p - 2 by omega]
      using (upPairs_card_eq (E p) (p - 1)).symm
  have hup : upPairs (E p) (p - 1) = ((E p).product (E p)).filter (fun q => q.1 < q.2) := by
    ext q
    simp only [upPairs, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1, h.2.1⟩
    · intro hq
      rcases hq with ⟨hprod, hlt⟩
      constructor
      · exact hprod
      · constructor
        · exact hlt
        · have hq2E : q.2 ∈ E p := (Finset.mem_product.mp hprod).2
          have hq1E : q.1 ∈ E p := (Finset.mem_product.mp hprod).1
          have hEsub : E p ⊆ Finset.Icc 1 (p - 1) := by
            rw [E]
            exact Finset.filter_subset _ _
          have hq2_le : q.2 ≤ p - 1 := (Finset.mem_Icc.mp (hEsub hq2E)).2
          have hq1_ge : 1 ≤ q.1 := (Finset.mem_Icc.mp (hEsub hq1E)).1
          omega
  have hchoose : (((E p).product (E p)).filter (fun q => q.1 < q.2)).card
      = Nat.choose (E p).card 2 := by
    rw [Finset.product_eq_sprod]
    exact Finset.card_product_filter_lt (s := E p)
  have h2 : 2 * Nat.choose (E p).card 2 = (E p).card * ((E p).card - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (two_dvd_mul_pred ((E p).card))
  calc
    (E p).card * ((E p).card - 1)
        = 2 * Nat.choose (E p).card 2 := h2.symm
    _ = 2 * (((E p).product (E p)).filter (fun q => q.1 < q.2)).card := by rw [hchoose]
    _ = 2 * (upPairs (E p) (p - 1)).card := by rw [← hup]
    _ = 2 * (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card) := by
        rw [← hsum]

/-- Casting `f_p (f_p - 1)` to `ℝ` commutes with the subtraction. -/
lemma cast_card_mul_pred_card (p : ℕ) :
    (((E p).card * ((E p).card - 1) : ℕ) : ℝ)
      = ((E p).card : ℝ) * (((E p).card : ℝ) - 1) := by
  rw [Nat.cast_mul]
  by_cases h : 1 ≤ (E p).card
  · rw [Nat.cast_sub h]
    norm_num
  · have h0 : (E p).card = 0 := by omega
    rw [h0]
    norm_num

/-- Real-valued pair double count: `f_p (f_p - 1) = 2 · Σ_d #{r | r, r + d ∈ E p}` in `ℝ`. -/
lemma E_pairs_card_eq_two_mul_sum_dist_real (p : ℕ) :
    ((E p).card : ℝ) * (((E p).card : ℝ) - 1) =
      2 * (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card : ℝ) := by
  rw [← cast_card_mul_pred_card p, E_pairs_card_eq_two_mul_sum_dist p]
  simp [Nat.cast_mul, Nat.cast_sum]

/-! ## Theorem 2: `M x` as a distance double sum -/

/-- `M x` re-expressed as a double sum over primes `p ≤ x` and distances `d ∈ [1, p - 2]`. -/
theorem M_eq_two_mul_sum_dist (x : ℕ) :
    M x = 2 * ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      (1 / ((p - 1 : ℕ) : ℝ)) *
        (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card : ℝ) := by
  unfold M
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hq : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have : 0 < p - 1 := by omega
    exact_mod_cast (ne_of_gt this)
  rw [E_pairs_card_eq_two_mul_sum_dist_real p]
  field_simp [hq]

/-! ## Theorem 3: the (vacuous) pair wall -/

/-- The honest negative result: the spacing/pair bound alone gives `M x ≤ Σ_{p ≤ x}
(p - 2)(p - 3) / (p - 1)`, which is `≍ x² / log x`, far from `O(log log x)`. -/
theorem M_le_pair_wall (x : ℕ) :
    M x ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      (((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ) := by
  rw [M_eq_two_mul_sum_dist x]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro p hp
  have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  letI : Fact p.Prime := ⟨hp'⟩
  have hqpos_nat : 0 < p - 1 := by omega
  have hqpos_real : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hqpos_nat
  have hq : ((p - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hqpos_real
  have hsum_le : (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card : ℝ)
      ≤ (∑ d ∈ Finset.Icc 1 (p - 2), ((d - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    exact_mod_cast (E_add_count_le_pred_all p d (Finset.mem_Icc.mp hd).1)
  have hsum_eq : (∑ d ∈ Finset.Icc 1 (p - 2), ((d - 1 : ℕ) : ℝ))
      = (((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / 2 := sum_Icc_one_pred_eq_real p
  have hinner : (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card : ℝ)
      ≤ (((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / 2 :=
    le_trans hsum_le (le_of_eq hsum_eq)
  have hqnonneg : 0 ≤ (1 / ((p - 1 : ℕ) : ℝ)) :=
    le_of_lt (one_div_pos.mpr hqpos_real)
  have hmul : (1 / ((p - 1 : ℕ) : ℝ)) *
        (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card : ℝ)
      ≤ (1 / ((p - 1 : ℕ) : ℝ)) * ((((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / 2) :=
    mul_le_mul_of_nonneg_left hinner hqnonneg
  have hcancel : 2 * ((1 / ((p - 1 : ℕ) : ℝ)) *
        ((((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / 2))
      = (((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ) := by
    field_simp [hq]
  calc
    2 * ((1 / ((p - 1 : ℕ) : ℝ)) *
        (∑ d ∈ Finset.Icc 1 (p - 2), ((E p).filter fun r => r + d ∈ E p).card : ℝ))
        ≤ 2 * ((1 / ((p - 1 : ℕ) : ℝ)) *
            ((((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / 2)) :=
              mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
    _ = (((p - 2 : ℕ) : ℝ) * ((p - 3 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ) := hcancel

end Erdos291
