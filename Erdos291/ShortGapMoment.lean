import Erdos291.SecondMomentDoubleCount
import Erdos291.BadSetGrowth
import Erdos291.SecondMoment
import Erdos291.MertensUpper
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Lemmas

/-!
# Erdős #291 — the unconditional short-gap second moment

Recall that the second factorial moment `M x = Σ_{p ≤ x} f_p (f_p - 1) / (p - 1)` re-expresses
(by `M_eq_two_mul_sum_dist`) as a sum over *distances* `d` of the number of bad-residue pairs
`{r, r + d}` with `r, r + d ∈ E p`:

  `M x = 2 · Σ_{p ≤ x} (1 / (p - 1)) · Σ_{d = 1}^{p - 2} #{r | r, r + d ∈ E p}`.

This file isolates the *short-gap* part of `M x`, namely the contribution of the distances
`d ≤ D` for a cutoff `D`:

  `MleD x D = 2 · Σ_{p ≤ x} (1 / (p - 1)) · Σ_{d = 1}^{min D (p - 2)} #{r | r, r + d ∈ E p}`.

The spacing bound `#{r | r, r + d ∈ E p} ≤ d - 1` (`E_add_count_le_pred_all`) turns the inner
distance sum into the arithmetic series `Σ_{d = 1}^{D} (d - 1) = D (D - 1) / 2`, so that

  `MleD x D ≤ D² · Σ_{p ≤ x} 1 / (p - 1)`,

and hence — unconditionally, by Mertens' bound `Σ_{p ≤ x} 1 / (p - 1) = O(log log x)` —

  `MleD x D ≤ D² · C · (1 + log log x)`.

This is a *genuine* region removal: the pairs at distance `d ≤ D` contribute `O(D² log log x)`,
which is `o(log x)` once `D = o(√(log x / log log x))` (in particular for `D = (log x)^{1/3}`).

There are no unproved declarations in this file.
-/

open scoped BigOperators

namespace Erdos291

open Filter

/-! ## The short-gap second moment -/

/-- The short-gap second moment: the part of `M x` coming from bad-residue pairs at distance
`d ≤ D` (clipped to the valid range `d ≤ p - 2`). -/
noncomputable def MleD (x D : ℕ) : ℝ :=
  2 * ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
    (1 / ((p - 1 : ℕ) : ℝ)) *
      (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ)

/-! ## The arithmetic-series identity -/

/-- `2 · Σ_{d = 1}^{D} (d - 1) = D (D - 1)`, from `Σ_{d = 1}^{D} (d - 1) = D (D - 1) / 2`
(`sum_Icc_one_pred_eq`) and the divisibility `2 ∣ D (D - 1)`. -/
lemma two_mul_sum_Icc_one_pred (D : ℕ) :
    2 * (∑ d ∈ Finset.Icc 1 D, (d - 1)) = D * (D - 1) := by
  have h := sum_Icc_one_pred_eq (D + 1)
  have h1 : (D + 1) - 1 = D := by omega
  have h2 : (D + 1) - 2 = D - 1 := by omega
  rw [h1, h2] at h
  rw [h]
  exact Nat.mul_div_cancel' (two_dvd_mul_pred D)

/-- For a prime `p`, `2 · Σ_{d = 1}^{min D (p - 2)} #{r | r, r + d ∈ E p} ≤ D²`: the spacing bound
bounds each fibre by `d - 1`, the range `[1, min D (p - 2)]` embeds into `[1, D]`, and
`2 · Σ_{d = 1}^{D} (d - 1) = D (D - 1) ≤ D²`. -/
lemma two_mul_sum_filter_card_le_nat (p D : ℕ) [Fact p.Prime] :
    2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card)
      ≤ D ^ 2 := by
  classical
  have hstep1 : (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card)
      ≤ (∑ d ∈ Finset.Icc 1 (min D (p - 2)), (d - 1)) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    exact E_add_count_le_pred_all p d (Finset.mem_Icc.mp hd).1
  have hsub : Finset.Icc 1 (min D (p - 2)) ⊆ Finset.Icc 1 D := by
    intro d hd
    rw [Finset.mem_Icc]
    have hd' : 1 ≤ d ∧ d ≤ min D (p - 2) := Finset.mem_Icc.mp hd
    exact ⟨hd'.1, le_trans hd'.2 (min_le_left _ _)⟩
  have hstep2 : (∑ d ∈ Finset.Icc 1 (min D (p - 2)), (d - 1))
      ≤ (∑ d ∈ Finset.Icc 1 D, (d - 1)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro d _ _; omega)
  have hstep3 : 2 * (∑ d ∈ Finset.Icc 1 D, (d - 1)) = D * (D - 1) := two_mul_sum_Icc_one_pred D
  have hstep4 : D * (D - 1) ≤ D ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left D (by omega : D - 1 ≤ D)
  calc
    2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card)
        ≤ 2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)), (d - 1)) := Nat.mul_le_mul_left 2 hstep1
    _ ≤ 2 * (∑ d ∈ Finset.Icc 1 D, (d - 1)) := Nat.mul_le_mul_left 2 hstep2
    _ = D * (D - 1) := hstep3
    _ ≤ D ^ 2 := hstep4

/-! ## Theorem 1: the core unconditional bound -/

/-- Pointwise: `2 · (1 / (p - 1)) · Σ_{d ≤ D} #{r | r, r + d ∈ E p} ≤ D² / (p - 1)`. -/
lemma two_mul_inv_pred_mul_sum_filter_le (p D : ℕ) [Fact p.Prime] :
    2 * ((1 / ((p - 1 : ℕ) : ℝ)) *
        (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ))
      ≤ (D : ℝ) ^ 2 * (1 / ((p - 1 : ℕ) : ℝ)) := by
  have hqpos_nat : 0 < p - 1 := by
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  have hqpos_real : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hqpos_nat
  have hqnonneg : 0 ≤ (1 / ((p - 1 : ℕ) : ℝ)) := le_of_lt (one_div_pos.mpr hqpos_real)
  have hnat := two_mul_sum_filter_card_le_nat p D
  have hreal : 2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)),
      ((E p).filter fun r => r + d ∈ E p).card : ℝ) ≤ (D : ℝ) ^ 2 := by
    have hcast : ((2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)),
        ((E p).filter fun r => r + d ∈ E p).card) : ℕ) : ℝ) ≤ ((D ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow] using hcast
  have hmul : (1 / ((p - 1 : ℕ) : ℝ)) *
      (2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ))
        ≤ (1 / ((p - 1 : ℕ) : ℝ)) * (D : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hreal hqnonneg
  calc
    2 * ((1 / ((p - 1 : ℕ) : ℝ)) *
        (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ))
        = (1 / ((p - 1 : ℕ) : ℝ)) *
            (2 * (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ)) := by
          ring
    _ ≤ (1 / ((p - 1 : ℕ) : ℝ)) * (D : ℝ) ^ 2 := hmul
    _ = (D : ℝ) ^ 2 * (1 / ((p - 1 : ℕ) : ℝ)) := by ring

/-- **The core unconditional bound.** The short-gap part `MleD x D` of the second moment is at
most `D² · Σ_{p ≤ x} 1 / (p - 1)`. -/
theorem MleD_le (x D : ℕ) :
    MleD x D ≤ (D : ℝ)^2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, 1 / ((p - 1 : ℕ) : ℝ)) := by
  unfold MleD
  calc
    2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
          (1 / ((p - 1 : ℕ) : ℝ)) *
            (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ))
        = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
            2 * ((1 / ((p - 1 : ℕ) : ℝ)) *
              (∑ d ∈ Finset.Icc 1 (min D (p - 2)), ((E p).filter fun r => r + d ∈ E p).card : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
          (D : ℝ) ^ 2 * (1 / ((p - 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
          let _ : Fact p.Prime := ⟨hp'⟩
          exact two_mul_inv_pred_mul_sum_filter_le p D
    _ = (D : ℝ) ^ 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, 1 / ((p - 1 : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]

/-! ## Theorem 2: the log-log bound -/

/-- **The unconditional log-log bound.** For every cutoff `D`, there is a constant `C` (the
Mertens constant from `sum_inv_pred_le_loglog`) such that eventually
`MleD x D ≤ D² · C · (1 + log log x)`. In particular the short-gap part is `o(log x)` whenever
`D² = o(log x / log log x)`. -/
theorem MleD_le_loglog (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      MleD x D ≤ (D : ℝ) ^ 2 * C * (1 + Real.log (Real.log (x : ℝ))) := by
  rcases sum_inv_pred_le_loglog with ⟨C₀, hC0pos, hC₀⟩
  refine ⟨C₀, hC0pos, ?_⟩
  filter_upwards [hC₀] with x hx
  calc
    MleD x D ≤ (D : ℝ) ^ 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, 1 / ((p - 1 : ℕ) : ℝ)) :=
        MleD_le x D
    _ ≤ (D : ℝ) ^ 2 * (C₀ * (1 + Real.log (Real.log (x : ℝ)))) :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg (D : ℝ))
    _ = (D : ℝ) ^ 2 * C₀ * (1 + Real.log (Real.log (x : ℝ))) := by ring

end Erdos291
