import Erdos291.GapPolynomial
import Erdos291.MiddlePairStructure
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Erdős #291 — elementary mid-block restrictions

This file records elementary congruence restrictions forced by a middle pair
`(r, p)` in the *intrinsic mid regime* `p > 4r + 1` (the regime relevant for
the hard dyadic blocks `P ∈ (4R, R²]`).

The main result is that in this regime a bad digit `r` has no bad digit at
distance `2`: `r + 2 ∉ E p`.  Together with the existing
`BadSet.not_mem_E_succ` (`r + 1 ∉ E p`), this says the bad digits of a prime
`p` are `3`-separated in the range `r ≤ (p - 1)/4`.

Numeric support (see the round report): among all 10924 middle pairs with
`r ≤ 20000` and `p > 4r + 1`, zero have `r + 2 ∈ E p`; the only pairs with
`r + d ∈ E p` for `d ≤ 20` are `(r,p,d) = (379,9467,3)`, `(382,9467,-3)`,
`(25,109,6)`, `(25,109,19)`.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The harmonic-sum difference: `H_{r+a} - H_r = Σ_{j=r+1}^{r+a} j⁻¹` in `ZMod p`,
provided `r + a < p` so every index is a unit. -/
lemma harmonicSum_sub_eq_sum_inv_Icc (p r a : ℕ) (h : r + a < p) :
    harmonicSum p (r + a) - harmonicSum p r =
      ∑ j ∈ Finset.Icc (r + 1) (r + a), ((j : ZMod p)⁻¹) := by
  unfold harmonicSum
  have hsplit := sum_Icc_split_add (fun j => ((j : ZMod p)⁻¹)) r a
  rw [← hsplit]
  abel

/-- The two-term special case: `H_{r+2} - H_r = (r+1)⁻¹ + (r+2)⁻¹`. -/
lemma harmonicSum_sub_two_eq_inv_add (p r : ℕ) (h : r + 2 < p) :
    harmonicSum p (r + 2) - harmonicSum p r =
      ((r + 1 : ℕ) : ZMod p)⁻¹ + ((r + 2 : ℕ) : ZMod p)⁻¹ := by
  rw [harmonicSum_sub_eq_sum_inv_Icc p r 2 h]
  rw [Finset.sum_Icc_succ_top (a := r + 1) (b := r + 1) (by omega) (fun j => ((j : ZMod p)⁻¹))]
  have hcast : ((r + 1 + 1 : ℕ) : ZMod p) = (r + 2 : ℕ) := by
    rw [show r + 1 + 1 = r + 2 by omega]
  simp [hcast]

/-- If `r` and `r + 2` are both bad digits modulo `p`, then `p ∣ 2r + 3`. -/
lemma p_dvd_two_mul_r_add_three_of_mem_E_add_two (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hr2E : r + 2 ∈ E p) :
    p ∣ 2 * r + 3 := by
  have hp : Nat.Prime p := Fact.out
  have hr2le : r + 2 ≤ p - 1 := by
    unfold E at hr2E
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hr2E).1).2
  have hr_lt : r < p := by omega
  have hr2_lt : r + 2 < p := by omega
  have hsum_r : harmonicSum p r = 0 := harmonicSum_middle_pair_zero p r hrE hr_lt
  have hsum_r2 : harmonicSum p (r + 2) = 0 := harmonicSum_middle_pair_zero p (r + 2) hr2E hr2_lt
  have hsum_mid : ((r + 1 : ℕ) : ZMod p)⁻¹ + ((r + 2 : ℕ) : ZMod p)⁻¹ = 0 := by
    rw [← harmonicSum_sub_two_eq_inv_add p r hr2_lt]
    rw [hsum_r2, hsum_r]
    simp
  have hunit_r1 : ((r + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ r + 1 := (ZMod.natCast_eq_zero_iff (r + 1) p).mp hz
    have hle : p ≤ r + 1 := Nat.le_of_dvd (by omega : 1 ≤ r + 1) hdvd
    omega
  have hunit_r2 : ((r + 2 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ r + 2 := (ZMod.natCast_eq_zero_iff (r + 2) p).mp hz
    have hle : p ≤ r + 2 := Nat.le_of_dvd (by omega : 1 ≤ r + 2) hdvd
    omega
  have hmul : (((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p)) *
        (((r + 1 : ℕ) : ZMod p)⁻¹ + ((r + 2 : ℕ) : ZMod p)⁻¹) = 0 := by
    rw [hsum_mid]; simp
  have hexp : (((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p)) *
        (((r + 1 : ℕ) : ZMod p)⁻¹ + ((r + 2 : ℕ) : ZMod p)⁻¹)
        = ((r + 2 : ℕ) : ZMod p) + ((r + 1 : ℕ) : ZMod p) := by
    have h1 : ((r + 1 : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹ = 1 :=
      mul_inv_cancel₀ hunit_r1
    have h2 : ((r + 2 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p)⁻¹ = 1 :=
      mul_inv_cancel₀ hunit_r2
    calc
      (((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p)) *
          (((r + 1 : ℕ) : ZMod p)⁻¹ + ((r + 2 : ℕ) : ZMod p)⁻¹)
          = ((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹
              + ((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p)⁻¹ := by
              rw [mul_add]
      _ = ((r + 2 : ℕ) : ZMod p) + ((r + 1 : ℕ) : ZMod p) := by
              rw [show ((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹
                  = ((r + 2 : ℕ) : ZMod p) by
                    rw [mul_assoc, mul_comm ((r + 2 : ℕ) : ZMod p) ((r + 1 : ℕ) : ZMod p)⁻¹,
                      ← mul_assoc, h1, one_mul]]
              rw [show ((r + 1 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p) * ((r + 2 : ℕ) : ZMod p)⁻¹
                  = ((r + 1 : ℕ) : ZMod p) by
                    rw [mul_assoc, h2, mul_one]]
  have hcast : ((2 * r + 3 : ℕ) : ZMod p) = 0 := by
    have hsum_cast : ((r + 2 : ℕ) : ZMod p) + ((r + 1 : ℕ) : ZMod p) = 0 := by
      rw [← hexp, hmul]
    have hcomm : ((r + 2 : ℕ) : ZMod p) + ((r + 1 : ℕ) : ZMod p)
        = ((2 * r + 3 : ℕ) : ZMod p) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    rw [← hcomm, hsum_cast]
  exact (ZMod.natCast_eq_zero_iff (2 * r + 3) p).mp hcast

/-- If `r` and `r + 2` are both bad digits modulo `p`, then in fact `p = 2r + 3`
(the gap-2 case). -/
lemma p_eq_two_mul_r_add_three_of_mem_E_add_two (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hr2E : r + 2 ∈ E p) :
    p = 2 * r + 3 := by
  have hp : Nat.Prime p := Fact.out
  have hr2le : r + 2 ≤ p - 1 := by
    unfold E at hr2E
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hr2E).1).2
  have hdvd : p ∣ 2 * r + 3 := p_dvd_two_mul_r_add_three_of_mem_E_add_two p r hrE hr2E
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hknot
    have hk0 : k = 0 := by omega
    rw [hk0, mul_zero] at hk
    omega
  have hp_ge : r + 3 ≤ p := by omega
  by_cases hk1 : k = 1
  · subst k
    simpa using hk.symm
  · have hkge : 2 ≤ k := by omega
    have hmul : p * 2 ≤ p * k := Nat.mul_le_mul_left p hkge
    have htwomul : 2 * p ≤ 2 * r + 3 := by
      rw [hk]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    omega

/-- If `r ∈ E p` and `2r + 3 < p`, then `r + 2` is not a bad digit. -/
lemma not_mem_E_add_two_of_two_mul_r_add_three_lt (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (h : 2 * r + 3 < p) :
    r + 2 ∉ E p := by
  intro hr2E
  have hp_eq : p = 2 * r + 3 := p_eq_two_mul_r_add_three_of_mem_E_add_two p r hrE hr2E
  omega

/-- **Intrinsic mid-regime restriction.**  For a middle pair with `p > 4r + 1`, the
digit `r + 2` is never bad.  Hence (with `not_mem_E_succ`) the bad digits in the
intrinsic mid range are `3`-separated. -/
lemma not_mem_E_add_two_of_four_mul_r_add_one_lt (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    r + 2 ∉ E p := by
  have hr1 : 1 ≤ r := by
    unfold E at hrE
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).1
  have h : 2 * r + 3 < p := by omega
  exact not_mem_E_add_two_of_two_mul_r_add_three_lt p r hrE h

/-- The same restriction for `r - 2`: in the intrinsic mid regime, `r - 2` is not bad
(when it is a valid digit, `4 ≤ r`). -/
lemma not_mem_E_sub_two_of_four_mul_r_add_one_lt (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hr4 : 4 ≤ r) (hmid : 4 * r + 1 < p) :
    r - 2 ∉ E p := by
  have hmid' : 4 * (r - 2) + 1 < p := by omega
  intro hsub
  have hsubE : r - 2 ∈ E p := hsub
  have hnot := not_mem_E_add_two_of_four_mul_r_add_one_lt p (r - 2) hsubE hmid'
  have hcast : r - 2 + 2 = r := by omega
  have hnot' : r ∉ E p := by simpa [hcast] using hnot
  exact hnot' hrE

/-- A middle pair in the intrinsic mid regime has no other bad digit among
`{r - 2, r - 1, r + 1, r + 2}` (where the negative shifts are valid). -/
lemma no_bad_digit_within_two_of_four_mul_r_add_one_lt (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (r + 1 ∉ E p) ∧ (r + 2 ∉ E p) ∧
      (3 ≤ r → r - 1 ∉ E p) ∧ (4 ≤ r → r - 2 ∉ E p) := by
  have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact not_mem_E_succ p r hp2 hrE
  · exact not_mem_E_add_two_of_four_mul_r_add_one_lt p r hrE hmid
  · intro hr3 hsub
    have hr1E : r - 1 ∈ E p := hsub
    have hle : (r - 1) + 1 = r := by omega
    have hnot := not_mem_E_succ p (r - 1) hp2 hr1E
    have hnot' : r ∉ E p := by simpa [hle] using hnot
    exact hnot' hrE
  · intro hr4
    exact not_mem_E_sub_two_of_four_mul_r_add_one_lt p r hrE hr4 hmid

/-- The harmonic sum is symmetric: `H_{2r} = H_{p-1-2r}` in `ZMod p` for an odd
prime `p`.  For a middle pair this says `H_{2r} = H_{2t}` with
`t = (p - 1 - 2r) / 2`. -/
lemma harmonicSum_two_mul_r_eq_harmonicSum_pred_sub_two_mul_r (p r : ℕ) [Fact p.Prime]
    (hp3 : 3 ≤ p) (h2rle : 2 * r ≤ p - 1) :
    harmonicSum p (2 * r) = harmonicSum p (p - 1 - 2 * r) := by
  unfold harmonicSum
  exact (sum_inv_Icc_sub_eq_sum_inv p (2 * r) hp3 h2rle).symm

/-- For a middle pair, `H_{2r} = H_{2t}` with `t = (p - 1 - 2r) / 2`. -/
lemma harmonicSum_two_mul_r_eq_harmonicSum_two_mul_t_of_middle_pair
    (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    harmonicSum p (2 * r) = harmonicSum p (2 * ((p - 1 - 2 * r) / 2)) := by
  have h2rle : 2 * r ≤ p - 1 := by omega
  have hs := harmonicSum_two_mul_r_eq_harmonicSum_pred_sub_two_mul_r p r hp h2rle
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  have hdiv : 2 ∣ p - 1 - 2 * r := by
    rcases hodd with ⟨m, hm⟩
    use m - r
    omega
  have hmul : 2 * ((p - 1 - 2 * r) / 2) = p - 1 - 2 * r := Nat.mul_div_cancel' hdiv
  simpa [hmul] using hs

end

end Erdos291
