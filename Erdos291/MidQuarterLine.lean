import Erdos291.MidDuplication
import Erdos291.MidResultant
import Erdos291.MidAttackLine3
import Erdos291.OddHarmonicWalk
import Erdos291.Eisenstein
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Erdős #291 — the quarter-point line and the six roots of `Q_r`

This file works out two consequences of the duplication structure from
`MidDuplication`, both in `ZMod p`.

## 1. The dangerous line `p = 4r + 5`

For `p = 4m + 1` one has

    `H_m = -3 · q_p(2)  (mod p)`,

and therefore, writing `r = m - 1` (so that `p = 4r + 5`),

    `H_r = 0  ↔  3 · q_p(2) = 4  (mod p)`.

The derivation is purely elementary:

* the even/odd split gives `H_{2m} = (1/2) H_m + C_m` where `C_t` is the
  odd-harmonic walk;
* the tail identity `C_{2m} - C_m = -(1/2) H_m` comes from the reflection
  `2(m-k)+1 = p - 2k`;
* `C_{2m} = q_p(2)` (`oddWalk_mid_eq_fermatQuotient`) and
  `H_{2m} = -2 q_p(2)` (`eisenstein_congruence`) close the system.

This is the elementary shadow of the logarithmic derivative of the duplication
formula `L_r(-1/2) = 2 H_{2r} - H_r` at `X = 0`.

## 2. The six roots of `Q_r`

If `p > 4r + 1` and `H_r = H_{2r} = 0` in `ZMod p`, then `Q p r` vanishes at
the six pairwise distinct points

    `0,  r,  -r-1,  -2r-1,  -1/2,  -r-1/2`,

whence the sextic

    `D_mod p r = X(X-r)(X+r+1)(X+2r+1)(2X+1)(2X+2r+1)`

divides `Q p r`.  This generalizes the quartic `A_poly` divisibility of
`MidTwoHalves` (which needs only `H_{2r} = 0` and `r ∈ E p`); here the extra
two roots come from the duplication/quarter structure.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

open Polynomial

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Elementary recursions for `harmonicSum` -/

/-- Appending one term: `H_{n+1} = H_n + (n+1)⁻¹`. -/
lemma harmonicSum_succ (p n : ℕ) :
    harmonicSum p (n + 1) = harmonicSum p n + ((n + 1 : ℕ) : ZMod p)⁻¹ := by
  rw [harmonicSum, harmonicSum]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

/-- `H_m = H_{m-1} + m⁻¹` for `1 ≤ m`. -/
lemma harmonicSum_eq_pred_add_inv (p m : ℕ) (hm : 1 ≤ m) :
    harmonicSum p m = harmonicSum p (m - 1) + ((m : ℕ) : ZMod p)⁻¹ := by
  have hm_eq : m = (m - 1) + 1 := by omega
  rw [hm_eq, harmonicSum_succ p (m - 1)]
  rw [Nat.sub_add_cancel hm]

/-! ## The even/odd split of `H_{2m}` -/

/-- Splitting `H_{2m}` into even and odd indices:
`H_{2m} = (1/2) H_m + C_m`, where `C_m = oddWalk p m`. -/
lemma harmonicSum_two_mul_eq_half_add_oddWalk (p m : ℕ) [Fact p.Prime] :
    harmonicSum p (2 * m) =
      (2 : ZMod p)⁻¹ * harmonicSum p m + oddWalk p m := by
  have hsplit := sum_Icc_one_mul_two m (fun j => ((j : ZMod p)⁻¹))
  have heven : (∑ i ∈ Finset.Icc 1 m, ((2 * i : ℕ) : ZMod p)⁻¹) =
      (2 : ZMod p)⁻¹ * (∑ i ∈ Finset.Icc 1 m, ((i : ℕ) : ZMod p)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_mul, mul_inv_rev, mul_comm]
    simp
  rw [harmonicSum, harmonicSum, hsplit, oddWalk, heven]
  ring

/-- The integral logarithmic-derivative shadow of duplication at `X = 0`:
`2 · H_{2r} = H_r + 2 · C_r`. -/
lemma two_mul_harmonicSum_two_mul_eq_harmonicSum_add_two_mul_oddWalk
    (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (2 : ZMod p) * harmonicSum p (2 * r) =
      harmonicSum p r + (2 : ZMod p) * oddWalk p r := by
  have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp
  calc
    (2 : ZMod p) * harmonicSum p (2 * r)
        = (2 : ZMod p) * ((2 : ZMod p)⁻¹ * harmonicSum p r + oddWalk p r) := by
            rw [harmonicSum_two_mul_eq_half_add_oddWalk p r]
    _ = (2 : ZMod p) * ((2 : ZMod p)⁻¹ * harmonicSum p r) +
          (2 : ZMod p) * oddWalk p r := by ring
    _ = harmonicSum p r + (2 : ZMod p) * oddWalk p r := by
            rw [← mul_assoc, htwo, one_mul]

/-! ## The quarter harmonic sum `H_m = -3 q_p(2)` for `p = 4m + 1` -/

/-- The inverse of `m` is `-4` when `p = 4m + 1`. -/
lemma inv_m_eq_neg_four_of_p_eq_four_mul_add_one (p m : ℕ) [Fact p.Prime]
    (hp : p = 4 * m + 1) : (m : ZMod p)⁻¹ = (-4 : ZMod p) := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp5 : 5 ≤ p := by omega
  have hmpos : 0 < m := by omega
  have h4m : (4 : ZMod p) * (m : ZMod p) = (-1 : ZMod p) := by
    have hcast : ((4 * m : ℕ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
      rw [show 4 * m = p - 1 by omega]
    rw [Nat.cast_mul] at hcast
    have hp1 : ((p - 1 : ℕ) : ZMod p) = (-1 : ZMod p) := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      simp
    exact hcast.trans hp1
  have hm_ne : (m : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ m := (ZMod.natCast_eq_zero_iff m p).mp hz
    have hle : p ≤ m := Nat.le_of_dvd hmpos hdvd
    omega
  have hmunit : IsUnit (m : ZMod p) := hm_ne.isUnit
  have h4eq : (4 : ZMod p) = -((m : ZMod p)⁻¹) := by
    calc
      (4 : ZMod p) = (4 : ZMod p) * 1 := by rw [mul_one]
      _ = (4 : ZMod p) * ((m : ZMod p) * (m : ZMod p)⁻¹) := by
            rw [ZMod.mul_inv_of_unit (m : ZMod p)]
            exact hmunit
      _ = ((4 : ZMod p) * (m : ZMod p)) * (m : ZMod p)⁻¹ := by ring
      _ = (-1 : ZMod p) * (m : ZMod p)⁻¹ := by rw [h4m]
      _ = -((m : ZMod p)⁻¹) := by simp
  have hneg := congrArg Neg.neg h4eq
  rw [neg_neg] at hneg
  exact hneg.symm

/-- The quarter harmonic sum: for `p = 4m + 1`,
`H_m = -3 · q_p(2)` in `ZMod p`. -/
theorem harmonicSum_quarter_eq_neg_three_mul_fermatQuotient
    (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 1) :
    harmonicSum p m = -(3 : ZMod p) * (fermatQuotient p : ZMod p) := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp5 : 5 ≤ p := by omega
  have hp3 : 3 ≤ p := by omega
  have hmpos : 0 < m := by omega
  have hhalf : (p - 1) / 2 = 2 * m := by omega
  have hH2m : harmonicSum p (2 * m) =
      -((2 : ZMod p)) * (fermatQuotient p : ZMod p) := by
    simpa [harmonicSum, hhalf] using (eisenstein_congruence p hp3)
  have hwalk : oddWalk p (2 * m) = (fermatQuotient p : ZMod p) := by
    simpa [hhalf] using oddWalk_mid_eq_fermatQuotient p hp3
  have hsplit : harmonicSum p (2 * m) =
      (2 : ZMod p)⁻¹ * harmonicSum p m + oddWalk p m :=
    harmonicSum_two_mul_eq_half_add_oddWalk p m
  have hmle : m ≤ (p - 1) / 2 := by omega
  have hshift := oddWalk_sub_eq_neg_half_H p m hp3 hmle
  have hshift' : oddWalk p (2 * m) - oddWalk p m =
      -((2 : ZMod p)⁻¹) * harmonicSum p m := by
    have hsub : (p - 1) / 2 - m = m := by omega
    rw [hsub, hhalf] at hshift
    rw [← harmonicSum_eq_sum_inv p m] at hshift
    exact hshift
  have hw1 : oddWalk p m =
      harmonicSum p (2 * m) - (2 : ZMod p)⁻¹ * harmonicSum p m := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact hsplit.symm
  have hw2 : oddWalk p (2 * m) =
      oddWalk p m - (2 : ZMod p)⁻¹ * harmonicSum p m := by
    rw [sub_eq_iff_eq_add] at hshift'
    rw [hshift', add_comm]
    simp [sub_eq_add_neg]
  have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp3
  have hhalfsum : (2 : ZMod p)⁻¹ * harmonicSum p m +
      (2 : ZMod p)⁻¹ * harmonicSum p m = harmonicSum p m := by
    have h2ne : (2 : ZMod p) ≠ 0 := (two_isUnit p hp3).ne_zero
    field_simp [h2ne]
    ring
  have hmain : (fermatQuotient p : ZMod p) =
      -((2 : ZMod p)) * (fermatQuotient p : ZMod p) - harmonicSum p m := by
    calc
      (fermatQuotient p : ZMod p) = oddWalk p (2 * m) := by exact hwalk.symm
      _ = oddWalk p m - (2 : ZMod p)⁻¹ * harmonicSum p m := hw2
      _ = (harmonicSum p (2 * m) - (2 : ZMod p)⁻¹ * harmonicSum p m) -
            (2 : ZMod p)⁻¹ * harmonicSum p m := by rw [hw1]
      _ = harmonicSum p (2 * m) -
            ((2 : ZMod p)⁻¹ * harmonicSum p m +
              (2 : ZMod p)⁻¹ * harmonicSum p m) := by ring
      _ = harmonicSum p (2 * m) - harmonicSum p m := by rw [hhalfsum]
      _ = -((2 : ZMod p)) * (fermatQuotient p : ZMod p) - harmonicSum p m := by
            rw [hH2m]
  have hmain2 : (fermatQuotient p : ZMod p) + harmonicSum p m =
      -((2 : ZMod p)) * (fermatQuotient p : ZMod p) :=
    eq_sub_iff_add_eq.mp hmain
  have hH : harmonicSum p m =
      -((2 : ZMod p)) * (fermatQuotient p : ZMod p) - (fermatQuotient p : ZMod p) := by
    rw [eq_sub_iff_add_eq]
    rw [add_comm]
    exact hmain2
  rw [hH]
  ring

/-- For `p = 4m + 1`: `H_{m-1} = 4 - 3 · q_p(2)` in `ZMod p`. -/
theorem harmonicSum_quarter_pred_eq_four_sub_three_mul_fermatQuotient
    (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 1) :
    harmonicSum p (m - 1) = (4 : ZMod p) - (3 : ZMod p) * (fermatQuotient p : ZMod p) := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hm1 : 1 ≤ m := by omega
  have hmain := harmonicSum_quarter_eq_neg_three_mul_fermatQuotient p m hp
  have hminv := inv_m_eq_neg_four_of_p_eq_four_mul_add_one p m hp
  have hpred : harmonicSum p (m - 1) = harmonicSum p m - (m : ZMod p)⁻¹ := by
    rw [eq_comm, sub_eq_iff_eq_add]
    exact harmonicSum_eq_pred_add_inv p m hm1
  calc
    harmonicSum p (m - 1) = harmonicSum p m - (m : ZMod p)⁻¹ := hpred
    _ = (-(3 : ZMod p) * (fermatQuotient p : ZMod p)) - (-(4 : ZMod p)) := by
            rw [hmain, hminv]
    _ = (4 : ZMod p) - (3 : ZMod p) * (fermatQuotient p : ZMod p) := by ring

/-- For `p = 4m + 1`: `H_{m-1} = 0 ↔ 3 · q_p(2) = 4` in `ZMod p`. -/
theorem harmonicSum_quarter_pred_eq_zero_iff_three_fermatQuotient_eq_four
    (p m : ℕ) [Fact p.Prime] (hp : p = 4 * m + 1) :
    harmonicSum p (m - 1) = 0 ↔
      (3 : ZMod p) * (fermatQuotient p : ZMod p) = (4 : ZMod p) := by
  rw [harmonicSum_quarter_pred_eq_four_sub_three_mul_fermatQuotient p m hp]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    rw [h]
    ring

/-- The dangerous-line equivalence: for `p = 4r + 5`,
`H_r = 0 ↔ 3 · q_p(2) = 4` in `ZMod p`. -/
theorem harmonicSum_eq_zero_iff_three_fermatQuotient_eq_four_of_p_eq_four_r_add_five
    (p r : ℕ) [Fact p.Prime] (hp : p = 4 * r + 5) :
    harmonicSum p r = 0 ↔
      (3 : ZMod p) * (fermatQuotient p : ZMod p) = (4 : ZMod p) := by
  let m : ℕ := r + 1
  have hp' : p = 4 * m + 1 := by
    dsimp [m]
    omega
  have h := harmonicSum_quarter_pred_eq_zero_iff_three_fermatQuotient_eq_four p m hp'
  have hm1 : m - 1 = r := by
    dsimp [m]
  simpa [hm1] using h

/-! ## Evaluation and reflection tools for the six roots -/

/-- A natural number in `[1, p)` is nonzero in `ZMod p`. -/
private lemma cast_ne_zero_of_lt_prime (p n : ℕ) [Fact p.Prime]
    (hn1 : 1 ≤ n) (hnlt : n < p) : (n : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
  have hle : p ≤ n := Nat.le_of_dvd hn1 hdvd
  omega

/-- Evaluation of `Q p d` at an arbitrary field point as the erased-product sum. -/
lemma eval_Q_eq_sum_prod_erase_of_eval (p d : ℕ) (a : ZMod p) :
    Polynomial.eval a (Q p d) =
      ∑ i ∈ Finset.Icc 1 d, ∏ j ∈ (Finset.Icc 1 d).erase i, (a + (j : ZMod p)) := by
  rw [Q, P, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.derivative_X_add_C,
    Polynomial.eval_one, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- Evaluation of `P p d` as a product of linear values. -/
lemma eval_P_eq_prod (p d : ℕ) (a : ZMod p) :
    Polynomial.eval a (P p d) = ∏ j ∈ Finset.Icc 1 d, (a + (j : ZMod p)) := by
  rw [P]
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- `-1/2 + j = (2j - 1) / 2` in `ZMod p`. -/
lemma neg_inv_two_add_eq_pred_two_mul_mul_inv_two (p j : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hj1 : 1 ≤ j) :
    (-(2 : ZMod p)⁻¹) + (j : ZMod p) =
      ((2 * j - 1 : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
  have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp
  calc
    (-(2 : ZMod p)⁻¹) + (j : ZMod p) = (j : ZMod p) - (2 : ZMod p)⁻¹ := by ring
    _ = (j : ZMod p) * 1 - (2 : ZMod p)⁻¹ := by rw [mul_one]
    _ = (j : ZMod p) * ((2 : ZMod p) * (2 : ZMod p)⁻¹) - (2 : ZMod p)⁻¹ := by
            rw [htwo]
    _ = (2 : ZMod p) * (j : ZMod p) * (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹ := by ring
    _ = (((2 * j : ℕ) : ZMod p) - 1) * (2 : ZMod p)⁻¹ := by
            rw [Nat.cast_mul]
            ring
    _ = ((2 * j - 1 : ℕ) : ZMod p) * (2 : ZMod p)⁻¹ := by
            rw [Nat.cast_sub (by omega : 1 ≤ 2 * j)]
            norm_num

/-- `-1/2 + j` is a unit whenever `2j - 1 < p`. -/
lemma isUnit_neg_inv_two_add (p j : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hj1 : 1 ≤ j) (hjlt : 2 * j - 1 < p) :
    IsUnit ((-(2 : ZMod p)⁻¹) + (j : ZMod p)) := by
  rw [neg_inv_two_add_eq_pred_two_mul_mul_inv_two p j hp hj1]
  apply IsUnit.mul
  · have hpos : 1 ≤ 2 * j - 1 := by omega
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    intro hdvd
    exact (not_lt_of_ge (Nat.le_of_dvd hpos hdvd)) hjlt
  · exact (two_isUnit p hp).inv

/-- `(-1/2 + j)⁻¹ = 2 · (2j - 1)⁻¹` in `ZMod p`. -/
lemma inv_neg_inv_two_add_eq_two_mul_inv_pred_two_mul (p j : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hj1 : 1 ≤ j) :
    ((-(2 : ZMod p)⁻¹) + (j : ZMod p))⁻¹ =
      (2 : ZMod p) * ((2 * j - 1 : ℕ) : ZMod p)⁻¹ := by
  rw [neg_inv_two_add_eq_pred_two_mul_mul_inv_two p j hp hj1]
  rw [mul_inv_rev, inv_inv]
/-- Reindexing `Icc 1 r` to `range r` for the odd inverses. -/
lemma sum_inv_pred_two_mul_Icc_eq_oddWalk (p r : ℕ) :
    (∑ i ∈ Finset.Icc 1 r, ((2 * i - 1 : ℕ) : ZMod p)⁻¹) = oddWalk p r := by
  rw [oddWalk]
  refine Finset.sum_bij (fun i _ => i - 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range]
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ r := Finset.mem_Icc.mp hi₁
    have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ r := Finset.mem_Icc.mp hi₂
    omega
  · intro j hj
    have hj' : j < r := Finset.mem_range.mp hj
    refine ⟨j + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    have hnat : 2 * i - 1 = 2 * (i - 1) + 1 := by omega
    rw [hnat]

/-- At `X = -1/2`, the logarithmic derivative of `P_r` is twice the odd walk:
`Q_r(-1/2) = P_r(-1/2) · (2 · C_r)`. -/
lemma eval_Q_neg_inv_two_eq_eval_P_neg_inv_two_mul_two_mul_oddWalk
    (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (h2r : 2 * r < p) :
    Polynomial.eval (-(2 : ZMod p)⁻¹) (Q p r) =
      Polynomial.eval (-(2 : ZMod p)⁻¹) (P p r) * ((2 : ZMod p) * oddWalk p r) := by
  let a : ZMod p := -(2 : ZMod p)⁻¹
  have hunits : ∀ i ∈ Finset.Icc 1 r, IsUnit (a + (i : ZMod p)) := by
    intro i hi
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    have hjlt : 2 * i - 1 < p := by omega
    dsimp [a]
    exact isUnit_neg_inv_two_add p i hp hi'.1 hjlt
  calc
    Polynomial.eval (-(2 : ZMod p)⁻¹) (Q p r)
        = ∑ i ∈ Finset.Icc 1 r,
            ∏ j ∈ (Finset.Icc 1 r).erase i, ((-(2 : ZMod p)⁻¹) + (j : ZMod p)) := by
              rw [eval_Q_eq_sum_prod_erase_of_eval p r (-(2 : ZMod p)⁻¹)]
    _ = (∏ j ∈ Finset.Icc 1 r, ((-(2 : ZMod p)⁻¹) + (j : ZMod p))) *
          (∑ i ∈ Finset.Icc 1 r, ((-(2 : ZMod p)⁻¹) + (i : ZMod p))⁻¹) := by
              dsimp [a] at hunits
              rw [sum_prod_erase_eq_mul_inv (Finset.Icc 1 r)
                (fun i => (-(2 : ZMod p)⁻¹) + (i : ZMod p)) hunits]
    _ = Polynomial.eval (-(2 : ZMod p)⁻¹) (P p r) *
          (∑ i ∈ Finset.Icc 1 r, ((-(2 : ZMod p)⁻¹) + (i : ZMod p))⁻¹) := by
              rw [eval_P_eq_prod]
    _ = Polynomial.eval (-(2 : ZMod p)⁻¹) (P p r) * ((2 : ZMod p) * oddWalk p r) := by
              have hsum_inv : (∑ i ∈ Finset.Icc 1 r,
                  ((-(2 : ZMod p)⁻¹) + (i : ZMod p))⁻¹) =
                  (2 : ZMod p) * oddWalk p r := by
                calc
                  (∑ i ∈ Finset.Icc 1 r, ((-(2 : ZMod p)⁻¹) + (i : ZMod p))⁻¹)
                      = ∑ i ∈ Finset.Icc 1 r,
                          (2 : ZMod p) * ((2 * i - 1 : ℕ) : ZMod p)⁻¹ := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        have hi' := Finset.mem_Icc.mp hi
                        rw [inv_neg_inv_two_add_eq_two_mul_inv_pred_two_mul p i hp hi'.1]
                  _ = (2 : ZMod p) *
                      (∑ i ∈ Finset.Icc 1 r, ((2 * i - 1 : ℕ) : ZMod p)⁻¹) := by
                        rw [Finset.mul_sum]
                  _ = (2 : ZMod p) * oddWalk p r := by
                        rw [sum_inv_pred_two_mul_Icc_eq_oddWalk p r]
              rw [hsum_inv]

/-! ## Reflection of `Q p d` -/

/-- The reduction mod `p` of the reflection symmetry of `Qd`. -/
lemma Q_comp_neg_X_sub_C_add_one (p d : ℕ) [Fact p.Prime] :
    (Q p d).comp (-Polynomial.X - Polynomial.C ((d + 1 : ℕ) : ZMod p)) =
      Polynomial.C (-1 : ZMod p) ^ (d + 1) * Q p d := by
  have h := Qd_comp_neg_X_sub_C_add_one d
  have hmap := congrArg (fun f : Polynomial ℤ => f.map (Int.castRingHom (ZMod p))) h
  rw [Polynomial.map_comp, Qd_map] at hmap
  have hq : ((-Polynomial.X - Polynomial.C ((d : ℤ) + 1) : Polynomial ℤ).map
      (Int.castRingHom (ZMod p))) =
      -Polynomial.X - Polynomial.C ((d + 1 : ℕ) : ZMod p) := by
    simp only [Polynomial.map_sub, Polynomial.map_neg, Polynomial.map_X, Polynomial.map_C]
    norm_num [Int.cast_add, Int.cast_one]
  rw [hq] at hmap
  simpa [map_mul, map_pow, Polynomial.map_C, Qd_map, Polynomial.C_pow] using hmap

/-- Evaluating the reflected polynomial: `Q(-a - (d+1)) = (-1)^(d+1) Q(a)`. -/
lemma eval_Q_neg_sub_eq_pow_mul_eval (p d : ℕ) [Fact p.Prime] (a : ZMod p) :
    Polynomial.eval (-a - ((d + 1 : ℕ) : ZMod p)) (Q p d) =
      (-1 : ZMod p) ^ (d + 1) * Polynomial.eval a (Q p d) := by
  have h := Q_comp_neg_X_sub_C_add_one p d
  have heval := congrArg (fun f : Polynomial (ZMod p) => Polynomial.eval a f) h
  rw [Polynomial.eval_comp] at heval
  rw [eval_sub, eval_neg, eval_X, eval_C] at heval
  rw [eval_mul, eval_pow, eval_C] at heval
  exact heval

/-- `Q(-(r+1)) = (-1)^(r+1) · Q(0)`. -/
lemma eval_Q_neg_add_one_eq_pow_mul_eval_zero (p r : ℕ) [Fact p.Prime] :
    Polynomial.eval (-((r + 1 : ℕ) : ZMod p)) (Q p r) =
      (-1 : ZMod p) ^ (r + 1) * Polynomial.eval (0 : ZMod p) (Q p r) := by
  simpa using (eval_Q_neg_sub_eq_pow_mul_eval p r (0 : ZMod p))

/-- `Q(-(2r+1)) = (-1)^(r+1) · Q(r)`. -/
lemma eval_Q_neg_two_mul_add_one_eq_pow_mul_eval_r (p r : ℕ) [Fact p.Prime] :
    Polynomial.eval (-((2 * r + 1 : ℕ) : ZMod p)) (Q p r) =
      (-1 : ZMod p) ^ (r + 1) * Polynomial.eval (r : ZMod p) (Q p r) := by
  have h := eval_Q_neg_sub_eq_pow_mul_eval p r (r : ZMod p)
  have hc : ((2 * r + 1 : ℕ) : ZMod p) = (r : ZMod p) + ((r + 1 : ℕ) : ZMod p) := by
    have hnat : 2 * r + 1 = r + (r + 1) := by omega
    rw [hnat]
    norm_num [Nat.cast_add]
  rw [show -((2 * r + 1 : ℕ) : ZMod p) = -(r : ZMod p) - ((r + 1 : ℕ) : ZMod p) by
    rw [hc]
    ring]
  exact h

/-! ## The roots of `Q p r` under `H_r = H_{2r} = 0` -/

/-- Root at `0`. -/
lemma eval_Q_zero_eq_zero_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime]
    (hrlt : r < p) (hHr : harmonicSum p r = 0) :
    Polynomial.eval (0 : ZMod p) (Q p r) = 0 := by
  rw [eval_zero_Q_eq_factorial_mul_harmonic p r hrlt, hHr, mul_zero]

/-- Root at `r`. -/
lemma eval_Q_r_eq_zero_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime]
    (h2r : 2 * r < p) (hHr : harmonicSum p r = 0)
    (hH2r : harmonicSum p (2 * r) = 0) :
    Polynomial.eval (r : ZMod p) (Q p r) = 0 := by
  rw [eval_Q_p_r_eq_ascFactorial_mul_sum_inv_Icc p r h2r]
  have hmid : (∑ j ∈ Finset.Icc (r + 1) (2 * r), ((j : ZMod p)⁻¹)) = 0 := by
    have hsplit := sum_Icc_split_add (fun j => ((j : ZMod p)⁻¹)) r r
    have hrr : r + r = 2 * r := by omega
    have h : harmonicSum p r +
        (∑ j ∈ Finset.Icc (r + 1) (2 * r), ((j : ZMod p)⁻¹)) =
        harmonicSum p (2 * r) := by
      simpa [harmonicSum, hrr] using hsplit
    rw [hHr, hH2r, zero_add] at h
    exact h
  rw [hmid, mul_zero]

/-- Root at `-r-1` via reflection of the root at `0`. -/
lemma eval_Q_neg_add_one_eq_zero_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime]
    (hrlt : r < p) (hHr : harmonicSum p r = 0) :
    Polynomial.eval (-((r + 1 : ℕ) : ZMod p)) (Q p r) = 0 := by
  rw [eval_Q_neg_add_one_eq_pow_mul_eval_zero p r,
    eval_Q_zero_eq_zero_of_harmonicSum_zero p r hrlt hHr, mul_zero]

/-- Root at `-2r-1` via reflection of the root at `r`. -/
lemma eval_Q_neg_two_mul_add_one_eq_zero_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime]
    (h2r : 2 * r < p) (hHr : harmonicSum p r = 0)
    (hH2r : harmonicSum p (2 * r) = 0) :
    Polynomial.eval (-((2 * r + 1 : ℕ) : ZMod p)) (Q p r) = 0 := by
  rw [eval_Q_neg_two_mul_add_one_eq_pow_mul_eval_r p r,
    eval_Q_r_eq_zero_of_harmonicSum_zero p r h2r hHr hH2r, mul_zero]

/-- Root at `-1/2` from the odd walk. -/
lemma eval_Q_neg_inv_two_eq_zero_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (h2r : 2 * r < p) (hHr : harmonicSum p r = 0)
    (hH2r : harmonicSum p (2 * r) = 0) :
    Polynomial.eval (-(2 : ZMod p)⁻¹) (Q p r) = 0 := by
  rw [eval_Q_neg_inv_two_eq_eval_P_neg_inv_two_mul_two_mul_oddWalk p r hp h2r]
  have hsplit := two_mul_harmonicSum_two_mul_eq_harmonicSum_add_two_mul_oddWalk p r hp
  have hw2 : (2 : ZMod p) * oddWalk p r = 0 := by
    rw [hH2r, hHr] at hsplit
    rw [mul_zero, zero_add] at hsplit
    exact hsplit.symm
  have hw : oddWalk p r = 0 := by
    rw [mul_eq_zero] at hw2
    rcases hw2 with h2 | hw
    · exact False.elim ((two_isUnit p hp).ne_zero h2)
    · exact hw
  rw [hw]
  ring

/-! ## The sextic `D_mod` and the six-root divisibility theorem -/

/-- The sextic divisor
`X (X-r) (X+r+1) (X+2r+1) (2X+1) (2X+2r+1)` over `ZMod p`. -/
noncomputable def D_mod (p r : ℕ) : Polynomial (ZMod p) :=
  Polynomial.X * (Polynomial.X - Polynomial.C (r : ZMod p)) *
    (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ZMod p)) *
    (Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ZMod p)) *
    ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C (1 : ZMod p)) *
    ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ZMod p))

/-- A unit multiple of a divisor is still a divisor. -/
private lemma unit_mul_dvd_of_dvd {R : Type*} [CommRing R] {u f g : R}
    (hu : IsUnit u) (h : f ∣ g) : (u * f) ∣ g := by
  rcases h with ⟨t, rfl⟩
  refine ⟨(↑hu.unit⁻¹ : R) * t, ?_⟩
  have h1 : (u : R) * (↑hu.unit⁻¹ : R) = 1 := by
    exact_mod_cast hu.unit.mul_inv
  have h' : f * t = (u * f) * ((↑hu.unit⁻¹ : R) * t) := by
    calc
      f * t = (1 : R) * (f * t) := by rw [one_mul]
      _ = (u * (↑hu.unit⁻¹ : R)) * (f * t) := by rw [h1]
      _ = (u * f) * ((↑hu.unit⁻¹ : R) * t) := by ring
  exact h'

/-- `2X + 1 = 2 · (X + 1/2)` in `ZMod p`. -/
lemma two_mul_X_add_C_one_eq_two_mul_X_add_inv_two (p : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) :
    ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C (1 : ZMod p)) =
      (2 : Polynomial (ZMod p)) * (Polynomial.X + Polynomial.C ((2 : ZMod p)⁻¹)) := by
  rw [mul_add]
  rw [show (2 : Polynomial (ZMod p)) = Polynomial.C (2 : ZMod p) by rfl]
  rw [← Polynomial.C_mul]
  have h21 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp
  rw [h21]

/-- `2X + 2r + 1 = 2 · (X + r + 1/2)` in `ZMod p`. -/
lemma two_mul_X_add_C_two_r_add_one_eq_two_mul_X_add_r_add_inv_two
    (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ZMod p)) =
      (2 : Polynomial (ZMod p)) *
        (Polynomial.X + Polynomial.C ((r : ZMod p) + (2 : ZMod p)⁻¹)) := by
  rw [mul_add]
  rw [show (2 : Polynomial (ZMod p)) = Polynomial.C (2 : ZMod p) by rfl]
  rw [← Polynomial.C_mul]
  have h21 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp
  have hparam : (2 : ZMod p) * ((r : ZMod p) + (2 : ZMod p)⁻¹) =
      ((2 * r + 1 : ℕ) : ZMod p) := by
    calc
      (2 : ZMod p) * ((r : ZMod p) + (2 : ZMod p)⁻¹)
          = (2 : ZMod p) * (r : ZMod p) + (2 : ZMod p) * (2 : ZMod p)⁻¹ := by ring
      _ = (2 : ZMod p) * (r : ZMod p) + 1 := by rw [h21]
      _ = ((2 * r + 1 : ℕ) : ZMod p) := by
            norm_num [Nat.cast_add]
  rw [hparam]

/-- `D_mod` is the product of six monic linear factors times the unit `4`. -/
lemma D_mod_eq_C_four_mul_prod_linear (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    D_mod p r = Polynomial.C (4 : ZMod p) *
      ((Polynomial.X - Polynomial.C (0 : ZMod p)) *
       (Polynomial.X - Polynomial.C (r : ZMod p)) *
       (Polynomial.X - Polynomial.C (-((r + 1 : ℕ) : ZMod p))) *
       (Polynomial.X - Polynomial.C (-((2 * r + 1 : ℕ) : ZMod p))) *
       (Polynomial.X - Polynomial.C (-(2 : ZMod p)⁻¹)) *
       (Polynomial.X - Polynomial.C (-((r : ZMod p) + (2 : ZMod p)⁻¹)))) := by
  unfold D_mod
  rw [two_mul_X_add_C_one_eq_two_mul_X_add_inv_two p hp]
  rw [two_mul_X_add_C_two_r_add_one_eq_two_mul_X_add_r_add_inv_two p r hp]
  simp only [Polynomial.C_neg, Polynomial.C_0]
  rw [show (Polynomial.C (4 : ZMod p) : Polynomial (ZMod p)) =
      (4 : Polynomial (ZMod p)) by rfl]
  ring_nf

/-- `r + 1/2 ≠ 0` when `2r + 1 < p`. -/
lemma add_inv_two_ne_zero_of_two_mul_add_one_lt (p r : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hmid : 2 * r + 1 < p) :
    (r : ZMod p) + (2 : ZMod p)⁻¹ ≠ 0 := by
  intro h
  have h2ne : (2 : ZMod p) ≠ 0 := (two_isUnit p hp).ne_zero
  field_simp [h2ne] at h
  have hz : ((2 * r + 1 : ℕ) : ZMod p) = 0 := by
    calc
      ((2 * r + 1 : ℕ) : ZMod p) = (2 : ZMod p) * (r : ZMod p) + 1 := by
            norm_num [Nat.cast_add]
      _ = (r : ZMod p) * 2 + 1 := by rw [mul_comm]
      _ = 0 := by rw [h, mul_zero]
  exact (cast_ne_zero_of_lt_prime p (2 * r + 1) (by omega) hmid) hz

/-- `(r+1) - 1/2 ≠ 0` when `2r + 1 < p`. -/
lemma sub_inv_two_ne_zero_of_two_mul_add_one_lt (p r : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hmid : 2 * r + 1 < p) :
    ((r + 1 : ℕ) : ZMod p) - (2 : ZMod p)⁻¹ ≠ 0 := by
  intro h
  have h2ne : (2 : ZMod p) ≠ 0 := (two_isUnit p hp).ne_zero
  field_simp [h2ne] at h
  have hz : ((2 * r + 1 : ℕ) : ZMod p) = 0 := by
    calc
      ((2 * r + 1 : ℕ) : ZMod p) = (2 : ZMod p) * ((r + 1 : ℕ) : ZMod p) - 1 := by
            norm_num [Nat.cast_add]
            ring
      _ = ((r + 1 : ℕ) : ZMod p) * 2 - 1 := by rw [mul_comm]
      _ = 0 := by rw [h, mul_zero]
  exact (cast_ne_zero_of_lt_prime p (2 * r + 1) (by omega) hmid) hz

/-- `2r + 1/2 ≠ 0` when `4r + 1 < p`. -/
lemma two_mul_r_add_inv_two_ne_zero_of_four_mul_add_one_lt (p r : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hmid : 4 * r + 1 < p) :
    (2 : ZMod p) * (r : ZMod p) + (2 : ZMod p)⁻¹ ≠ 0 := by
  intro h
  have h2ne : (2 : ZMod p) ≠ 0 := (two_isUnit p hp).ne_zero
  field_simp [h2ne] at h
  have hz : ((4 * r + 1 : ℕ) : ZMod p) = 0 := by
    calc
      ((4 * r + 1 : ℕ) : ZMod p) = (2 : ZMod p) * ((2 : ZMod p) * (r : ZMod p)) + 1 := by
            norm_num [Nat.cast_add, Nat.cast_mul]
            ring
      _ = ((2 : ZMod p) * (r : ZMod p)) * 2 + 1 := by ring
      _ = 0 := by
            rw [show ((2 : ZMod p) * (r : ZMod p)) * 2 + 1 =
                (2 : ZMod p) ^ 2 * (r : ZMod p) + 1 by ring]
            rw [h]
            simp
  exact (cast_ne_zero_of_lt_prime p (4 * r + 1) (by omega) hmid) hz

/-- `X - C u` and `X - C v` are coprime for distinct field elements. -/
private lemma isCoprime_X_sub_C_of_ne {R : Type*} [Field R] {u v : R} (h : u ≠ v) :
    IsCoprime (Polynomial.X - Polynomial.C u) (Polynomial.X - Polynomial.C v) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne h).isUnit

/-- The sixth reflection point equals `-r - 1/2`:
`1/2 - (r+1) = -(r + 1/2)` in `ZMod p`. -/
lemma inv_two_sub_add_one_eq_neg_add_inv_two (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (2 : ZMod p)⁻¹ - ((r + 1 : ℕ) : ZMod p) =
      -((r : ZMod p) + (2 : ZMod p)⁻¹) := by
  have h2ne : (2 : ZMod p) ≠ 0 := (two_isUnit p hp).ne_zero
  field_simp [h2ne]
  norm_num [Nat.cast_add]
  ring

/-- **Six-root divisibility.** If `p > 4r + 1` and `H_r = H_{2r} = 0`, then the six
pairwise distinct points `0, r, -r-1, -2r-1, -1/2, -r-1/2` are roots of `Q p r`,
hence the sextic `D_mod p r` divides `Q p r`. -/
theorem D_mod_dvd_Q_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime]
    (hr : 1 ≤ r) (hmid : 4 * r + 1 < p)
    (hHr : harmonicSum p r = 0) (hH2r : harmonicSum p (2 * r) = 0) :
    D_mod p r ∣ Q p r := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp3 : 3 ≤ p := by omega
  have hrlt : r < p := by omega
  have h2r : 2 * r < p := by omega
  have hroot0 := eval_Q_zero_eq_zero_of_harmonicSum_zero p r hrlt hHr
  have hrootr := eval_Q_r_eq_zero_of_harmonicSum_zero p r h2r hHr hH2r
  have hrootnr1 := eval_Q_neg_add_one_eq_zero_of_harmonicSum_zero p r hrlt hHr
  have hrootn2r1 := eval_Q_neg_two_mul_add_one_eq_zero_of_harmonicSum_zero p r h2r hHr hH2r
  have hrootinv2 := eval_Q_neg_inv_two_eq_zero_of_harmonicSum_zero p r hp3 h2r hHr hH2r
  have hrootnrinv2 : Polynomial.eval ((2 : ZMod p)⁻¹ - ((r + 1 : ℕ) : ZMod p)) (Q p r) = 0 := by
    have h := eval_Q_neg_sub_eq_pow_mul_eval p r (-(2 : ZMod p)⁻¹)
    rw [show (-(-(2 : ZMod p)⁻¹) - ((r + 1 : ℕ) : ZMod p)) =
        (2 : ZMod p)⁻¹ - ((r + 1 : ℕ) : ZMod p) by ring] at h
    rw [h, hrootinv2, mul_zero]
  let u0 : ZMod p := 0
  let u1 : ZMod p := r
  let u2 : ZMod p := -((r + 1 : ℕ) : ZMod p)
  let u3 : ZMod p := -((2 * r + 1 : ℕ) : ZMod p)
  let u4 : ZMod p := -(2 : ZMod p)⁻¹
  let u5 : ZMod p := -((r : ZMod p) + (2 : ZMod p)⁻¹)
  have hroot2 : Polynomial.eval u2 (Q p r) = 0 := by dsimp [u2]; exact hrootnr1
  have hroot3 : Polynomial.eval u3 (Q p r) = 0 := by dsimp [u3]; exact hrootn2r1
  have hroot4 : Polynomial.eval u4 (Q p r) = 0 := by dsimp [u4]; exact hrootinv2
  have hroot5 : Polynomial.eval u5 (Q p r) = 0 := by
    dsimp [u5]
    rw [← inv_two_sub_add_one_eq_neg_add_inv_two p r hp3]
    exact hrootnrinv2
  -- the pairwise distinctness of the six points
  have hr_ne : (r : ZMod p) ≠ 0 := cast_ne_zero_of_lt_prime p r hr hrlt
  have hr1_ne : ((r + 1 : ℕ) : ZMod p) ≠ 0 :=
    cast_ne_zero_of_lt_prime p (r + 1) (by omega) (by omega)
  have h2r1_ne : ((2 * r + 1 : ℕ) : ZMod p) ≠ 0 :=
    cast_ne_zero_of_lt_prime p (2 * r + 1) (by omega) (by omega)
  have h3r1_ne : ((3 * r + 1 : ℕ) : ZMod p) ≠ 0 :=
    cast_ne_zero_of_lt_prime p (3 * r + 1) (by omega) (by omega)
  have h4r1_ne : ((4 * r + 1 : ℕ) : ZMod p) ≠ 0 :=
    cast_ne_zero_of_lt_prime p (4 * r + 1) (by omega) hmid
  have hinv2_ne : (2 : ZMod p)⁻¹ ≠ 0 := (two_isUnit p hp3).inv.ne_zero
  have hadd_inv2 : (r : ZMod p) + (2 : ZMod p)⁻¹ ≠ 0 :=
    add_inv_two_ne_zero_of_two_mul_add_one_lt p r hp3 (by omega)
  have hsub_inv2 : ((r + 1 : ℕ) : ZMod p) - (2 : ZMod p)⁻¹ ≠ 0 :=
    sub_inv_two_ne_zero_of_two_mul_add_one_lt p r hp3 (by omega)
  have h2r_add_inv2 : (2 : ZMod p) * (r : ZMod p) + (2 : ZMod p)⁻¹ ≠ 0 :=
    two_mul_r_add_inv_two_ne_zero_of_four_mul_add_one_lt p r hp3 hmid
  have h21 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp3
  have h01 : u0 ≠ u1 := by
    dsimp [u0, u1]
    exact hr_ne.symm
  have h02 : u0 ≠ u2 := by
    dsimp [u0, u2]
    intro h
    exact hr1_ne (neg_eq_zero.mp h.symm)
  have h03 : u0 ≠ u3 := by
    dsimp [u0, u3]
    intro h
    exact h2r1_ne (neg_eq_zero.mp h.symm)
  have h04 : u0 ≠ u4 := by
    dsimp [u0, u4]
    intro h
    exact hinv2_ne (neg_eq_zero.mp h.symm)
  have h05 : u0 ≠ u5 := by
    dsimp [u0, u5]
    intro h
    exact hadd_inv2 (neg_eq_zero.mp h.symm)
  have h12 : u1 ≠ u2 := by
    dsimp [u1, u2]
    intro h
    have hz : ((2 * r + 1 : ℕ) : ZMod p) = 0 := by
      calc
        ((2 * r + 1 : ℕ) : ZMod p) = (r : ZMod p) + ((r + 1 : ℕ) : ZMod p) := by
              have hnat : 2 * r + 1 = r + (r + 1) := by omega
              rw [hnat]
              norm_num [Nat.cast_add]
        _ = 0 := by rw [h]; simp
    exact h2r1_ne hz
  have h13 : u1 ≠ u3 := by
    dsimp [u1, u3]
    intro h
    have hz : ((3 * r + 1 : ℕ) : ZMod p) = 0 := by
      calc
        ((3 * r + 1 : ℕ) : ZMod p) = (r : ZMod p) + ((2 * r + 1 : ℕ) : ZMod p) := by
              have hnat : 3 * r + 1 = r + (2 * r + 1) := by omega
              rw [hnat]
              norm_num [Nat.cast_add]
        _ = 0 := by rw [h]; simp
    exact h3r1_ne hz
  have h14 : u1 ≠ u4 := by
    dsimp [u1, u4]
    intro h
    have hz : (r : ZMod p) + (2 : ZMod p)⁻¹ = 0 := by
      calc
        (r : ZMod p) + (2 : ZMod p)⁻¹ = (r : ZMod p) - (-(2 : ZMod p)⁻¹) := by ring
        _ = 0 := by rw [h]; simp
    exact hadd_inv2 hz
  have h15 : u1 ≠ u5 := by
    dsimp [u1, u5]
    intro h
    have hz : (2 : ZMod p) * (r : ZMod p) + (2 : ZMod p)⁻¹ = 0 := by
      calc
        (2 : ZMod p) * (r : ZMod p) + (2 : ZMod p)⁻¹
            = (r : ZMod p) + ((r : ZMod p) + (2 : ZMod p)⁻¹) := by ring
        _ = 0 := by nth_rewrite 1 [h]; simp
    exact h2r_add_inv2 hz
  have h23 : u2 ≠ u3 := by
    dsimp [u2, u3]
    intro h
    have h' := neg_inj.mp h
    have hsub := congrArg (fun t : ZMod p => t - ((r + 1 : ℕ) : ZMod p)) h'
    rw [sub_self,
      show ((2 * r + 1 : ℕ) : ZMod p) - ((r + 1 : ℕ) : ZMod p) = (r : ZMod p) by
        norm_num [Nat.cast_add]
        ring] at hsub
    exact hr_ne hsub.symm
  have h24 : u2 ≠ u4 := by
    dsimp [u2, u4]
    intro h
    have h' := neg_inj.mp h
    have hz : ((r + 1 : ℕ) : ZMod p) - (2 : ZMod p)⁻¹ = 0 := by
      rw [h']
      simp
    exact hsub_inv2 hz
  have h25 : u2 ≠ u5 := by
    dsimp [u2, u5]
    intro h
    have h' := neg_inj.mp h
    have hsub := congrArg (fun t : ZMod p => t - (r : ZMod p)) h'
    have hc1 : ((r + 1 : ℕ) : ZMod p) - (r : ZMod p) = (1 : ZMod p) := by
      norm_num [Nat.cast_add]
    have hc2 : ((r : ZMod p) + (2 : ZMod p)⁻¹) - (r : ZMod p) = (2 : ZMod p)⁻¹ := by ring
    rw [hc1, hc2] at hsub
    have h2eq1 : (2 : ZMod p) = 1 := by
      calc
        (2 : ZMod p) = (2 : ZMod p) * 1 := by rw [mul_one]
        _ = (2 : ZMod p) * (2 : ZMod p)⁻¹ := by rw [hsub]
        _ = 1 := h21
    have hone_ne : (1 : ZMod p) ≠ 0 := by
      intro hz
      simp at hz
    have hz : (1 : ZMod p) = 0 := by
      rw [← sub_eq_zero] at h2eq1
      ring_nf at h2eq1 ⊢
      exact h2eq1
    exact hone_ne hz
  have h34 : u3 ≠ u4 := by
    dsimp [u3, u4]
    intro h
    have h' := neg_inj.mp h
    have h2ne : (2 : ZMod p) ≠ 0 := (two_isUnit p hp3).ne_zero
    have hzsub : ((2 * r + 1 : ℕ) : ZMod p) - (2 : ZMod p)⁻¹ = 0 := by
      rw [h']
      simp
    field_simp [h2ne] at hzsub
    have hz : ((4 * r + 1 : ℕ) : ZMod p) = 0 := by
      calc
        ((4 * r + 1 : ℕ) : ZMod p) = (2 : ZMod p) * ((2 * r + 1 : ℕ) : ZMod p) - 1 := by
              norm_num [Nat.cast_add]
              ring
        _ = ((2 * r + 1 : ℕ) : ZMod p) * 2 - 1 := by rw [mul_comm]
        _ = 0 := by rw [hzsub, mul_zero]
    exact h4r1_ne hz
  have h35 : u3 ≠ u5 := by
    dsimp [u3, u5]
    intro h
    have h' := neg_inj.mp h
    have hsub := congrArg (fun t : ZMod p => t - (r : ZMod p)) h'
    have hc1 : ((2 * r + 1 : ℕ) : ZMod p) - (r : ZMod p) = ((r + 1 : ℕ) : ZMod p) := by
      norm_num [Nat.cast_add]
      ring
    have hc2 : ((r : ZMod p) + (2 : ZMod p)⁻¹) - (r : ZMod p) = (2 : ZMod p)⁻¹ := by ring
    rw [hc1, hc2] at hsub
    have hz : ((r + 1 : ℕ) : ZMod p) - (2 : ZMod p)⁻¹ = 0 := by
      rw [hsub]
      simp
    exact hsub_inv2 hz
  have h45 : u4 ≠ u5 := by
    dsimp [u4, u5]
    intro h
    have h' := neg_inj.mp h
    have hz : (r : ZMod p) = 0 := by
      have hsub := congrArg (fun t : ZMod p => t - (2 : ZMod p)⁻¹) h'
      -- hsub : 2⁻¹ - 2⁻¹ = r + 2⁻¹ - 2⁻¹ → 0 = r
      rw [show (2 : ZMod p)⁻¹ - (2 : ZMod p)⁻¹ = (0 : ZMod p) by simp,
        show ((r : ZMod p) + (2 : ZMod p)⁻¹) - (2 : ZMod p)⁻¹ = (r : ZMod p) by ring] at hsub
      exact hsub.symm
    exact hr_ne hz
  -- divisibility by each linear factor
  have hdvd0 : (Polynomial.X - Polynomial.C u0) ∣ Q p r :=
    Polynomial.dvd_iff_isRoot.mpr hroot0
  have hdvd1 : (Polynomial.X - Polynomial.C u1) ∣ Q p r :=
    Polynomial.dvd_iff_isRoot.mpr hrootr
  have hdvd2 : (Polynomial.X - Polynomial.C u2) ∣ Q p r :=
    Polynomial.dvd_iff_isRoot.mpr hroot2
  have hdvd3 : (Polynomial.X - Polynomial.C u3) ∣ Q p r :=
    Polynomial.dvd_iff_isRoot.mpr hroot3
  have hdvd4 : (Polynomial.X - Polynomial.C u4) ∣ Q p r :=
    Polynomial.dvd_iff_isRoot.mpr hroot4
  have hdvd5 : (Polynomial.X - Polynomial.C u5) ∣ Q p r :=
    Polynomial.dvd_iff_isRoot.mpr hroot5
  -- combine via pairwise coprimality
  have hcop01 : IsCoprime (Polynomial.X - Polynomial.C u0) (Polynomial.X - Polynomial.C u1) :=
    isCoprime_X_sub_C_of_ne h01
  have hcop02 : IsCoprime (Polynomial.X - Polynomial.C u0) (Polynomial.X - Polynomial.C u2) :=
    isCoprime_X_sub_C_of_ne h02
  have hcop03 : IsCoprime (Polynomial.X - Polynomial.C u0) (Polynomial.X - Polynomial.C u3) :=
    isCoprime_X_sub_C_of_ne h03
  have hcop04 : IsCoprime (Polynomial.X - Polynomial.C u0) (Polynomial.X - Polynomial.C u4) :=
    isCoprime_X_sub_C_of_ne h04
  have hcop05 : IsCoprime (Polynomial.X - Polynomial.C u0) (Polynomial.X - Polynomial.C u5) :=
    isCoprime_X_sub_C_of_ne h05
  have hcop12 : IsCoprime (Polynomial.X - Polynomial.C u1) (Polynomial.X - Polynomial.C u2) :=
    isCoprime_X_sub_C_of_ne h12
  have hcop13 : IsCoprime (Polynomial.X - Polynomial.C u1) (Polynomial.X - Polynomial.C u3) :=
    isCoprime_X_sub_C_of_ne h13
  have hcop14 : IsCoprime (Polynomial.X - Polynomial.C u1) (Polynomial.X - Polynomial.C u4) :=
    isCoprime_X_sub_C_of_ne h14
  have hcop15 : IsCoprime (Polynomial.X - Polynomial.C u1) (Polynomial.X - Polynomial.C u5) :=
    isCoprime_X_sub_C_of_ne h15
  have hcop23 : IsCoprime (Polynomial.X - Polynomial.C u2) (Polynomial.X - Polynomial.C u3) :=
    isCoprime_X_sub_C_of_ne h23
  have hcop24 : IsCoprime (Polynomial.X - Polynomial.C u2) (Polynomial.X - Polynomial.C u4) :=
    isCoprime_X_sub_C_of_ne h24
  have hcop25 : IsCoprime (Polynomial.X - Polynomial.C u2) (Polynomial.X - Polynomial.C u5) :=
    isCoprime_X_sub_C_of_ne h25
  have hcop34 : IsCoprime (Polynomial.X - Polynomial.C u3) (Polynomial.X - Polynomial.C u4) :=
    isCoprime_X_sub_C_of_ne h34
  have hcop35 : IsCoprime (Polynomial.X - Polynomial.C u3) (Polynomial.X - Polynomial.C u5) :=
    isCoprime_X_sub_C_of_ne h35
  have hcop45 : IsCoprime (Polynomial.X - Polynomial.C u4) (Polynomial.X - Polynomial.C u5) :=
    isCoprime_X_sub_C_of_ne h45
  let F0 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C u0
  let F1 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C u1
  let F2 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C u2
  let F3 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C u3
  let F4 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C u4
  let F5 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C u5
  have hdvd01 : F0 * F1 ∣ Q p r := by dsimp [F0, F1]; exact hcop01.mul_dvd hdvd0 hdvd1
  have hcop012 : IsCoprime (F0 * F1) F2 := by
    dsimp [F0, F1, F2]
    exact hcop02.mul_left hcop12
  have hdvd012 : F0 * F1 * F2 ∣ Q p r := hcop012.mul_dvd hdvd01 (by dsimp [F2]; exact hdvd2)
  have hcop0123 : IsCoprime (F0 * F1 * F2) F3 := by
    dsimp [F0, F1, F2, F3]
    exact (hcop03.mul_left hcop13).mul_left hcop23
  have hdvd0123 : F0 * F1 * F2 * F3 ∣ Q p r :=
    hcop0123.mul_dvd hdvd012 (by dsimp [F3]; exact hdvd3)
  have hcop01234 : IsCoprime (F0 * F1 * F2 * F3) F4 := by
    dsimp [F0, F1, F2, F3, F4]
    exact ((hcop04.mul_left hcop14).mul_left hcop24).mul_left hcop34
  have hdvd01234 : F0 * F1 * F2 * F3 * F4 ∣ Q p r :=
    hcop01234.mul_dvd hdvd0123 (by dsimp [F4]; exact hdvd4)
  have hcop012345 : IsCoprime (F0 * F1 * F2 * F3 * F4) F5 := by
    dsimp [F0, F1, F2, F3, F4, F5]
    exact (((hcop05.mul_left hcop15).mul_left hcop25).mul_left hcop35).mul_left hcop45
  have hprod_dvd : F0 * F1 * F2 * F3 * F4 * F5 ∣ Q p r :=
    hcop012345.mul_dvd hdvd01234 (by dsimp [F5]; exact hdvd5)
  have h4unit : IsUnit (4 : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro hz
    have hdvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hz
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hC4unit : IsUnit (Polynomial.C (4 : ZMod p) : Polynomial (ZMod p)) :=
    (IsUnit.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p))) h4unit
  rw [D_mod_eq_C_four_mul_prod_linear p r hp3]
  exact unit_mul_dvd_of_dvd hC4unit hprod_dvd

end

end Erdos291
