import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

/-!
# Erdős #291 — Bonferroni factorial-moment machinery

Purely combinatorial lemmas about the factorial moments of the "bad prime" count,
together with the exact inclusion-exclusion identity and the Bonferroni truncation
bounds (odd truncations are lower bounds, even truncations are upper bounds).

Everything here is generic over a finite universe `Ω : Finset ℕ`, a finite prime-set
`P : Finset ℕ`, and a map `S : ℕ → Finset ℕ`; `badCount P S n` counts the `p ∈ P`
with `n ∈ S p`.
-/

namespace Erdos291

/-- Number of `p ∈ P` with `n ∈ S p` (the "bad" primes for `n`). -/
def badCount (P : Finset ℕ) (S : ℕ → Finset ℕ) (n : ℕ) : ℕ :=
  (P.filter fun p => n ∈ S p).card

/-- The `j`-th factorial moment `M_j = ∑_{n∈Ω} C(badCount P S n, j)`. -/
def factorialMoment (Ω P : Finset ℕ) (S : ℕ → Finset ℕ) (j : ℕ) : ℤ :=
  ∑ n ∈ Ω, (Nat.choose (badCount P S n) j : ℤ)

/-- `badCount P S n` never exceeds the total number of primes `P.card`. -/
lemma badCount_le_card (P : Finset ℕ) (S : ℕ → Finset ℕ) (n : ℕ) :
    badCount P S n ≤ P.card :=
  Finset.card_filter_le P (fun p => n ∈ S p)

/-- `(-1 : ℤ)` raised to an even power `2 * k` is `1`. -/
lemma neg_one_pow_two_mul (k : ℕ) : (-1 : ℤ) ^ (2 * k) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

/-- `(-1 : ℤ)` raised to an odd power `2 * k + 1` is `-1`. -/
lemma neg_one_pow_two_mul_add_one (k : ℕ) : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
  rw [pow_add, neg_one_pow_two_mul k, pow_one]
  simp

/-- The correction term in the truncation identity is nonnegative: `C(Y-1,r) · [Y≠0] ≥ 0`. -/
lemma choose_mul_indicator_nonneg (Y r : ℕ) :
    (0 : ℤ) ≤ (Nat.choose (Y - 1) r : ℤ) * (if Y = 0 then (0 : ℤ) else 1) := by
  have h1 : (0 : ℤ) ≤ (Nat.choose (Y - 1) r : ℤ) := Nat.cast_nonneg (Nat.choose (Y - 1) r)
  have h2 : (0 : ℤ) ≤ (if Y = 0 then (0 : ℤ) else 1) := by
    by_cases h : Y = 0 <;> simp [h]
  exact mul_nonneg h1 h2

/-- The full alternating sum of binomial coefficients is the indicator of `Y = 0`. -/
lemma alternating_sum_choose_eq_indicator (Y : ℕ) :
    (∑ j ∈ Finset.range (Y + 1), ((-1 : ℤ) ^ j * (Nat.choose Y j : ℤ))) =
      (if Y = 0 then (1 : ℤ) else 0) := by
  simpa using (Int.alternating_sum_range_choose (n := Y))

/-- The truncated alternating sum of binomial coefficients equals the indicator of `Y = 0`
plus a signed correction term. This is the load-bearing pointwise identity behind the
Bonferroni bounds. -/
lemma alternating_sum_choose_eq_indicator_add (Y r : ℕ) :
    (∑ j ∈ Finset.range (r + 1), ((-1 : ℤ) ^ j * (Nat.choose Y j : ℤ))) =
      (if Y = 0 then (1 : ℤ) else 0) +
        ((-1 : ℤ) ^ r * (Nat.choose (Y - 1) r : ℤ)) * (if Y = 0 then (0 : ℤ) else 1) := by
  by_cases hY : Y = 0
  · subst Y
    rw [Finset.sum_range_succ']
    simp
  · have hY' : (Y - 1) + 1 = Y := by omega
    have hmain := Int.alternating_sum_range_choose_eq_choose (n := Y - 1) (m := r)
    rw [hY'] at hmain
    simpa [hY] using hmain

/-- Extending the alternating-sum upper index from `Y` to any `N ≥ Y` does not change the
value: the extra binomial coefficients `C(Y,j)` vanish for `j > Y`. -/
lemma alternating_sum_choose_eq_indicator_extended {Y N : ℕ} (hY : Y ≤ N) :
    (∑ j ∈ Finset.range (N + 1), ((-1 : ℤ) ^ j * (Nat.choose Y j : ℤ))) =
      (if Y = 0 then (1 : ℤ) else 0) := by
  rw [← alternating_sum_choose_eq_indicator Y]
  have hN : N + 1 = (Y + 1) + (N - Y) := by omega
  rw [hN, Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range (N - Y),
      ((-1 : ℤ) ^ (Y + 1 + j) * (Nat.choose Y (Y + 1 + j) : ℤ))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp [Nat.choose_eq_zero_of_lt (by omega : Y < Y + 1 + j)]
  rw [hzero, add_zero]

/-- Pointwise lower-bound inequality: the odd-truncated alternating sum is at most the
indicator `[Y = 0]`. -/
lemma partial_sum_lower_le_indicator (Y m : ℕ) :
    (∑ j ∈ Finset.range (2 * m + 2), ((-1 : ℤ) ^ j * (Nat.choose Y j : ℤ))) ≤
      (if Y = 0 then (1 : ℤ) else 0) := by
  rw [alternating_sum_choose_eq_indicator_add Y (2 * m + 1)]
  rw [neg_one_pow_two_mul_add_one m]
  have hnonneg : (0 : ℤ) ≤
      (Nat.choose (Y - 1) (2 * m + 1) : ℤ) * (if Y = 0 then (0 : ℤ) else 1) :=
    choose_mul_indicator_nonneg Y (2 * m + 1)
  nlinarith

/-- Pointwise upper-bound inequality: the even-truncated alternating sum is at least the
indicator `[Y = 0]`. -/
lemma partial_sum_upper_ge_indicator (Y m : ℕ) :
    (if Y = 0 then (1 : ℤ) else 0) ≤
      ∑ j ∈ Finset.range (2 * m + 1), ((-1 : ℤ) ^ j * (Nat.choose Y j : ℤ)) := by
  rw [alternating_sum_choose_eq_indicator_add Y (2 * m)]
  rw [neg_one_pow_two_mul m]
  have hnonneg : (0 : ℤ) ≤
      (Nat.choose (Y - 1) (2 * m) : ℤ) * (if Y = 0 then (0 : ℤ) else 1) :=
    choose_mul_indicator_nonneg Y (2 * m)
  nlinarith

/-- Exact inclusion-exclusion: the good count equals the full alternating sum of factorial
moments (finite: `M_j = 0` for `j > P.card`). -/
theorem good_count_eq_alternating_moments (Ω P : Finset ℕ) (S : ℕ → Finset ℕ) :
    ((Ω.filter fun n => badCount P S n = 0).card : ℤ) =
      ∑ j ∈ Finset.range (P.card + 1), ((-1 : ℤ) ^ j) * factorialMoment Ω P S j := by
  rw [Finset.natCast_card_filter (fun n => badCount P S n = 0) Ω]
  simp_rw [factorialMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  exact (alternating_sum_choose_eq_indicator_extended (badCount_le_card P S n)).symm

/-- Bonferroni LOWER bound (odd truncation r = 2m+1): partial alternating sum ≤ #good. -/
theorem bonferroni_lower (Ω P : Finset ℕ) (S : ℕ → Finset ℕ) (m : ℕ) :
    ((Ω.filter fun n => badCount P S n = 0).card : ℤ) ≥
      ∑ j ∈ Finset.range (2 * m + 2), ((-1 : ℤ) ^ j) * factorialMoment Ω P S j := by
  rw [ge_iff_le]
  rw [Finset.natCast_card_filter (fun n => badCount P S n = 0) Ω]
  simp_rw [factorialMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n _
  exact partial_sum_lower_le_indicator (badCount P S n) m

/-- Bonferroni UPPER bound (even truncation r = 2m): partial alternating sum ≥ #good. -/
theorem bonferroni_upper (Ω P : Finset ℕ) (S : ℕ → Finset ℕ) (m : ℕ) :
    ((Ω.filter fun n => badCount P S n = 0).card : ℤ) ≤
      ∑ j ∈ Finset.range (2 * m + 1), ((-1 : ℤ) ^ j) * factorialMoment Ω P S j := by
  rw [Finset.natCast_card_filter (fun n => badCount P S n = 0) Ω]
  simp_rw [factorialMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n _
  exact partial_sum_upper_ge_indicator (badCount P S n) m

end Erdos291
