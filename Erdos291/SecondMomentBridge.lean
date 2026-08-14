import Erdos291.ShellMoments
import Erdos291.Bonferroni
import Erdos291.HABrun
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Basic

/-!
# Erdős #291 — the shell-row ↔ column second-moment bridge

On the dyadic shell `Ω_X = (X, 2X]` the random variable `Y X n` counts the bad primes of `n`.
Its second normalized factorial moment is

    `mu X 2 = (1/X) · Σ_{n ∈ Ω_X} C(Y X n, 2)`,

which counts (unordered) pairs of distinct bad primes.  This file develops the *order-2 Fubini
double count* relating `mu X 2` to the joint densities `γ_{p,q}(X) = badPairDensity p q X`, and
extracts the exact decomposition of the order-2 Brun error

    `Rtwo X = mu X 2 − (lambda X)^2 / 2`

into a (negative) diagonal term and the cross-prime covariance `crossCov X`:

    `Rtwo X = −(1/2) · Σ_p β_p² + (1/2) · crossCov X`.

Everything here is unconditional.  Bounding `crossCov X` is the open obstruction and is
deliberately *not* attempted in this file.

The two load-bearing identities are

* `two_mul_mu_two_eq_sum_off_diag`: `2 · μ₂ = Σ_{p ≠ q} γ_{p,q}` (order-2 Fubini), and
* `two_mul_mu_two_eq_lambda_sq_sub_sum_beta_sq_add_crossCov`: the bridge identity (i).

All moments are normalized by `1 / (X : ℝ)`; for `X = 0` this is `0`, so every theorem is
stated for all `X` with no positivity hypothesis.
-/

open scoped BigOperators

namespace Erdos291

/-! ## Joint densities and the order-2 Brun error -/

/-- Joint count: number of `n` in the shell where BOTH `p` and `q` are bad. -/
def badPairCount (X p q : ℕ) : ℕ :=
  ((shellOmega X).filter (fun n => badPrime p n ∧ badPrime q n)).card

/-- Joint density `γ_{p,q}(X) = (1/X) · #{n : p, q both bad}`. -/
noncomputable def badPairDensity (p q X : ℕ) : ℝ :=
  (1 / (X : ℝ)) * (badPairCount X p q : ℝ)

/-- Cross-prime covariance `K(X) = Σ_{p ≠ q} (γ_{p,q} − β_p β_q)`. -/
noncomputable def crossCov (X : ℕ) : ℝ :=
  ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X,
    if p ≠ q then (badPairDensity p q X - beta p X * beta q X) else 0

/-- The `j = 2` Brun error `R_2(X) = μ_2(X) − λ_X²/2`. -/
noncomputable def Rtwo (X : ℕ) : ℝ := mu X 2 - (lambda X)^2 / 2

/-! ## Combinatorial double count at order 2 -/

/-- The off-diagonal of a finset has cardinality `2 · C(#s, 2)`: each unordered pair of
distinct elements gives two ordered pairs. -/
lemma offDiag_card_eq_two_mul_choose (s : Finset ℕ) :
    s.offDiag.card = 2 * (s.card).choose 2 := by
  rw [Finset.offDiag_card, Nat.choose_two_right]
  have hdiv : 2 * (s.card * (s.card - 1) / 2) = s.card * (s.card - 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self s.card))
  rw [hdiv]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Fubini over `offDiag`: `Σ_n #(offDiag of the bad-prime set of n) = Σ_{p ≠ q} badPairCount`.
This is the order-2 analogue of `sum_card_filter_comm`. -/
lemma sum_offDiag_eq_sum_badPair (X : ℕ) :
    (∑ n ∈ shellOmega X, ((badPrimes X).filter (fun p => badPrime p n)).offDiag.card) =
      ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairCount X p q else 0 := by
  classical
  have hfinset (n : ℕ) :
      ((badPrimes X).filter (fun p => badPrime p n)).offDiag =
        ((badPrimes X).offDiag).filter (fun pq => badPrime pq.1 n ∧ badPrime pq.2 n) := by
    ext pq
    simp [Finset.mem_offDiag]
    tauto
  have hoff : (badPrimes X).offDiag =
      ((badPrimes X) ×ˢ (badPrimes X)).filter (fun pq => pq.1 ≠ pq.2) := by
    ext pq
    simp [Finset.mem_offDiag]
    tauto
  calc
    (∑ n ∈ shellOmega X, ((badPrimes X).filter (fun p => badPrime p n)).offDiag.card)
        = ∑ n ∈ shellOmega X, ∑ pq ∈ (badPrimes X).offDiag,
            if badPrime pq.1 n ∧ badPrime pq.2 n then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro n _
          rw [hfinset n]
          rw [Finset.sum_boole]
          rfl
    _ = ∑ pq ∈ (badPrimes X).offDiag, ∑ n ∈ shellOmega X,
            if badPrime pq.1 n ∧ badPrime pq.2 n then 1 else 0 := Finset.sum_comm
    _ = ∑ pq ∈ (badPrimes X).offDiag, badPairCount X pq.1 pq.2 := by
          refine Finset.sum_congr rfl ?_
          intro pq _
          rw [Finset.sum_boole]
          rfl
    _ = ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairCount X p q else 0 := by
          rw [hoff]
          rw [Finset.sum_filter]
          exact (Finset.sum_product (badPrimes X) (badPrimes X)
            (fun a => if a.1 ≠ a.2 then badPairCount X a.1 a.2 else 0))

/-- `2 · Σ_n C(Y X n, 2) = Σ_{p ≠ q} badPairCount X p q`: the numerator-level order-2 Fubini
identity. -/
lemma two_mul_sum_choose_two (X : ℕ) :
    2 * (∑ n ∈ shellOmega X, Nat.choose (Y X n) 2) =
      ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairCount X p q else 0 := by
  calc
    2 * (∑ n ∈ shellOmega X, Nat.choose (Y X n) 2)
        = ∑ n ∈ shellOmega X, 2 * Nat.choose (Y X n) 2 := by
            rw [Finset.mul_sum]
    _ = ∑ n ∈ shellOmega X, ((badPrimes X).filter (fun p => badPrime p n)).offDiag.card := by
            refine Finset.sum_congr rfl ?_
            intro n _
            exact (offDiag_card_eq_two_mul_choose ((badPrimes X).filter (fun p => badPrime p n))).symm
    _ = ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairCount X p q else 0 := by
            exact sum_offDiag_eq_sum_badPair X

/-- Real-valued form of the numerator-level order-2 Fubini identity. -/
lemma two_mul_sum_choose_two_real (X : ℕ) :
    (2 : ℝ) * (∑ n ∈ shellOmega X, (Nat.choose (Y X n) 2 : ℝ)) =
      ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then (badPairCount X p q : ℝ) else 0 := by
  exact_mod_cast two_mul_sum_choose_two X

/-- Distributing the normalization `1/X` through the off-diagonal sum. -/
lemma one_div_mul_sum_offDiag (X : ℕ) :
    (1 / (X : ℝ)) * (∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X,
        if p ≠ q then (badPairCount X p q : ℝ) else 0) =
      ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairDensity p q X else 0 := by
  unfold badPairDensity
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [mul_ite]
  simp

/-! ## Order-2 Fubini and the diagonal collapse -/

/-- On the diagonal the joint density collapses to the marginal: `γ_{p,p} = β_p`. -/
theorem badPairDensity_diag (p X : ℕ) : badPairDensity p p X = beta p X := by
  unfold badPairDensity badPairCount beta
  congr 1
  norm_cast
  congr 1
  ext n
  simp

/-- **Order-2 Fubini**: `2 · μ₂ = Σ_{p ≠ q} γ_{p,q}`, the analogue of `mu_one_eq_lambda`. -/
theorem two_mul_mu_two_eq_sum_off_diag (X : ℕ) :
    2 * mu X 2 = ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairDensity p q X else 0 := by
  calc
    2 * mu X 2 = (1 / (X : ℝ)) * (2 * ∑ n ∈ shellOmega X, (Nat.choose (Y X n) 2 : ℝ)) := by
        unfold mu
        ring
    _ = (1 / (X : ℝ)) * (∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X,
          if p ≠ q then (badPairCount X p q : ℝ) else 0) := by
        rw [two_mul_sum_choose_two_real X]
    _ = ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, if p ≠ q then badPairDensity p q X else 0 := by
        exact one_div_mul_sum_offDiag X

/-! ## Bridge identity (i) -/

/-- **Bridge identity (i)**: `2 · μ₂ = λ² − Σ_p β_p² + K(X)`, where `K = crossCov X`. -/
theorem two_mul_mu_two_eq_lambda_sq_sub_sum_beta_sq_add_crossCov (X : ℕ) :
    2 * mu X 2 = (lambda X)^2 - (∑ p ∈ badPrimes X, (beta p X)^2) + crossCov X := by
  rw [two_mul_mu_two_eq_sum_off_diag X]
  have hsq : (lambda X)^2 = ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X, beta p X * beta q X := by
    unfold lambda
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hdiag : (∑ p ∈ badPrimes X, (beta p X)^2) = ∑ p ∈ badPrimes X, ∑ q ∈ badPrimes X,
      if p = q then beta p X * beta q X else 0 := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rw [Finset.sum_ite_eq]
    simp [hp, pow_two]
  rw [hsq, hdiag]
  unfold crossCov
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro q _
  by_cases hpq : p = q <;> simp [hpq]

/-! ## Bridge identity (ii): the exact Brun-error decomposition -/

/-- **Bridge identity (ii)**: `R_2(X) = −(1/2)·Σ_p β_p² + (1/2)·crossCov X`. -/
theorem Rtwo_eq_neg_half_sum_beta_sq_add_half_crossCov (X : ℕ) :
    Rtwo X = -(1 / 2) * (∑ p ∈ badPrimes X, (beta p X)^2) + (1 / 2) * crossCov X := by
  unfold Rtwo
  have h3 := two_mul_mu_two_eq_lambda_sq_sub_sum_beta_sq_add_crossCov X
  nlinarith

/-! ## Basic bounds for `beta` -/

/-- Every local density `beta p X` is at most `1`. -/
theorem beta_le_one (p X : ℕ) : beta p X ≤ 1 := by
  unfold beta
  by_cases hX : X = 0
  · simp [hX]
  · have hcard : ((shellOmega X).filter (fun n => badPrime p n)).card ≤ X := by
      calc
        ((shellOmega X).filter (fun n => badPrime p n)).card ≤ (shellOmega X).card :=
          Finset.card_le_card (Finset.filter_subset (fun n => badPrime p n) (shellOmega X))
        _ = X := by
          rw [shellOmega, Nat.card_Icc]
          omega
    have hcardR : (((shellOmega X).filter (fun n => badPrime p n)).card : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hcard
    have hinv : 0 ≤ (1 / (X : ℝ)) := one_div_nonneg.mpr (Nat.cast_nonneg X)
    have hmul : (1 / (X : ℝ)) * (((shellOmega X).filter (fun n => badPrime p n)).card : ℝ) ≤
        (1 / (X : ℝ)) * (X : ℝ) :=
      mul_le_mul_of_nonneg_left hcardR hinv
    calc
      (1 / (X : ℝ)) * (((shellOmega X).filter (fun n => badPrime p n)).card : ℝ)
          ≤ (1 / (X : ℝ)) * (X : ℝ) := hmul
      _ = 1 := by
        exact one_div_mul_cancel (by exact_mod_cast hX : (X : ℝ) ≠ 0)

/-! ## The diagonal is controlled by the first moment -/

/-- Since `0 ≤ β_p ≤ 1`, we have `β_p² ≤ β_p`, hence `Σ_p β_p² ≤ Σ_p β_p = λ_X`. -/
theorem diag_le_lambda (X : ℕ) : (∑ p ∈ badPrimes X, (beta p X)^2) ≤ lambda X := by
  unfold lambda
  refine Finset.sum_le_sum ?_
  intro p _
  have hnonneg : 0 ≤ beta p X := beta_nonneg p X
  have hle1 : beta p X ≤ 1 := beta_le_one p X
  calc
    (beta p X)^2 = beta p X * beta p X := by rw [pow_two]
    _ ≤ beta p X * 1 := mul_le_mul_of_nonneg_left hle1 hnonneg
    _ = beta p X := by ring

end Erdos291
