import Erdos291.BlockMid
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Reducing `Wmid → 0` to the row-count second moment `Qmid = o(R)`

For each `r` in the dyadic block `[R, 2R)` let `rowCountMid R x r` be the number of
middle bad prime factors of `H_r`:

  `2r + 1 < p ≤ r²`, `p` prime, `p ∣ num (H_r)`, `p ≤ x`.

Write `Bmid R x = Σ_r rowCountMid R x r` for the total row count and
`Qmid R x = Σ_r (rowCountMid R x r)²` for its second moment.  This file proves the
three formal reductions that move the goal from `Wmid` to `Qmid`:

1. **Lemma 14a.** Each counted pair contributes weight `1/(p-1) ≤ 1/(2R)`, hence

     `Wmid R x ≤ Bmid R x / (2R)`.

2. **Lemma 14b.** Cauchy–Schwarz on the `R` rows:

     `Bmid R x ^ 2 ≤ R * Qmid R x`.

3. **Lemma 14c.** If `Qmid R x = o(R)` uniformly in `x` (as `R → ∞`), then
   `Bmid R x ≤ sqrt ε · R` for large `R`, and therefore `Wmid R x → 0` uniformly
   in `x`.  This is the capstone that transfers a future second-moment estimate
   to the whole remaining goal of the project.
-/

open scoped BigOperators

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The number of middle bad prime factors of `H_r`: primes `p ≤ x` with
`2r + 1 < p ≤ r²` and `p ∣ num (H_r)`. -/
noncomputable def rowCountMid (R x r : ℕ) : ℕ :=
  ((Finset.Icc 2 x).filter
    (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧
      Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)).card

/-- The total row count over the dyadic block `[R, 2R)`. -/
noncomputable def Bmid (R x : ℕ) : ℕ :=
  ∑ r ∈ Finset.Ico R (2 * R), rowCountMid R x r

/-- The second moment of the row counts over the dyadic block `[R, 2R)`. -/
noncomputable def Qmid (R x : ℕ) : ℕ :=
  ∑ r ∈ Finset.Ico R (2 * R), (rowCountMid R x r) ^ 2

/-- **Lemma 14a.** `Wmid` is controlled by the row count: every counted pair has
weight `1/(p-1) ≤ 1/(2R)`, so `Wmid R x ≤ Bmid R x / (2R)`. -/
theorem Wmid_le_Bmid_div_two_mul_R (R x : ℕ) (hR : 0 < R) :
    Wmid R x ≤ (Bmid R x : ℝ) / (2 * (R : ℝ)) := by
  calc
    Wmid R x = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (Finset.Icc 2 x).filter
            (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧
              Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
          (1 / ((p - 1 : ℕ) : ℝ)) := by
      rfl
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
        (rowCountMid R x r : ℝ) * (1 / (2 * (R : ℝ))) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hrIco := Finset.mem_Ico.mp hr
          have hRr : R ≤ r := hrIco.1
          have hRposR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
          have h2Rpos : 0 < (2 * (R : ℝ)) := by positivity
          have hinner := Finset.sum_le_card_nsmul
            ((Finset.Icc 2 x).filter
              (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧
                Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num))
            (fun p => (1 / ((p - 1 : ℕ) : ℝ)))
            (1 / (2 * (R : ℝ))) (by
              intro p hp
              have hpF := Finset.mem_filter.mp hp
              have hcond := hpF.2
              rcases hcond with ⟨h2rp, _hle, _hpPrime, _hdvd⟩
              have h2R_le : 2 * R ≤ p - 1 := by omega
              have hppos : 0 < ((p - 1 : ℕ) : ℝ) := by
                have hpne : 0 < p - 1 := by omega
                exact_mod_cast hpne
              have hcast : (2 * (R : ℝ)) ≤ ((p - 1 : ℕ) : ℝ) := by
                exact_mod_cast h2R_le
              exact one_div_le_one_div_of_le h2Rpos hcast)
          simpa [rowCountMid, nsmul_eq_mul] using hinner
    _ = ((∑ r ∈ Finset.Ico R (2 * R), rowCountMid R x r : ℕ) : ℝ) *
        (1 / (2 * (R : ℝ))) := by
          rw [← Finset.sum_mul, ← Nat.cast_sum]
    _ = (Bmid R x : ℝ) * (1 / (2 * (R : ℝ))) := by
          rw [Bmid]
    _ = (Bmid R x : ℝ) / (2 * (R : ℝ)) := by
          rw [mul_one_div]

/-- **Lemma 14b.** Cauchy–Schwarz for the row counts: the square of the total is
bounded by the number of rows times the sum of squares. -/
theorem Bmid_sq_le_R_mul_Qmid (R x : ℕ) :
    (Bmid R x) ^ 2 ≤ R * Qmid R x := by
  let f : ℕ → ℝ := fun r => (rowCountMid R x r : ℝ)
  have hCauchy := sq_sum_le_card_mul_sum_sq (s := Finset.Ico R (2 * R)) (f := f)
  have hcard : (Finset.Ico R (2 * R)).card = R := by
    simp
    omega
  have hBsum : (Bmid R x : ℝ) = ∑ r ∈ Finset.Ico R (2 * R), f r := by
    rw [Bmid]
    push_cast
    rfl
  have hQsum : (Qmid R x : ℝ) = ∑ r ∈ Finset.Ico R (2 * R), f r ^ 2 := by
    rw [Qmid]
    push_cast
    rfl
  have hReal : (Bmid R x : ℝ) ^ 2 ≤ (R : ℝ) * (Qmid R x : ℝ) := by
    calc
      (Bmid R x : ℝ) ^ 2 = (∑ r ∈ Finset.Ico R (2 * R), f r) ^ 2 := by
        rw [hBsum]
      _ ≤ (Finset.Ico R (2 * R)).card *
          ∑ r ∈ Finset.Ico R (2 * R), f r ^ 2 := by
            simpa [f] using hCauchy
      _ = (R : ℝ) * ∑ r ∈ Finset.Ico R (2 * R), f r ^ 2 := by
        rw [hcard]
      _ = (R : ℝ) * (Qmid R x : ℝ) := by
        rw [← hQsum]
  exact_mod_cast hReal

/-- **Lemma 14c.** Uniform `Qmid R x = o(R)` in `x` implies the uniform vanishing of
`Wmid R x`.  This is the capstone reduction of the whole project: it suffices to
prove the second moment of the row counts is `o(R)`. -/
theorem Wmid_uniformly_tends_to_zero_of_Qmid_o_R
    (hQ : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ,
      (Qmid R x : ℝ) ≤ ε * (R : ℝ)) :
    ∀ δ : ℝ, 0 < δ → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ δ := by
  intro δ hδ
  have hδsq_pos : 0 < δ ^ 2 := sq_pos_of_ne_zero (ne_of_gt hδ)
  rcases hQ (δ ^ 2) hδsq_pos with ⟨Rq, hRq⟩
  refine ⟨max Rq 1, ?_⟩
  intro R hR x
  have hRqle : Rq ≤ R := le_trans (le_max_left Rq 1) hR
  have hR1 : 1 ≤ R := le_trans (le_max_right Rq 1) hR
  have hRpos : 0 < R := by omega
  have hQle : (Qmid R x : ℝ) ≤ δ ^ 2 * (R : ℝ) := hRq R hRqle x
  have hWle : Wmid R x ≤ (Bmid R x : ℝ) / (2 * (R : ℝ)) :=
    Wmid_le_Bmid_div_two_mul_R R x hRpos
  have hBsq : (Bmid R x : ℝ) ^ 2 ≤ (R : ℝ) * (Qmid R x : ℝ) := by
    exact_mod_cast Bmid_sq_le_R_mul_Qmid R x
  have hBsq_delta : (Bmid R x : ℝ) ^ 2 ≤ (δ * (R : ℝ)) ^ 2 := by
    calc
      (Bmid R x : ℝ) ^ 2 ≤ (R : ℝ) * (Qmid R x : ℝ) := hBsq
      _ ≤ (R : ℝ) * (δ ^ 2 * (R : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hQle (Nat.cast_nonneg _)
      _ = (δ * (R : ℝ)) ^ 2 := by ring
  have hδRnonneg : 0 ≤ δ * (R : ℝ) :=
    mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hBle : (Bmid R x : ℝ) ≤ δ * (R : ℝ) :=
    le_of_sq_le_sq hBsq_delta hδRnonneg
  have h2Rpos : 0 < (2 * (R : ℝ)) := by positivity
  calc
    Wmid R x ≤ (Bmid R x : ℝ) / (2 * (R : ℝ)) := hWle
    _ ≤ (δ * (R : ℝ)) / (2 * (R : ℝ)) := by
      exact div_le_div_of_nonneg_right hBle (le_of_lt h2Rpos)
    _ ≤ δ := by
      rw [div_le_iff₀ h2Rpos]
      nlinarith [hδ]

end Erdos291
