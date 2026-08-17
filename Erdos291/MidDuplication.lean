import Erdos291.GapResultant
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Erdős #291 — the duplication identity of the Pochhammer product

For `P_r(X) = ∏_{j=1}^r (X + j)` the classical duplication formula reads

    `P_{2r}(2X) = 2^{2r} P_r(X) P_r(X - 1/2)`

over `ℚ[X]`.  This file formalizes its integral-coefficient form

    `P_{2r}(2X) = 2^r · P_r(X) · ∏_{j=1}^r (2X + 2j - 1)`,

together with the differentiated version

    `2 · Q_{2r}(2X) = (P_{2r}(2X))'`.

Both are stated over `ℤ[X]` using `Pd` and `Qd` from `GapResultant`, so they
reduce mod `p` without any rational denominators.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

open Polynomial

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The odd-factor product `∏_{j=1}^r (2X + 2j - 1)` over `ℤ`. -/
noncomputable def oddProductZ (r : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.Icc 1 r,
    ((2 : Polynomial ℤ) * Polynomial.X + Polynomial.C ((2 * j - 1 : ℕ) : ℤ))

/-- Appending the last factor: `Pd (d+1) = Pd d · (X + d + 1)`. -/
lemma Pd_succ (d : ℕ) :
    Pd (d + 1) = Pd d * (Polynomial.X + Polynomial.C ((d + 1 : ℕ) : ℤ)) := by
  rw [Pd]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ d + 1)]
  rfl

/-- Appending the last odd factor. -/
lemma oddProductZ_succ (r : ℕ) :
    oddProductZ (r + 1) =
      oddProductZ r * ((2 : Polynomial ℤ) * Polynomial.X +
        Polynomial.C ((2 * r + 1 : ℕ) : ℤ)) := by
  rw [oddProductZ]
  rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
  rfl

/-- Doubling the last linear factor: `2·(X + r + 1) = 2X + 2r + 2` over `ℤ`. -/
lemma two_mul_X_add_C_add_one (r : ℕ) :
    (Polynomial.C (2 : ℤ)) * (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ℤ)) =
      (Polynomial.C (2 : ℤ)) * Polynomial.X + Polynomial.C ((2 * r + 2 : ℕ) : ℤ) := by
  rw [mul_add]
  rw [← Polynomial.C_mul]
  have hc : (2 * ((r + 1 : ℕ) : ℤ)) = ((2 * r + 2 : ℕ) : ℤ) := by
    norm_num
    ring
  rw [hc]

/-- The integral duplication identity:
`P_{2r}(2X) = 2^r · P_r(X) · ∏_{j=1}^r (2X + 2j - 1)`. -/
theorem Pd_comp_two_mul_eq_C_pow_mul_self_mul_oddProduct (r : ℕ) :
    (Pd (2 * r)).comp ((2 : Polynomial ℤ) * Polynomial.X) =
      Polynomial.C ((2 ^ r : ℕ) : ℤ) * Pd r * oddProductZ r := by
  induction r with
  | zero =>
      simp [Pd, oddProductZ]
  | succ r ih =>
      have hP2r1 : Pd (2 * r + 1) = Pd (2 * r) *
          (Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ℤ)) := Pd_succ (2 * r)
      have hP2r2 : Pd (2 * (r + 1)) = Pd (2 * r + 1) *
          (Polynomial.X + Polynomial.C ((2 * r + 2 : ℕ) : ℤ)) := by
        rw [show 2 * (r + 1) = 2 * r + 1 + 1 by omega]
        exact Pd_succ (2 * r + 1)
      have hpow : ((2 ^ (r + 1) : ℕ) : ℤ) = ((2 ^ r : ℕ) : ℤ) * 2 := by
        rw [pow_succ]
        norm_num
      calc
        (Pd (2 * (r + 1))).comp ((2 : Polynomial ℤ) * Polynomial.X)
            = ((Pd (2 * r) * (Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ℤ))) *
                (Polynomial.X + Polynomial.C ((2 * r + 2 : ℕ) : ℤ))).comp
                  ((2 : Polynomial ℤ) * Polynomial.X) := by
                  rw [hP2r2, hP2r1]
        _ = ((Pd (2 * r)).comp ((2 : Polynomial ℤ) * Polynomial.X)) *
              (((2 : Polynomial ℤ) * Polynomial.X) + Polynomial.C ((2 * r + 1 : ℕ) : ℤ)) *
              (((2 : Polynomial ℤ) * Polynomial.X) + Polynomial.C ((2 * r + 2 : ℕ) : ℤ)) := by
              simp only [mul_comp, add_comp, X_comp, C_comp]
        _ = (Polynomial.C ((2 ^ r : ℕ) : ℤ) * Pd r * oddProductZ r) *
              (((2 : Polynomial ℤ) * Polynomial.X) + Polynomial.C ((2 * r + 1 : ℕ) : ℤ)) *
              (((2 : Polynomial ℤ) * Polynomial.X) + Polynomial.C ((2 * r + 2 : ℕ) : ℤ)) := by
              rw [ih]
        _ = Polynomial.C ((2 ^ (r + 1) : ℕ) : ℤ) * Pd (r + 1) * oddProductZ (r + 1) := by
              rw [hpow, Pd_succ, oddProductZ_succ]
              simp only [Polynomial.C_mul]
              rw [show (2 : Polynomial ℤ) = Polynomial.C (2 : ℤ) by norm_num]
              rw [mul_assoc (Polynomial.C ((2 ^ r : ℕ) : ℤ)) (Polynomial.C (2 : ℤ))
                (Pd r * (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ℤ)))]
              rw [← mul_assoc (Polynomial.C (2 : ℤ)) (Pd r)
                (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ℤ))]
              rw [mul_comm (Polynomial.C (2 : ℤ)) (Pd r)]
              rw [mul_assoc (Pd r) (Polynomial.C (2 : ℤ))
                (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ℤ))]
              have hrearr : (Polynomial.C ((2 ^ r : ℕ) : ℤ) *
                  (Pd r * (Polynomial.C (2 : ℤ) *
                    (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ℤ))))) *
                  (oddProductZ r * (Polynomial.C (2 : ℤ) * Polynomial.X +
                    Polynomial.C ((2 * r + 1 : ℕ) : ℤ))) =
                Polynomial.C ((2 ^ r : ℕ) : ℤ) * Pd r * oddProductZ r *
                  (Polynomial.C (2 : ℤ) * Polynomial.X +
                    Polynomial.C ((2 * r + 1 : ℕ) : ℤ)) *
                  (Polynomial.C (2 : ℤ) *
                    (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ℤ))) := by
                ring
              rw [hrearr]
              rw [two_mul_X_add_C_add_one r]

/-- The differentiated duplication identity:
`(P_{2r}(2X))' = 2 · Q_{2r}(2X)`. -/
theorem derivative_Pd_comp_two_mul_eq_two_mul_Q_comp (r : ℕ) :
    Polynomial.derivative ((Pd (2 * r)).comp ((2 : Polynomial ℤ) * Polynomial.X)) =
      (2 : Polynomial ℤ) * (Qd (2 * r)).comp ((2 : Polynomial ℤ) * Polynomial.X) := by
  rw [Polynomial.derivative_comp]
  have hd : Polynomial.derivative ((2 : Polynomial ℤ) * Polynomial.X) =
      (2 : Polynomial ℤ) := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X]
    simp
  rw [hd]
  dsimp [Qd]

end

end Erdos291
