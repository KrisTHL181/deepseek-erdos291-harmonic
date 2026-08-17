import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Erdős #291 — the step-4 difference connection of the scaled distance polynomial

This file formalizes the polynomial identities behind sections 1-2 of the
difference-connection analysis (ChatGPT report 20260817-2238):

    G_r(T) := ∏_{j=1}^r (T + 4j).

1. **The step identity.**  Over any ring,

       (T + 4) · G_r(T + 4) = (T + 4r + 4) · G_r(T).

   In particular, writing `p = 4r + 2s + 1` and `α = 2s - 3`, one has
   `4r + 4 ≡ -α (mod p)`, so modulo `p`

       G_r(T + 4) = ((T - α)/(T + 4)) · G_r(T),

   the rank-one step-4 difference module of the report.

2. **The reflection.**  Over any ring,

       G_r(-4(r+1) - T) = (-1)^r · G_r(T).

   Modulo `p = 4r + 2s + 1` this is `G_r(α - T) = (-1)^r G_r(T)`.

Everything is stated at polynomial level (no rational functions), so the
identities reduce mod `p` without denominators.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The scaled distance polynomial `G_r(T) = ∏_{j=1}^r (T + 4j)` over `ℤ`. -/
noncomputable def GpolyZ (r : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.Icc 1 r, (Polynomial.X + Polynomial.C ((4 * j : ℕ) : ℤ))

/-- The scaled distance polynomial reduced modulo `p`. -/
noncomputable def GpolyMod (p r : ℕ) : Polynomial (ZMod p) :=
  (GpolyZ r).map (Int.castRingHom (ZMod p))

/-- `α = 2s - 3` as an element of `ZMod p` (an integer, so it also covers `s = 1`). -/
noncomputable def alphaMod (p s : ℕ) : ZMod p := ((2 * s : ℤ) - 3 : ZMod p)

/-! ## The step identity -/

/-- The core telescoping identity over `ℤ`:
`(T + 4) · G_r(T + 4) = (T + 4r + 4) · G_r(T)`. -/
theorem GpolyZ_comp_succ_mul (r : ℕ) :
    (Polynomial.X + Polynomial.C (4 : ℤ)) *
        ((GpolyZ r).comp (Polynomial.X + Polynomial.C (4 : ℤ))) =
      (Polynomial.X + Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) * GpolyZ r := by
  induction r with
  | zero =>
      simp [GpolyZ]
  | succ r ih =>
      have hG : GpolyZ (r + 1) = GpolyZ r * (Polynomial.X + Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) := by
        unfold GpolyZ
        rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ r + 1)]
      rw [hG]
      rw [Polynomial.mul_comp]
      simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
      have hcast : (Polynomial.X + Polynomial.C (4 : ℤ) +
            Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) =
          Polynomial.X + Polynomial.C ((4 * (r + 2) : ℕ) : ℤ) := by
        rw [show Polynomial.X + Polynomial.C (4 : ℤ) + Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)
            = Polynomial.X + (Polynomial.C (4 : ℤ) + Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) by ring]
        rw [← Polynomial.C_add]
        congr 1
        have hnat : 4 * (r + 2) = 4 * (r + 1) + 4 := by omega
        rw [hnat]
        norm_num [Nat.cast_add]
        ring
      rw [hcast]
      rw [show r + 1 + 1 = r + 2 by omega]
      rw [← mul_assoc]
      rw [ih]
      ring

/-! ## The reflection -/

/-- The reflection identity over `ℤ`:
`G_r(-4(r+1) - T) = (-1)^r · G_r(T)`. -/
theorem GpolyZ_comp_neg_mul (r : ℕ) :
    (GpolyZ r).comp (-Polynomial.X - Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) =
      Polynomial.C ((-1 : ℤ) ^ r) * GpolyZ r := by
  unfold GpolyZ
  rw [Polynomial.prod_comp]
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hrefl : (∏ j ∈ Finset.Icc 1 r,
        (((-Polynomial.X - Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) +
          Polynomial.C ((4 * j : ℕ) : ℤ)))) =
      ∏ j ∈ Finset.Icc 1 r, (-(Polynomial.X + Polynomial.C ((4 * j : ℕ) : ℤ))) := by
    refine Finset.prod_bij (fun j hj => r + 1 - j) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_Icc]
      have hj' := Finset.mem_Icc.mp hj
      omega
    · intro i hi j hj h
      have hi' := Finset.mem_Icc.mp hi
      have hj' := Finset.mem_Icc.mp hj
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨r + 1 - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      calc
        (-Polynomial.X - Polynomial.C ((4 * (r + 1) : ℕ) : ℤ)) +
            Polynomial.C ((4 * j : ℕ) : ℤ)
            = -Polynomial.X - (Polynomial.C ((4 * (r + 1) : ℕ) : ℤ) -
                Polynomial.C ((4 * j : ℕ) : ℤ)) := by ring
        _ = -Polynomial.X - Polynomial.C (((4 * (r + 1) : ℕ) : ℤ) - (4 * j : ℕ)) := by
              rw [← Polynomial.C_sub]
        _ = -Polynomial.X - Polynomial.C (((4 * (r + 1) - 4 * j : ℕ) : ℤ)) := by
              rw [Nat.cast_sub (by omega : 4 * j ≤ 4 * (r + 1))]
        _ = -Polynomial.X - Polynomial.C (((4 * (r + 1 - j) : ℕ) : ℤ)) := by
              congr 1
              congr 1
              congr 1
              omega
        _ = -(Polynomial.X + Polynomial.C ((4 * (r + 1 - j) : ℕ) : ℤ)) := by ring
  rw [hrefl]
  rw [Finset.prod_neg]
  have hcard : (Finset.Icc 1 r).card = r := by
    rw [Nat.card_Icc]
    omega
  rw [hcard]
  have hnegpow : (-1 : Polynomial ℤ) ^ r = Polynomial.C ((-1 : ℤ) ^ r) := by
    rw [show (-1 : Polynomial ℤ) = Polynomial.C (-1 : ℤ) by norm_num]
    rw [← Polynomial.C_pow]
  rw [hnegpow]

end

end Erdos291
