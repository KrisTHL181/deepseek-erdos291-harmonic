import Erdos291.MidAttackLine2
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Erdős #291 — Attack Line 3: arithmetic (ℤ) remainder content

This file lifts the middle-polynomial machinery from `ZMod p` to `ℤ`, so that
the single vanishing condition `H_{2r} = 0` can be expressed as a divisibility
of the *content* of an explicit remainder polynomial.  The main objects are the
integer tail products and the quartic

    `A_poly r = X (X - r) (X + r + 1) (X + 2r + 1)`,

whose four roots over `ZMod p` are `0, r, p-1-2r, p-1-r`.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The integer plus product `∏_{j=a}^b (X + j)`. -/
noncomputable def plusProductZ (a b : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc a b, (Polynomial.X + Polynomial.C (i : ℤ))

/-- The integer mid tail product `∏_{j=r+1}^e (X + j)`. -/
noncomputable def midTailProductZ (r e : ℕ) : Polynomial ℤ := plusProductZ (r + 1) e

/-- The derivative of the integer mid tail product. -/
noncomputable def midTailDerivativeZ (r e : ℕ) : Polynomial ℤ :=
  Polynomial.derivative (midTailProductZ r e)

/-- The integer prefix product `∏_{j=r+1}^{e-r} (X + j)`. -/
noncomputable def midPrefixProductZ (r e : ℕ) : Polynomial ℤ := plusProductZ (r + 1) (e - r)

/-- The derivative of the integer prefix product. -/
noncomputable def midPrefixDerivativeZ (r e : ℕ) : Polynomial ℤ :=
  Polynomial.derivative (midPrefixProductZ r e)

/-- The quartic whose roots over `ZMod p` are `0, r, p-1-2r, p-1-r`. -/
noncomputable def A_poly (r : ℕ) : Polynomial ℤ :=
  Polynomial.X * (Polynomial.X - Polynomial.C (r : ℤ)) *
    (Polynomial.X + Polynomial.C ((r : ℤ) + 1)) *
    (Polynomial.X + Polynomial.C (2 * (r : ℤ) + 1))

/-- The reduction of `A_poly r` modulo `p`. -/
noncomputable def A_poly_mod (p r : ℕ) : Polynomial (ZMod p) :=
  (A_poly r).map (Int.castRingHom (ZMod p))

/-- The remainder of `Qd r` modulo the monic quartic `A_poly r`. -/
noncomputable def RemainderR (r : ℕ) : Polynomial ℤ := (Qd r) %ₘ (A_poly r)

/-- Arithmetic hypothesis: for `r ≥ 1`, every prime dividing the content of the
remainder of `Qd r` modulo `A_poly r` satisfies `p ≤ 4r + 1`. -/
def HA_arithmetic_remainder_content : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ p : ℕ, Nat.Prime p →
    p ∣ (Polynomial.content (RemainderR r)).natAbs → p ≤ 4 * r + 1

/-! ## 1. Basic properties of the integer plus products -/

/-- `plusProductZ a b` is monic. -/
lemma plusProductZ_monic (a b : ℕ) : (plusProductZ a b).Monic := by
  rw [plusProductZ]
  exact monic_prod_of_monic _ _ fun i hi => monic_X_add_C (i : ℤ)

/-- `plusProductZ a b` has degree `b + 1 - a`. -/
lemma plusProductZ_natDegree (a b : ℕ) : (plusProductZ a b).natDegree = b + 1 - a := by
  rw [plusProductZ]
  have hmonic : ∀ i ∈ Finset.Icc a b, Monic (Polynomial.X + Polynomial.C (i : ℤ)) := by
    intro i hi
    exact monic_X_add_C (i : ℤ)
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc a b)
    (fun i => Polynomial.X + Polynomial.C (i : ℤ)) hmonic]
  simp only [Polynomial.natDegree_X_add_C]
  rw [← Finset.card_eq_sum_ones, Nat.card_Icc]

/-- The reduction of `plusProductZ a b` modulo `p` is `plusProduct p a b`. -/
lemma plusProductZ_map (p a b : ℕ) :
    (plusProductZ a b).map (Int.castRingHom (ZMod p)) = plusProduct p a b := by
  rw [plusProductZ, plusProduct]
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- The reduction of `midTailProductZ r e` modulo `p` is `midTailProduct p r e`. -/
lemma midTailProductZ_map (p r e : ℕ) :
    (midTailProductZ r e).map (Int.castRingHom (ZMod p)) = midTailProduct p r e := by
  rw [midTailProductZ, midTailProduct]
  exact plusProductZ_map p (r + 1) e

/-- The reduction of `midTailDerivativeZ r e` modulo `p` is the derivative of
`midTailProduct p r e`. -/
lemma midTailDerivativeZ_map (p r e : ℕ) :
    (midTailDerivativeZ r e).map (Int.castRingHom (ZMod p)) =
      Polynomial.derivative (midTailProduct p r e) := by
  rw [midTailDerivativeZ, ← Polynomial.derivative_map]
  exact congrArg Polynomial.derivative (midTailProductZ_map p r e)

/-- The reduction of `midPrefixProductZ r e` modulo `p` is
`midTailProduct p r (e - r)`. -/
lemma midPrefixProductZ_map (p r e : ℕ) :
    (midPrefixProductZ r e).map (Int.castRingHom (ZMod p)) =
      midTailProduct p r (e - r) := by
  rw [midPrefixProductZ, midTailProduct]
  exact plusProductZ_map p (r + 1) (e - r)

/-- The reduction of `midPrefixDerivativeZ r e` modulo `p` is the derivative of
`midTailProduct p r (e - r)`. -/
lemma midPrefixDerivativeZ_map (p r e : ℕ) :
    (midPrefixDerivativeZ r e).map (Int.castRingHom (ZMod p)) =
      Polynomial.derivative (midTailProduct p r (e - r)) := by
  rw [midPrefixDerivativeZ, ← Polynomial.derivative_map]
  exact congrArg Polynomial.derivative (midPrefixProductZ_map p r e)

/-! ## 2. Splitting and differentiating the integer distance polynomial -/

/-- `Pd e = Pd r * midTailProductZ r e` for `r ≤ e`. -/
lemma Pd_eq_Pd_mul_midTailProductZ (r e : ℕ) (hre : r ≤ e) :
    Pd e = Pd r * midTailProductZ r e := by
  classical
  have hIcc : Finset.Icc 1 e = Finset.Icc 1 r ∪ Finset.Icc (r + 1) e := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) e) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hx1 : x ≤ r := (Finset.mem_Icc.mp hx).2
    have hx2 : r + 1 ≤ x := (Finset.mem_Icc.mp hx').1
    omega
  change (∏ i ∈ Finset.Icc 1 e, (Polynomial.X + Polynomial.C (i : ℤ))) =
    (∏ i ∈ Finset.Icc 1 r, (Polynomial.X + Polynomial.C (i : ℤ))) *
      (∏ i ∈ Finset.Icc (r + 1) e, (Polynomial.X + Polynomial.C (i : ℤ)))
  rw [hIcc, Finset.prod_union hdisj]

/-- `Qd e = Qd r * midTailProductZ r e + Pd r * midTailDerivativeZ r e` for `r ≤ e`. -/
lemma Qd_eq_Qd_mul_midTailProductZ_add_Pd_mul_midTailDerivativeZ (r e : ℕ)
    (hre : r ≤ e) :
    Qd e = Qd r * midTailProductZ r e + Pd r * midTailDerivativeZ r e := by
  have hP := Pd_eq_Pd_mul_midTailProductZ r e hre
  change Polynomial.derivative (Pd e) = Qd r * midTailProductZ r e +
    Pd r * Polynomial.derivative (midTailProductZ r e)
  rw [hP, Polynomial.derivative_mul]
  rfl

/-! ## 4. Resultant decomposition over ℤ -/

/-- The integer resultant factors as `resultant (Qd r) (Pd r)` times
`resultant (Qd r) (midTailDerivativeZ r e)`, for `1 ≤ r < e`. -/
lemma resultant_Qd_Qe_eq_resultant_Qd_Pd_mul_resultant_Qd_midTailDerivativeZ
    (r e : ℕ) (hr1 : 1 ≤ r) (hre : r ≤ e) (hlt : r < e) :
    (Polynomial.resultant (Qd r) (Qd e) : ℤ) =
      (Polynomial.resultant (Qd r) (Pd r) : ℤ) *
        (Polynomial.resultant (Qd r) (midTailDerivativeZ r e) : ℤ) := by
  let S : Polynomial ℤ := midTailProductZ r e
  let T : Polynomial ℤ := Polynomial.derivative S
  have hSdeg : S.natDegree = e - r := by
    dsimp [S, midTailProductZ]
    rw [plusProductZ_natDegree (r + 1) e]
    omega
  have hSm : S.Monic := by dsimp [S]; exact plusProductZ_monic (r + 1) e
  have hS_ne : S ≠ 0 := hSm.ne_zero
  have hTdeg : T.natDegree = e - r - 1 := by
    dsimp [T]
    rw [Polynomial.natDegree_derivative, hSdeg]
  have hT_ne : T ≠ 0 := by
    intro hT0
    have hSdeg_ne : S.natDegree ≠ 0 := by
      rw [hSdeg]
      omega
    have hder0 : S.natDegree = 0 := (Polynomial.derivative_eq_zero (p := S)).mp (by simpa [T] using hT0)
    exact hSdeg_ne hder0
  have hQrdeg : (Qd r).natDegree = r - 1 := Qd_natDegree r
  have hQedeg : (Qd e).natDegree = e - 1 := Qd_natDegree e
  have hPdeg : (Pd r).natDegree = r := Pd_natDegree r
  have hPTdeg_add : (Pd r * T).natDegree = (Pd r).natDegree + T.natDegree :=
    (Pd_monic r).natDegree_mul' hT_ne
  have hPTdeg : (Pd r * T).natDegree = e - 1 := by
    rw [hPTdeg_add, hPdeg, hTdeg]
    omega
  have hp_add : S.natDegree + (Qd r).natDegree ≤ (Pd r * T).natDegree := by
    rw [hSdeg, hQrdeg, hPTdeg]
    omega
  have hQe_decomp := Qd_eq_Qd_mul_midTailProductZ_add_Pd_mul_midTailDerivativeZ r e hre
  have hQe' : Qd e = Pd r * T + Qd r * S := by
    rw [hQe_decomp]
    dsimp [T, midTailDerivativeZ]
    ring
  have h_add := Polynomial.resultant_add_mul_right (f := Qd r) (g := Pd r * T) (p := S)
    (m := (Qd r).natDegree) (n := (Pd r * T).natDegree) hp_add le_rfl
  have hmain_add : Polynomial.resultant (Qd r) (Qd e) (Qd r).natDegree (Pd r * T).natDegree =
      Polynomial.resultant (Qd r) (Pd r * T) (Qd r).natDegree (Pd r * T).natDegree := by
    rw [hQe']
    exact h_add
  have h_mul := Polynomial.resultant_mul_right (f := Qd r) (g₁ := Pd r) (g₂ := T)
    (m := (Qd r).natDegree) le_rfl
  have hmain_mul : Polynomial.resultant (Qd r) (Pd r * T) (Qd r).natDegree (Pd r * T).natDegree =
      Polynomial.resultant (Qd r) (Pd r) * Polynomial.resultant (Qd r) T := by
    rw [hPTdeg_add]
    simpa using h_mul
  have hmain : Polynomial.resultant (Qd r) (Qd e) =
      Polynomial.resultant (Qd r) (Pd r) * Polynomial.resultant (Qd r) T := by
    have hmain' : Polynomial.resultant (Qd r) (Qd e) (Qd r).natDegree (Pd r * T).natDegree =
        Polynomial.resultant (Qd r) (Pd r) * Polynomial.resultant (Qd r) T := by
      rw [hmain_add, hmain_mul]
    simpa [hQedeg, hPTdeg] using hmain'
  simpa [S, T, midTailDerivativeZ] using hmain

/-! ## 5. The symmetry `Qd d (-X - C(d+1)) = (-1)^{d+1} Qd d` -/

/-- Composition distributes over finite products. -/
private lemma comp_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ) (q : Polynomial ℤ) :
    (∏ i ∈ s, f i).comp q = ∏ i ∈ s, (f i).comp q := by
  classical
  rw [Polynomial.comp, Polynomial.eval₂_finset_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rfl

/-- Reindexing the product `Pd d` by `i ↦ d + 1 - i` gives the symmetry
`(Pd d).comp(-X - C(d+1)) = (-1)^d Pd d`. -/
lemma Pd_comp_neg_X_sub_C_add_one (d : ℕ) :
    (Pd d).comp (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) = (-1 : ℤ) ^ d * Pd d := by
  classical
  have hfac : ∀ i ∈ Finset.Icc 1 d,
      (Polynomial.X + Polynomial.C (i : ℤ)).comp
        (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) =
        -(Polynomial.X + Polynomial.C ((d + 1 - i : ℕ) : ℤ)) := by
    intro i hi
    have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
    have hcast : ((d + 1 - i : ℕ) : ℤ) = (d : ℤ) + 1 - i := by
      rw [Nat.cast_sub (by omega : i ≤ d + 1), Nat.cast_add, Nat.cast_one]
    calc
      (Polynomial.X + Polynomial.C (i : ℤ)).comp
          (-Polynomial.X - Polynomial.C ((d : ℤ) + 1))
          = (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) + Polynomial.C (i : ℤ) := by
              rw [Polynomial.comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
      _ = -(Polynomial.X + Polynomial.C ((d + 1 - i : ℕ) : ℤ)) := by
              rw [hcast, Polynomial.C_sub]
              ring
  have hreindex : (∏ i ∈ Finset.Icc 1 d,
      (Polynomial.X + Polynomial.C ((d + 1 - i : ℕ) : ℤ))) = Pd d := by
    rw [Pd]
    refine Finset.prod_bij (fun i hi => d + 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc]
      have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ h
      have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ d := Finset.mem_Icc.mp hi₁
      have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ d := Finset.mem_Icc.mp hi₂
      omega
    · intro j hj
      have hj' : 1 ≤ j ∧ j ≤ d := Finset.mem_Icc.mp hj
      refine ⟨d + 1 - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro i hi
      rfl
  have hcomp : (Pd d).comp (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) =
      Polynomial.C (-1)^d * Pd d := by
    calc
      (Pd d).comp (-Polynomial.X - Polynomial.C ((d : ℤ) + 1))
          = (∏ i ∈ Finset.Icc 1 d,
              (Polynomial.X + Polynomial.C (i : ℤ))).comp
                (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) := by rw [Pd]
      _ = ∏ i ∈ Finset.Icc 1 d,
              (Polynomial.X + Polynomial.C (i : ℤ)).comp
                (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) := by
            rw [comp_prod]
      _ = ∏ i ∈ Finset.Icc 1 d,
              (-(Polynomial.X + Polynomial.C ((d + 1 - i : ℕ) : ℤ))) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            exact hfac i hi
      _ = Polynomial.C (-1)^d * Pd d := by
            rw [Finset.prod_neg, hreindex]
            simp
  simpa using hcomp

/-- Differentiating the `Pd` symmetry gives `Qd d (-X - C(d+1)) = (-1)^{d+1} Qd d`. -/
lemma Qd_comp_neg_X_sub_C_add_one (d : ℕ) :
    (Qd d).comp (-Polynomial.X - Polynomial.C ((d : ℤ) + 1)) = (-1 : ℤ) ^ (d + 1) * Qd d := by
  let q : Polynomial ℤ := -Polynomial.X - Polynomial.C ((d : ℤ) + 1)
  have hP := Pd_comp_neg_X_sub_C_add_one d
  have hder := congrArg Polynomial.derivative hP
  have hderq : Polynomial.derivative q = (-1 : Polynomial ℤ) := by
    dsimp [q]
    rw [Polynomial.derivative_sub, Polynomial.derivative_neg, Polynomial.derivative_X,
      Polynomial.derivative_C]
    simp
  have hder_lhs : Polynomial.derivative ((Pd d).comp q) =
      (-1 : Polynomial ℤ) * (Qd d).comp q := by
    rw [Polynomial.derivative_comp, hderq]
    dsimp [Qd]
  have hder_rhs : Polynomial.derivative (Polynomial.C (-1)^d * Pd d) =
      Polynomial.C (-1)^d * Qd d := by
    rw [← Polynomial.C_pow]
    rw [Polynomial.derivative_C_mul]
    dsimp [Qd]
  have hmain : (-1 : Polynomial ℤ) * (Qd d).comp q = Polynomial.C (-1)^d * Qd d := by
    rw [hder_lhs] at hder
    change (-1 : Polynomial ℤ) * (Qd d).comp q =
      Polynomial.derivative (Polynomial.C (-1)^d * Pd d) at hder
    rw [hder_rhs] at hder
    exact hder
  have hcomp : (Qd d).comp q = Polynomial.C (-1)^(d + 1) * Qd d := by
    calc
      (Qd d).comp q = (-1 : Polynomial ℤ) * ((-1 : Polynomial ℤ) * (Qd d).comp q) := by
            ring
      _ = (-1 : Polynomial ℤ) * (Polynomial.C (-1)^d * Qd d) := by rw [hmain]
      _ = Polynomial.C (-1)^(d + 1) * Qd d := by
            simp [pow_succ]
  simpa [q] using hcomp

/-! ## 6. Resultant shift symmetry (declared as a hypothesis) -/

/-- The shift symmetry of the integer resultant
`res(Qd a, (Qd b).comp(X + C a)) = res(Qd b, (Qd a).comp(X + C b))`.
The intended proof goes through the splitting field of `Qd a` and the
symmetry lemma `Qd_comp_neg_X_sub_C_add_one`; it is not yet formalized. -/
def HA_resultant_Qd_shift_symm : Prop :=
  ∀ a b : ℕ,
    (Polynomial.resultant (Qd a) ((Qd b).comp (Polynomial.X + Polynomial.C (a : ℤ))) : ℤ) =
    (Polynomial.resultant (Qd b) ((Qd a).comp (Polynomial.X + Polynomial.C (b : ℤ))) : ℤ)

/-! ## 7-9. Shift identities for the prefix product -/

/-- `plusProductZ (D+1) (D+r)` is `Pd r` shifted by `D`. -/
lemma plusProductZ_shift_eq_Pd_comp (D r : ℕ) :
    plusProductZ (D + 1) (D + r) = (Pd r).comp (Polynomial.X + Polynomial.C (D : ℤ)) := by
  classical
  have hprod_comp : (∏ j ∈ Finset.Icc 1 r,
      (Polynomial.X + Polynomial.C (j : ℤ))).comp (Polynomial.X + Polynomial.C (D : ℤ)) =
      ∏ j ∈ Finset.Icc 1 r,
        ((Polynomial.X + Polynomial.C (j : ℤ)).comp (Polynomial.X + Polynomial.C (D : ℤ))) := by
    rw [comp_prod]
  calc
    plusProductZ (D + 1) (D + r) = ∏ i ∈ Finset.Icc (D + 1) (D + r),
        (Polynomial.X + Polynomial.C (i : ℤ)) := by rfl
    _ = ∏ j ∈ Finset.Icc 1 r,
        (Polynomial.X + Polynomial.C ((D + j : ℕ) : ℤ)) := by
          refine Finset.prod_bij (fun i hi => i - D) ?_ ?_ ?_ ?_
          · intro i hi
            rw [Finset.mem_Icc]
            have hi' : D + 1 ≤ i ∧ i ≤ D + r := Finset.mem_Icc.mp hi
            omega
          · intro i₁ hi₁ i₂ hi₂ h
            have hi₁' : D + 1 ≤ i₁ ∧ i₁ ≤ D + r := Finset.mem_Icc.mp hi₁
            have hi₂' : D + 1 ≤ i₂ ∧ i₂ ≤ D + r := Finset.mem_Icc.mp hi₂
            omega
          · intro j hj
            have hj' : 1 ≤ j ∧ j ≤ r := Finset.mem_Icc.mp hj
            refine ⟨D + j, ?_, ?_⟩
            · rw [Finset.mem_Icc]
              omega
            · omega
          · intro i hi
            have hi' : D + 1 ≤ i ∧ i ≤ D + r := Finset.mem_Icc.mp hi
            congr 1
            rw [Nat.cast_add, Nat.cast_sub (by omega : D ≤ i)]
            ring_nf
    _ = ∏ j ∈ Finset.Icc 1 r,
        ((Polynomial.X + Polynomial.C (j : ℤ)).comp (Polynomial.X + Polynomial.C (D : ℤ))) := by
          refine Finset.prod_congr rfl ?_
          intro j hj
          rw [Polynomial.comp, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
          simp [Nat.cast_add]
          ring
    _ = (∏ j ∈ Finset.Icc 1 r,
        (Polynomial.X + Polynomial.C (j : ℤ))).comp (Polynomial.X + Polynomial.C (D : ℤ)) := by
          rw [hprod_comp]
    _ = (Pd r).comp (Polynomial.X + Polynomial.C (D : ℤ)) := by rw [Pd]

/-- The derivative of `plusProductZ (D+1) (D+r)` is `Qd r` shifted by `D`. -/
lemma derivative_plusProductZ_shift_eq_Qd_comp (D r : ℕ) :
    Polynomial.derivative (plusProductZ (D + 1) (D + r)) =
      (Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ)) := by
  rw [plusProductZ_shift_eq_Pd_comp]
  rw [Polynomial.derivative_comp]
  have hder : Polynomial.derivative (Polynomial.X + Polynomial.C (D : ℤ)) = 1 := by
    rw [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C]
    simp
  rw [hder]
  dsimp [Qd]
  simp

/-- `midPrefixDerivativeZ r e = (Qd (e - 2r)).comp (X + C r)` when `2r ≤ e`. -/
lemma derivative_midPrefixProductZ_eq_Qd_comp (r e : ℕ) (h : 2 * r ≤ e) :
    midPrefixDerivativeZ r e = (Qd (e - 2 * r)).comp (Polynomial.X + Polynomial.C (r : ℤ)) := by
  calc
    midPrefixDerivativeZ r e = Polynomial.derivative (plusProductZ (r + 1) (e - r)) := by
          rfl
    _ = (Qd (e - 2 * r)).comp (Polynomial.X + Polynomial.C (r : ℤ)) := by
          rw [show e - r = r + (e - 2 * r) by omega]
          exact derivative_plusProductZ_shift_eq_Qd_comp r (e - 2 * r)

/-! ## 10. The resultant `res(Qd d, Pd d)` is a unit modulo `p` -/

/-- The integer resultant `resultant (Qd d) (Pd d)` is nonzero modulo `p` for `1 ≤ d < p`. -/
lemma resultant_Qd_Pd_mod_p_ne_zero (p d : ℕ) [Fact p.Prime] (hd1 : 1 ≤ d) (hdlt : d < p) :
    ((Polynomial.resultant (Qd d) (Pd d) : ℤ) : ZMod p) ≠ 0 := by
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hdegQmap : ((Qd d).map φ).natDegree = (Qd d).natDegree := by
    rw [Qd_map p d]
    rw [Q_natDegree p d hd1 hdlt]
    rw [Qd_natDegree d]
  have hdegPmap : ((Pd d).map φ).natDegree = (Pd d).natDegree := by
    rw [Pd_map p d]
    rw [P_natDegree p d]
    rw [Pd_natDegree d]
  intro hz
  have hzmap : Polynomial.resultant ((Qd d).map φ) ((Pd d).map φ)
      (Qd d).natDegree (Pd d).natDegree = 0 := by
    rw [Polynomial.resultant_map_map]
    exact hz
  have hzQ : Polynomial.resultant (Q p d) (P p d) (Q p d).natDegree (P p d).natDegree = 0 := by
    rw [show (Q p d).natDegree = (Qd d).natDegree by rw [← Qd_map p d, hdegQmap],
      show (P p d).natDegree = (Pd d).natDegree by rw [← Pd_map p d, hdegPmap]]
    rw [← Qd_map p d, ← Pd_map p d]
    exact hzmap
  exact (resultant_Qr_Pr_ne_zero_of_lt p d hdlt) (by simpa using hzQ)

/-- If `1 ≤ d < p`, then `p` does not divide the absolute value of
`resultant (Qd d) (Pd d)`. -/
lemma not_dvd_resultant_Qd_Pd_natAbs_of_lt (p d : ℕ) [Fact p.Prime] (hd1 : 1 ≤ d)
    (hdlt : d < p) : ¬ p ∣ (Polynomial.resultant (Qd d) (Pd d)).natAbs := by
  intro hdvd
  have hz : ((Polynomial.resultant (Qd d) (Pd d) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.resultant (Qd d) (Pd d)) p).mpr
      ((Int.natCast_dvd (m := p) (n := Polynomial.resultant (Qd d) (Pd d))).mpr hdvd)
  exact (resultant_Qd_Pd_mod_p_ne_zero p d hd1 hdlt) hz

/-! ## 11-12. Divisibility of the two derivative resultants -/

/-- If `H_{2r} = 0` in the intrinsic MID regime, then `p` divides the absolute
value of `resultant (Qd r) (midTailDerivativeZ r (p - 1 - 2 * r))`. -/
lemma p_dvd_resultant_Qd_midTailDerivative_natAbs_of_harmonicSum_two_mul_r_zero
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hH2r : harmonicSum p (2 * r) = 0) :
    p ∣ (Polynomial.resultant (Qd r) (midTailDerivativeZ r (p - 1 - 2 * r))).natAbs := by
  have hp : Nat.Prime p := Fact.out
  let e : ℕ := p - 1 - 2 * r
  have hNde := (Nde_dvd_of_harmonicSum_two_mul_r_zero p r hrE hmid hH2r).1
  have hNde' : p ∣ (Polynomial.resultant (Qd r) (Qd e)).natAbs := by
    simpa [e, Nde] using hNde
  have hr1 : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have hre : r ≤ e := by dsimp [e]; omega
  have hlt : r < e := by dsimp [e]; omega
  have hdec := resultant_Qd_Qe_eq_resultant_Qd_Pd_mul_resultant_Qd_midTailDerivativeZ r e hr1 hre hlt
  have hnat : (Polynomial.resultant (Qd r) (Qd e)).natAbs =
      (Polynomial.resultant (Qd r) (Pd r)).natAbs *
        (Polynomial.resultant (Qd r) (midTailDerivativeZ r e)).natAbs := by
    rw [hdec, Int.natAbs_mul]
  have hdvd_mul : p ∣ (Polynomial.resultant (Qd r) (Pd r)).natAbs *
      (Polynomial.resultant (Qd r) (midTailDerivativeZ r e)).natAbs := by
    rwa [hnat] at hNde'
  have hdvd_or : p ∣ (Polynomial.resultant (Qd r) (Pd r)).natAbs ∨
      p ∣ (Polynomial.resultant (Qd r) (midTailDerivativeZ r e)).natAbs :=
    (Nat.Prime.dvd_mul hp).mp hdvd_mul
  have hnotP := not_dvd_resultant_Qd_Pd_natAbs_of_lt p r hr1 hr_lt
  exact (hdvd_or.resolve_left hnotP)

/-- If `H_{2r} = 0` in the intrinsic MID regime, then `p` divides the absolute
value of `resultant (Qd r) (midPrefixDerivativeZ r (p - 1 - 2 * r))`.
This uses the conditional resultant-shift symmetry `HA_resultant_Qd_shift_symm`. -/
lemma p_dvd_resultant_Qd_midPrefixDerivative_natAbs_of_harmonicSum_two_mul_r_zero
    (hSymm : HA_resultant_Qd_shift_symm)
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hH2r : harmonicSum p (2 * r) = 0) :
    p ∣ (Polynomial.resultant (Qd r) (midPrefixDerivativeZ r (p - 1 - 2 * r))).natAbs := by
  have hp : Nat.Prime p := Fact.out
  let D : ℕ := p - 1 - 4 * r
  let e : ℕ := p - 1 - 2 * r
  have hr1 : 1 ≤ r := mem_E_ge_one p r hrE
  have hD1 : 1 ≤ D := by dsimp [D]; omega
  have hDlt : D < p := by dsimp [D]; omega
  have hDr : D < D + r := by omega
  have hDre : D ≤ D + r := by omega
  have he2r : e - 2 * r = D := by dsimp [D, e]; omega
  have hNde := (Nde_dvd_of_harmonicSum_two_mul_r_zero p r hrE hmid hH2r).2
  have hNde' : p ∣ (Polynomial.resultant (Qd D) (Qd (D + r))).natAbs := by
    dsimp [D]
    have harg : p - 1 - 3 * r = (p - 1 - 4 * r) + r := by omega
    unfold Nde at hNde
    rwa [← harg]
  have hdec := resultant_Qd_Qe_eq_resultant_Qd_Pd_mul_resultant_Qd_midTailDerivativeZ D (D + r)
    hD1 hDre hDr
  have hmidDeriv : midTailDerivativeZ D (D + r) = (Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ)) := by
    rw [midTailDerivativeZ, show D + r = D + r by rfl]
    change Polynomial.derivative (plusProductZ (D + 1) (D + r)) = _
    exact derivative_plusProductZ_shift_eq_Qd_comp D r
  have hnat : (Polynomial.resultant (Qd D) (Qd (D + r))).natAbs =
      (Polynomial.resultant (Qd D) (Pd D)).natAbs *
        (Polynomial.resultant (Qd D) ((Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ)))).natAbs := by
    rw [hdec, Int.natAbs_mul]
    rw [hmidDeriv]
  have hdvd_mul : p ∣ (Polynomial.resultant (Qd D) (Pd D)).natAbs *
      (Polynomial.resultant (Qd D) ((Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ)))).natAbs := by
    rwa [hnat] at hNde'
  have hdvd_or : p ∣ (Polynomial.resultant (Qd D) (Pd D)).natAbs ∨
      p ∣ (Polynomial.resultant (Qd D) ((Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ)))).natAbs :=
    (Nat.Prime.dvd_mul hp).mp hdvd_mul
  have hnotP := not_dvd_resultant_Qd_Pd_natAbs_of_lt p D hD1 hDlt
  have hdvd_shift : p ∣
      (Polynomial.resultant (Qd D) ((Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ)))).natAbs :=
    hdvd_or.resolve_left hnotP
  have hswap : (Polynomial.resultant (Qd D) ((Qd r).comp (Polynomial.X + Polynomial.C (D : ℤ))) : ℤ) =
      (Polynomial.resultant (Qd r) ((Qd D).comp (Polynomial.X + Polynomial.C (r : ℤ))) : ℤ) := by
    have h := hSymm r D
    simpa [add_comm] using h.symm
  have hdvd_swap : p ∣
      (Polynomial.resultant (Qd r) ((Qd D).comp (Polynomial.X + Polynomial.C (r : ℤ)))).natAbs := by
    rw [← hswap]
    exact hdvd_shift
  have hpref : midPrefixDerivativeZ r e = (Qd D).comp (Polynomial.X + Polynomial.C (r : ℤ)) := by
    rw [derivative_midPrefixProductZ_eq_Qd_comp r e (by dsimp [e]; omega), he2r]
  change p ∣ (Polynomial.resultant (Qd r) (midPrefixDerivativeZ r e)).natAbs
  rw [hpref]
  exact hdvd_swap

/-! ## 13. The quartic `A_poly` -/

/-- `A_poly r` is monic. -/
lemma A_poly_monic (r : ℕ) : (A_poly r).Monic := by
  rw [A_poly]
  exact monic_X.mul (monic_X_sub_C (r : ℤ)) |>.mul (monic_X_add_C ((r : ℤ) + 1)) |>.mul
    (monic_X_add_C (2 * (r : ℤ) + 1))

/-- The reduction of `A_poly r` modulo `p` is the quartic with roots
`0, r, r+1, 2r+1` (negated plus-product form). -/
lemma A_poly_mod_eq (p r : ℕ) :
    A_poly_mod p r =
      Polynomial.X * (Polynomial.X - Polynomial.C (r : ZMod p)) *
        (Polynomial.X + Polynomial.C ((r : ZMod p) + 1)) *
        (Polynomial.X + Polynomial.C (2 * (r : ZMod p) + 1)) := by
  rw [A_poly_mod, A_poly]
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul]
  rw [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_add]
  simp only [Polynomial.map_X, Polynomial.map_C]
  norm_num [Nat.cast_add, Nat.cast_mul]

end

end Erdos291
