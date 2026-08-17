import Erdos291.MidAttackLine2
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Separable

/-!
# Erdős #291 — Attack Line 4: (C) `res(F,G) ≠ 0` reduces to CR-free + no-extension-root

This file proves the reduction theorem for the quotient resultant conjecture
`HA_mid_resultant_F_G_ne_zero`:

`res(F,G) ≠ 0` follows from the three hypotheses
1. `H_{2r} ≠ 0` (`HA_mid_harmonicSum_two_mul_r_ne_zero`);
2. no F_p-valued common root (`HA_mid_CR_free`);
3. no extension common root of `Q_r` and `S'`
   (`HA_mid_no_extension_common_root_Qr_midTailDerivative`).

The proof is purely algebraic and uses Mathlib's `isCoprime_iff_aeval_ne_zero`
to reduce coprimality over `ZMod p` to the absence of a common root in every
integral domain extension.  The two cases `a^(p-1)=1` and `a^(p-1)≠1` are
handled as follows.

* For `a^(p-1)=1` the product identity `P_r * S * R = X^(p-1)-1` forces
  `R(a)=0` (the alternative `S(a)=0` contradicts `gcd(S,S')=1`, which is
  Rolle/separability).  Thus `a` is one of `1, …, 2r`; the existing
  `Fp_common_root_iff_CR` then turns it into a forbidden CR solution.

* For `a^(p-1)≠1` the remaining hypothesis `HA_mid_no_extension_common_root_Qr_midTailDerivative`
  applies verbatim.

The extension-free hypothesis is the precise unproved residue of Attack
Line 2 / Route I.  Its intended proof is the total-log-derivative identity
in the algebraic closure:
`∑_{i=1}^{p-1} 1/(α+i) = -α^(p-2)/(α^(p-1)-1)` together with
`Q_r(α)=0` and `S'(α)=0`.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## The remaining extension-free hypothesis -/

/-- **Extension-free hypothesis for Attack Line 2.**  For every intrinsic middle pair
`(p,r)`, the polynomials `Q p r` and `midTailDerivative p r` have no common root `a`
in any integral domain algebra over `ZMod p` with `a ≠ 0` and `a^(p-1) ≠ 1`.

Equivalently (over an algebraic closure of `ZMod p`): there is no common root of
`Q_r` and `S'` outside `F_p^*`.  This is exactly the extension case of Route I. -/
def HA_mid_no_extension_common_root_Qr_midTailDerivative : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] (a : A),
      a ≠ 0 → a ^ (p - 1) ≠ 1 →
        Polynomial.aeval a (Q p r) = 0 →
        Polynomial.aeval a (midTailDerivative p r) = 0 → False

/-! ## Global factor lemmas -/

/-- `Q p r` is `X` times its quotient by `X` for a middle pair. -/
lemma X_mul_QrFactor_eq_Q (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.X : Polynomial (ZMod p)) * QrFactor p r = Q p r := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  have hroot0 : (Q p r).IsRoot 0 := by
    rw [Polynomial.IsRoot, eval_zero_Q_eq_factorial_mul_harmonic p r hrlt,
      harmonicSum_middle_pair_zero p r hrE hrlt, mul_zero]
  have h := (mul_divByMonic_eq_iff_isRoot (p := Q p r) (a := (0 : ZMod p))).2 hroot0
  simpa [QrFactor] using h

/-- `Q p e` is `X - C r` times its quotient by `X - C r` for a middle pair. -/
lemma X_sub_C_mul_QeFactor_eq_Q (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.X - Polynomial.C (r : ZMod p)) * QeFactor p r =
      Q p (p - 1 - 2 * r) := by
  have hrootr : (Q p (p - 1 - 2 * r)).IsRoot (r : ZMod p) := by
    rw [Polynomial.IsRoot]
    exact eval_Q_p_e_eq_zero_of_middle_pair p r hrE (by omega : 2 * r + 1 < p)
  have h := (mul_divByMonic_eq_iff_isRoot
    (p := Q p (p - 1 - 2 * r)) (a := (r : ZMod p))).2 hrootr
  simpa [QeFactor] using h

/-! ## Separability of the middle tail product -/

/-- The middle tail product `S` is separable: its roots are distinct mod `p`
because all indices are `< p`. -/
lemma midTailProduct_separable (p r e : ℕ) [Fact p.Prime] (he_lt : e < p) :
    (midTailProduct p r e).Separable := by
  classical
  have hp : Nat.Prime p := Fact.out
  rw [midTailProduct]
  refine separable_prod' (ι := ℕ)
    (f := fun i : ℕ => Polynomial.X + Polynomial.C (i : ZMod p))
    (s := Finset.Icc (r + 1) e) ?_ ?_
  · intro i hi j hj hij
    have hi' : r + 1 ≤ i ∧ i ≤ e := Finset.mem_Icc.mp hi
    have hj' : r + 1 ≤ j ∧ j ≤ e := Finset.mem_Icc.mp hj
    have hi_lt : i < p := lt_of_le_of_lt hi'.2 he_lt
    have hj_lt : j < p := lt_of_le_of_lt hj'.2 he_lt
    have hcij : (i : ZMod p) ≠ (j : ZMod p) := by
      intro hz
      have hmod : i % p = j % p := (ZMod.natCast_eq_natCast_iff' i j p).mp hz
      have heq : i = j := by
        rwa [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] at hmod
      exact hij heq
    have hneg : (-(i : ZMod p)) ≠ (-(j : ZMod p)) := by
      intro hneg
      exact hcij (neg_inj.mp hneg)
    have hfi : Polynomial.X + Polynomial.C (i : ZMod p) =
        Polynomial.X - Polynomial.C (-(i : ZMod p)) := by
      rw [Polynomial.C_neg, sub_eq_add_neg, neg_neg]
    have hfj : Polynomial.X + Polynomial.C (j : ZMod p) =
        Polynomial.X - Polynomial.C (-(j : ZMod p)) := by
      rw [Polynomial.C_neg, sub_eq_add_neg, neg_neg]
    rw [hfi, hfj]
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hneg).isUnit
  · intro i hi
    exact separable_X_add_C (i : ZMod p)

/-- `S` and `S'` are coprime: the tail product is separable. -/
lemma isCoprime_midTailProduct_midTailDerivative (p r : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) :
    IsCoprime (midTailProduct p r (p - 1 - 2 * r)) (midTailDerivative p r) := by
  have he_lt : p - 1 - 2 * r < p := by omega
  have hsep := midTailProduct_separable p r (p - 1 - 2 * r) he_lt
  simpa [midTailDerivative, Separable] using hsep

/-- `P p r` and `Q p r` are coprime in the intrinsic regime. -/
lemma isCoprime_Pr_Qr (p r : ℕ) [Fact p.Prime] (hmid : 4 * r + 1 < p) :
    IsCoprime (P p r) (Q p r) := by
  have hsep : (P p r).Separable := P_separable p r (by omega : r < p)
  simpa [Q, Separable] using hsep

/-! ## Root membership for interval products in a domain extension -/

/-- In a domain algebra over `ZMod p`, a root of `intervalProduct p a b` is one of
the cast elements `a, …, b`. -/
lemma aeval_intervalProduct_eq_zero_iff_exists
    (p a b : ℕ) (A : Type*) [CommRing A] [IsDomain A] [Algebra (ZMod p) A]
    (x : A) :
    Polynomial.aeval x (intervalProduct p a b) = 0 ↔
      ∃ j ∈ Finset.Icc a b, x = algebraMap (ZMod p) A (j : ZMod p) := by
  classical
  rw [intervalProduct]
  rw [Polynomial.aeval_def, eval₂_finsetProd]
  constructor
  · intro h
    rw [Finset.prod_eq_zero_iff] at h
    rcases h with ⟨j, hj, hj0⟩
    refine ⟨j, hj, ?_⟩
    have : x - algebraMap (ZMod p) A (j : ZMod p) = 0 := by
      simpa [Polynomial.aeval_def, eval₂_add, eval₂_X, eval₂_C] using hj0
    exact sub_eq_zero.mp this
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.prod_eq_zero_iff]
    refine ⟨j, hj, ?_⟩
    simp

/-! ## The reduction theorem -/

/-- The main reduction: if `H_{2r} ≠ 0`, there is no CR solution, and there is no
extension common root of `Q_r` and `S'`, then `F` and `G` are coprime. -/
theorem isCoprime_QrFactor_QeFactor_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hB : harmonicSum p (2 * r) ≠ 0)
    (hCR : HA_mid_CR_free)
    (hNoExt : HA_mid_no_extension_common_root_Qr_midTailDerivative) :
    IsCoprime (QrFactor p r) (QeFactor p r) := by
  have hp : Nat.Prime p := Fact.out
  let e : ℕ := p - 1 - 2 * r
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have he_ge : 1 ≤ e := by dsimp [e]; omega
  have he_lt : e < p := by dsimp [e]; omega
  have h2r_lt : 2 * r < p := by omega
  have hre : r ≤ e := by dsimp [e]; omega
  -- The two factorizations of `Q_r` and `Q_e`.
  have hQr_mul : (Polynomial.X : Polynomial (ZMod p)) * QrFactor p r = Q p r :=
    X_mul_QrFactor_eq_Q p r hrE hmid
  have hQe_mul : (Polynomial.X - Polynomial.C (r : ZMod p)) * QeFactor p r = Q p e := by
    dsimp [e]
    exact X_sub_C_mul_QeFactor_eq_Q p r hrE hmid
  -- Coprime partners.
  have hPr_Qr_cop : IsCoprime (P p r) (Q p r) := isCoprime_Pr_Qr p r hmid
  have hSS_cop : IsCoprime (midTailProduct p r e) (midTailDerivative p r) := by
    dsimp [e]
    exact isCoprime_midTailProduct_midTailDerivative p r hmid
  -- Polynomial identity `P_r * S * R = X^(p-1) - 1`.
  have hprod_poly : P p r * midTailProduct p r e * intervalProduct p 1 (2 * r) =
      (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
    calc
      P p r * midTailProduct p r e * intervalProduct p 1 (2 * r)
          = P p e * intervalProduct p 1 (2 * r) := by
              rw [P_e_eq_P_r_mul_midTailProduct p r e hre]
      _ = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
              dsimp [e]
              exact P_e_mul_R_eq_X_pow_pred_sub_one p r h2r_lt
  -- Use the aeval criterion for coprimality.
  rw [isCoprime_iff_aeval_ne_zero]
  intro A _ _ _ a
  by_contra hnot
  rw [not_or] at hnot
  rcases hnot with ⟨haF_ne, haG_ne⟩
  have haF : Polynomial.aeval a (QrFactor p r) = 0 := by
    by_contra h
    exact haF_ne h
  have haG : Polynomial.aeval a (QeFactor p r) = 0 := by
    by_contra h
    exact haG_ne h
  -- Step 1: `a` is a common root of `Q_r` and `Q_e`.
  have haQr : Polynomial.aeval a (Q p r) = 0 := by
    have hm := congrArg (Polynomial.aeval a) hQr_mul
    rw [Polynomial.aeval_mul, Polynomial.aeval_X, haF, mul_zero] at hm
    exact hm.symm
  have haQe : Polynomial.aeval a (Q p e) = 0 := by
    have hm := congrArg (Polynomial.aeval a) hQe_mul
    rw [Polynomial.aeval_mul, Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, haG, mul_zero] at hm
    exact hm.symm
  -- Step 2: `a ≠ 0`, because `a = 0` would force `H_{2r} = 0`.
  have ha_ne_zero : a ≠ 0 := by
    intro ha0
    have hQe0_aeval : Polynomial.aeval (0 : A) (Q p e) = 0 := by
      simpa [ha0] using haQe
    have hQe0_aeval' : Polynomial.aeval (algebraMap (ZMod p) A (0 : ZMod p)) (Q p e) = 0 := by
      simpa using hQe0_aeval
    have hQe0_eval_map : algebraMap (ZMod p) A (Polynomial.eval (0 : ZMod p) (Q p e)) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (0 : ZMod p) (Q p e)]
      exact hQe0_aeval'
    have hQe0_eval : Polynomial.eval (0 : ZMod p) (Q p e) = 0 := by
      apply (algebraMap (ZMod p) A).injective
      simpa using hQe0_eval_map
    have hH2r : harmonicSum p (2 * r) = 0 := by
      have hiff := eval_zero_Q_p_e_eq_zero_iff_harmonicSum_two_mul_r_eq_zero p r hrE
        (by omega : 2 * r + 1 < p)
      exact hiff.mp (by simpa [e] using hQe0_eval)
    exact hB hH2r
  -- Step 3: `P_r(a) ≠ 0`, hence `S'(a) = 0`.
  have haPr_ne_zero : Polynomial.aeval a (P p r) ≠ 0 := by
    intro haPr0
    have hnot := aeval_ne_zero_of_isCoprime hPr_Qr_cop a
    exact hnot.elim (fun h => h haPr0) (fun h => h haQr)
  have haSd : Polynomial.aeval a (midTailDerivative p r) = 0 := by
    have hdecomp := Q_e_eq_Q_r_mul_midTailProduct_add_P_r_mul_derivative p r e hre
    have hm := congrArg (Polynomial.aeval a) hdecomp
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_mul] at hm
    have hm' : Polynomial.aeval a (Q p e) =
        Polynomial.aeval a (Q p r) * Polynomial.aeval a (midTailProduct p r e) +
          Polynomial.aeval a (P p r) * Polynomial.aeval a (Polynomial.derivative (midTailProduct p r e)) := hm
    rw [haQe, haQr, zero_mul, zero_add] at hm'
    have hprod : Polynomial.aeval a (P p r) *
        Polynomial.aeval a (Polynomial.derivative (midTailProduct p r e)) = 0 := by
      simpa [haQe, haQr] using hm'.symm
    have hdvd : Polynomial.aeval a (Polynomial.derivative (midTailProduct p r e)) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left haPr_ne_zero
    simpa [midTailDerivative] using hdvd
  -- Step 4: split according to `a^(p-1)`.
  by_cases ha_pow : a ^ (p - 1) = 1
  · -- First case: `a` is in `F_p`; more precisely, the product identity forces
    -- `R(a) = 0`, and the CR-free hypothesis gives the contradiction.
    have hprod_eval : Polynomial.aeval a (P p r * midTailProduct p r e * intervalProduct p 1 (2 * r)) =
        a ^ (p - 1) - 1 := by
      rw [hprod_poly]
      simp [Polynomial.aeval_X]
    have hprod0 : Polynomial.aeval a (P p r) * Polynomial.aeval a (midTailProduct p r e) *
        Polynomial.aeval a (intervalProduct p 1 (2 * r)) = 0 := by
      simpa [Polynomial.aeval_mul, ha_pow] using hprod_eval
    have hS_ne_zero : Polynomial.aeval a (midTailProduct p r e) ≠ 0 := by
      intro hS0
      have hnot := aeval_ne_zero_of_isCoprime hSS_cop a
      exact hnot.elim (fun h => h hS0) (fun h => h (by simpa [midTailDerivative] using haSd))
    have hR0 : Polynomial.aeval a (intervalProduct p 1 (2 * r)) = 0 := by
      have hpr := mul_eq_zero.mp hprod0
      rcases hpr with hPS0 | hR0
      · have hPS := mul_eq_zero.mp hPS0
        rcases hPS with hP0 | hS0
        · exact (haPr_ne_zero hP0).elim
        · exact (hS_ne_zero hS0).elim
      · exact hR0
    have hrootR := (aeval_intervalProduct_eq_zero_iff_exists p 1 (2 * r) A a).mp hR0
    rcases hrootR with ⟨β, hβIcc, hβeq⟩
    have hβ1 : 1 ≤ β := (Finset.mem_Icc.mp hβIcc).1
    have hβ2 : β ≤ 2 * r := (Finset.mem_Icc.mp hβIcc).2
    -- `β ≠ r`: otherwise `a = r` and `Q_r(r) = 0` would force `H_{2r} = 0`.
    have hβ_ne_r : β ≠ r := by
      intro hβr
      subst β
      have ha_r : a = algebraMap (ZMod p) A (r : ZMod p) := hβeq
      have hQr_eval_map : algebraMap (ZMod p) A (Polynomial.eval (r : ZMod p) (Q p r)) = 0 := by
        rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (r : ZMod p) (Q p r)]
        rw [← ha_r]
        exact haQr
      have hQr_eval_r : Polynomial.eval (r : ZMod p) (Q p r) = 0 := by
        apply (algebraMap (ZMod p) A).injective
        simpa using hQr_eval_map
      have hQr_r_harm := eval_Q_p_r_eq_ascFactorial_mul_harmonicSum_two_mul_of_mem_E p r hrE
        (by omega : 2 * r + 1 < p)
      have hasc_ne : ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) ≠ 0 := by
        have hprod : ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) =
            ∏ i ∈ Finset.range r, (((r + 1 + i : ℕ) : ZMod p)) := by
          rw [Nat.ascFactorial_eq_prod_range]
          simp
        rw [hprod]
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        have hi' : i < r := Finset.mem_range.mp hi
        have hge : 1 ≤ r + 1 + i := by omega
        have hle : r + 1 + i ≤ 2 * r := by omega
        have hlt : r + 1 + i < p := by omega
        intro hz
        have hpdvd : p ∣ r + 1 + i := (ZMod.natCast_eq_zero_iff (r + 1 + i) p).mp hz
        exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
      have hH2r : harmonicSum p (2 * r) = 0 := by
        rw [hQr_r_harm] at hQr_eval_r
        exact (mul_eq_zero.mp hQr_eval_r).resolve_left hasc_ne
      exact hB hH2r
    -- Transfer the `F` and `G` roots back to `ZMod p` and apply `Fp_common_root_iff_CR`.
    have hF_eval : Polynomial.eval (β : ZMod p) (QrFactor p r) = 0 := by
      have hm : algebraMap (ZMod p) A (Polynomial.eval (β : ZMod p) (QrFactor p r)) = 0 := by
        rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (β : ZMod p) (QrFactor p r)]
        rw [← hβeq]
        exact haF
      apply (algebraMap (ZMod p) A).injective
      simpa using hm
    have hG_eval : Polynomial.eval (β : ZMod p) (QeFactor p r) = 0 := by
      have hm : algebraMap (ZMod p) A (Polynomial.eval (β : ZMod p) (QeFactor p r)) = 0 := by
        rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (β : ZMod p) (QeFactor p r)]
        rw [← hβeq]
        exact haG
      apply (algebraMap (ZMod p) A).injective
      simpa using hm
    have hCR_sol := (Fp_common_root_iff_CR p r β hrE hmid hβ1 hβ2 hβ_ne_r).mp ⟨hF_eval, hG_eval⟩
    exact hCR p r hp hmid hrE β hβ1 hβ2 hβ_ne_r hCR_sol.1 hCR_sol.2
  · -- Second case: extension root; the explicit hypothesis applies.
    exact hNoExt p r hp hmid hrE A a ha_ne_zero ha_pow haQr haSd

/-- The quotient-resultant conjecture follows from `H_{2r} ≠ 0`, CR-freeness and the
extension-free hypothesis. -/
theorem HA_mid_resultant_F_G_ne_zero_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
    (hB : HA_mid_harmonicSum_two_mul_r_ne_zero)
    (hCR : HA_mid_CR_free)
    (hNoExt : HA_mid_no_extension_common_root_Qr_midTailDerivative) :
    HA_mid_resultant_F_G_ne_zero := by
  intro p r hp hmid hrE
  haveI : Fact p.Prime := ⟨hp⟩
  have hB' : harmonicSum p (2 * r) ≠ 0 := hB p r hp hmid hrE
  have hcop : IsCoprime (QrFactor p r) (QeFactor p r) :=
    isCoprime_QrFactor_QeFactor_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
      p r hrE hmid hB' hCR hNoExt
  intro hres0
  have hF_ne : QrFactor p r ≠ 0 := QrFactor_ne_zero_of_middle_pair p r hrE hmid
  have hnot := (Polynomial.resultant_eq_zero_iff (f := QrFactor p r)
    (g := QeFactor p r)).mp hres0
  exact hnot.2 hcop

/-- The extension-free hypothesis together with `H_{2r} ≠ 0` and CR-freeness implies
the full Attack-Line-2 statement `res(Q_r, S') ≠ 0`. -/
theorem HA_mid_resultant_Qr_midTailDerivative_ne_zero_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
    (hB : HA_mid_harmonicSum_two_mul_r_ne_zero)
    (hCR : HA_mid_CR_free)
    (hNoExt : HA_mid_no_extension_common_root_Qr_midTailDerivative) :
    HA_mid_resultant_Qr_midTailDerivative_ne_zero := by
  have hFG : HA_mid_resultant_F_G_ne_zero :=
    HA_mid_resultant_F_G_ne_zero_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
      hB hCR hNoExt
  intro p r hp hmid hrE
  haveI : Fact p.Prime := ⟨hp⟩
  exact (resultant_Qr_midTailDerivative_ne_zero_iff p r hrE hmid).mpr
    ⟨hB p r hp hmid hrE, hFG p r hp hmid hrE⟩

end

end Erdos291
