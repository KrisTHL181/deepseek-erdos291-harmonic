import Erdos291.MidConjectures

/-!
# Erdős #291 — Attack Line 2: reducing everything to `gcd(Q_r, S') = 1`

The derivative of the mid tail product is

    `S' = derivative (midTailProduct p r (p - 1 - 2r))`.

The existing `MidRoots.lean` already contains the two polynomial identities
that drive this attack line:

* `Q p e = Q p r * S + P p r * S'`  (so `S' ≡ P_r⁻¹ * Q_e (mod Q_r)`);
* `resultant (Q p r) (Q p e) = resultant (Q p r) (P p r) * resultant (Q p r) S'`
  with `resultant (Q p r) (P p r) ≠ 0`.

Together with the exact factorization in `MidResultant.lean` this gives a clean
equivalence: `res(Q_r, S') ≠ 0 ↔ H_{2r} ≠ 0 ∧ res(F, G) ≠ 0`.  In particular
the single statement `res(Q_r, S') ≠ 0` (equivalently `gcd(Q_r, S') = 1`) is
the strongest of the three frontier hypotheses: it implies (A), (B), and (C).

This file proves that reduction and records the remaining unproved statement
`HA_mid_resultant_Qr_midTailDerivative_ne_zero`.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The derivative `S'` of the middle tail product. -/
noncomputable def midTailDerivative (p r : ℕ) : Polynomial (ZMod p) :=
  Polynomial.derivative (midTailProduct p r (p - 1 - 2 * r))

/-- The basic reduction for `S'` modulo `Q_r`:
`P_r * S' = Q_e - S * Q_r`, hence over the quotient by `Q_r` one has
`S' = P_r⁻¹ * Q_e`. -/
lemma midTailDerivative_mul_P_eq_Qe_sub_midTail_mul_Qr (p r : ℕ)
    (hr_le : r ≤ p - 1 - 2 * r) :
    midTailDerivative p r * P p r =
      Q p (p - 1 - 2 * r) - midTailProduct p r (p - 1 - 2 * r) * Q p r := by
  have h := Q_e_eq_Q_r_mul_midTailProduct_add_P_r_mul_derivative p r (p - 1 - 2 * r) hr_le
  dsimp [midTailDerivative]
  calc
    Polynomial.derivative (midTailProduct p r (p - 1 - 2 * r)) * P p r
        = P p r * Polynomial.derivative (midTailProduct p r (p - 1 - 2 * r)) := by ring
    _ = Q p (p - 1 - 2 * r) - midTailProduct p r (p - 1 - 2 * r) * Q p r := by
          rw [h]
          ring

/-- The resultant `res(Q_r, S')` vanishes iff the middle resultant vanishes.  This is
the immediate consequence of `res(Q_r, Q_e) = res(Q_r, P_r) * res(Q_r, S')` and
`res(Q_r, P_r) ≠ 0` already proved in `MidRoots.lean`. -/
lemma resultant_Qr_midTailDerivative_eq_zero_iff_resultant_Qr_Qe_eq_zero
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) = 0 ↔
      (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) = 0 := by
  have h := resultant_Qr_Qe_eq_zero_iff_resultant_Qr_derivative_midTail_eq_zero p r hrE hmid
  simpa [midTailDerivative] using h.symm

/-- The main equivalence of Attack Line 2:
`res(Q_r, S') = 0 ↔ H_{2r} = 0 ∨ res(F, G) = 0`.
Equivalently, `res(Q_r, S') ≠ 0 ↔ H_{2r} ≠ 0 ∧ res(F, G) ≠ 0`. -/
lemma resultant_Qr_midTailDerivative_eq_zero_iff
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) = 0 ↔
      harmonicSum p (2 * r) = 0 ∨
        Polynomial.resultant (QrFactor p r) (QeFactor p r) = 0 := by
  have h1 := resultant_Qr_midTailDerivative_eq_zero_iff_resultant_Qr_Qe_eq_zero p r hrE hmid
  have h2 := resultant_Qr_Qe_eq_zero_iff p r hrE (by omega : 2 * r + 1 < p)
  exact h1.trans h2

/-- The nonzero form of the main equivalence. -/
lemma resultant_Qr_midTailDerivative_ne_zero_iff
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) ≠ 0 ↔
      harmonicSum p (2 * r) ≠ 0 ∧
        Polynomial.resultant (QrFactor p r) (QeFactor p r) ≠ 0 := by
  constructor
  · intro h
    have hnot : ¬ ((Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) = 0) := by
      simpa using h
    have hzero : ¬ (harmonicSum p (2 * r) = 0 ∨
        (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) = 0) := by
      rw [← resultant_Qr_midTailDerivative_eq_zero_iff p r hrE hmid]
      exact hnot
    exact ⟨fun hH => hzero (Or.inl hH), fun hR => hzero (Or.inr hR)⟩
  · intro h
    have hzero : ¬ (harmonicSum p (2 * r) = 0 ∨
        (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) = 0) := by
      intro hz
      rcases hz with hz | hz
      · exact h.1 hz
      · exact h.2 hz
    have hnot : ¬ ((Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) = 0) := by
      rw [resultant_Qr_midTailDerivative_eq_zero_iff p r hrE hmid]
      exact hzero
    simpa using hnot

/-- The derivative `S'` of the middle tail product is nonzero in the intrinsic regime:
its leading coefficient is `e - r = p - 1 - 3r`, which is positive and `< p`. -/
lemma midTailDerivative_ne_zero_of_middle_pair (p r : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) : midTailDerivative p r ≠ 0 := by
  let e : ℕ := p - 1 - 2 * r
  have hre : r ≤ e := by dsimp [e]; omega
  have hd_pos : 0 < e - r := by dsimp [e]; omega
  have hd_lt : e - r < p := by dsimp [e]; omega
  have hSdeg : (midTailProduct p r e).natDegree = e - r := by
    dsimp [midTailProduct]
    rw [plusProduct_natDegree p (r + 1) e]
    omega
  have hSm : (midTailProduct p r e).Monic := midTailProduct_monic p r e
  have hcoeffS : coeff (midTailProduct p r e) (e - r) = 1 := by
    rw [← hSdeg, Polynomial.coeff_natDegree]
    exact hSm.leadingCoeff
  have hd_ne : ((e - r : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hpdvd : p ∣ e - r := (ZMod.natCast_eq_zero_iff (e - r) p).mp hz
    exact (not_lt_of_ge (Nat.le_of_dvd (Nat.succ_le_of_lt hd_pos) hpdvd)) hd_lt
  intro h
  have hcoeff0 : coeff (midTailDerivative p r) (e - r - 1) = 0 := by
    rw [h, Polynomial.coeff_zero]
  have hcoeffd : coeff (midTailDerivative p r) (e - r - 1) = (e - r : ZMod p) := by
    dsimp [midTailDerivative]
    change coeff (Polynomial.derivative (midTailProduct p r e)) (e - r - 1) = (e - r : ZMod p)
    have hd_succ : e - r - 1 + 1 = e - r := by omega
    calc
      coeff (Polynomial.derivative (midTailProduct p r e)) (e - r - 1)
          = coeff (midTailProduct p r e) (e - r - 1 + 1) * ((e - r - 1 + 1 : ℕ) : ZMod p) := by
              rw [Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
      _ = coeff (midTailProduct p r e) (e - r) * ((e - r : ℕ) : ZMod p) := by rw [hd_succ]
      _ = 1 * ((e - r : ℕ) : ZMod p) := by rw [hcoeffS]
      _ = (e - r : ZMod p) := by
          simp [Nat.cast_sub hre]
  have hcoeff0' : ((e - r : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hre]
    exact hcoeffd.symm.trans hcoeff0
  exact hd_ne hcoeff0'

/-- For intrinsic middle pairs, `gcd(Q_r, S') = 1` is equivalent to
`res(Q_r, S') ≠ 0`. -/
lemma isCoprime_Qr_midTailDerivative_iff_resultant_ne_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    IsCoprime (Q p r) (midTailDerivative p r) ↔
      (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) ≠ 0 := by
  have hQr_ne : Q p r ≠ 0 := Q_ne_zero p r (mem_E_ge_one p r hrE) (by omega : r < p)
  have hS'_ne : midTailDerivative p r ≠ 0 := midTailDerivative_ne_zero_of_middle_pair p r hmid
  constructor
  · intro hcop hres0
    have hzero := (Polynomial.resultant_eq_zero_iff (f := Q p r)
      (g := midTailDerivative p r)).1 hres0
    exact hzero.2 hcop
  · intro hres
    by_contra hncop
    have hres0 : (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      exact ⟨Or.inl hQr_ne, hncop⟩
    exact hres hres0

/-- The quotient `QrFactor p r` is nonzero for an intrinsic middle pair. -/
lemma QrFactor_ne_zero_of_middle_pair (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) : QrFactor p r ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have hQr_ne : Q p r ≠ 0 := Q_ne_zero p r h1r hr_lt
  have hroot0 : (Q p r).IsRoot 0 := by
    rw [Polynomial.IsRoot, eval_zero_Q_eq_factorial_mul_harmonic p r hr_lt,
      harmonicSum_middle_pair_zero p r hrE hr_lt, mul_zero]
  have hmulX : (Polynomial.X : Polynomial (ZMod p)) * QrFactor p r = Q p r := by
    have h := (mul_divByMonic_eq_iff_isRoot (p := Q p r) (a := (0 : ZMod p))).2 hroot0
    simpa [QrFactor] using h
  intro hF0
  have hm := hmulX
  rw [hF0, mul_zero] at hm
  exact hQr_ne hm.symm

/-- The quotient `QeFactor p r` is nonzero for an intrinsic middle pair. -/
lemma QeFactor_ne_zero_of_middle_pair (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) : QeFactor p r ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have he_ge : 1 ≤ p - 1 - 2 * r := by omega
  have he_lt : p - 1 - 2 * r < p := by omega
  have hQe_ne : Q p (p - 1 - 2 * r) ≠ 0 := Q_ne_zero p (p - 1 - 2 * r) he_ge he_lt
  have hrootR : (Q p (p - 1 - 2 * r)).IsRoot (r : ZMod p) := by
    rw [Polynomial.IsRoot]
    exact eval_Q_p_e_eq_zero_of_middle_pair p r hrE (by omega : 2 * r + 1 < p)
  have hmulE : (Polynomial.X - Polynomial.C (r : ZMod p)) * QeFactor p r =
      Q p (p - 1 - 2 * r) := by
    have h := (mul_divByMonic_eq_iff_isRoot (p := Q p (p - 1 - 2 * r))
      (a := (r : ZMod p))).2 hrootR
    simpa [QeFactor] using h
  intro hG0
  have hm := hmulE
  rw [hG0, mul_zero] at hm
  exact hQe_ne hm.symm

/-- If `res(F,G) ≠ 0` then `F` and `G` are coprime. -/
lemma isCoprime_QrFactor_QeFactor_of_resultant_ne_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hFG : (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0) :
    IsCoprime (QrFactor p r) (QeFactor p r) := by
  have hF_ne : QrFactor p r ≠ 0 := QrFactor_ne_zero_of_middle_pair p r hrE hmid
  have hG_ne : QeFactor p r ≠ 0 := QeFactor_ne_zero_of_middle_pair p r hrE hmid
  by_contra hncop
  have hres0 : (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) = 0 := by
    rw [Polynomial.resultant_eq_zero_iff]
    exact ⟨Or.inl hF_ne, hncop⟩
  exact hFG hres0

/-- The target statement `res(Q_r, S') ≠ 0` excludes the common-root configuration [CR]:
no `β ∈ [1, 2r] \ {r}` satisfies `H_β = H_{β+r} = H_{2r-β}`. -/
theorem no_CR_of_resultant_Qr_midTailDerivative_ne_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hres : (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) ≠ 0) :
    ∀ β : ℕ, 1 ≤ β → β ≤ 2 * r → β ≠ r →
      ¬ (harmonicSum p β = harmonicSum p (β + r) ∧
        harmonicSum p β = harmonicSum p (2 * r - β)) := by
  intro β hβ1 hβ2 hβne hCR
  have hiff := (resultant_Qr_midTailDerivative_ne_zero_iff p r hrE hmid).mp hres
  have hFG_ne : (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0 := hiff.2
  have hcop : IsCoprime (QrFactor p r) (QeFactor p r) :=
    isCoprime_QrFactor_QeFactor_of_resultant_ne_zero p r hrE hmid hFG_ne
  have hroot := (Fp_common_root_iff_CR p r β hrE hmid hβ1 hβ2 hβne).mpr hCR
  have hzero := aeval_ne_zero_of_isCoprime hcop (β : ZMod p)
  have hrootA : (Polynomial.aeval (β : ZMod p) (QrFactor p r) = 0 ∧
      Polynomial.aeval (β : ZMod p) (QeFactor p r) = 0) := by
    rw [show Polynomial.aeval (β : ZMod p) (QrFactor p r) =
        Polynomial.eval (β : ZMod p) (QrFactor p r) by
          rw [aeval_def]
          rfl]
    rw [show Polynomial.aeval (β : ZMod p) (QeFactor p r) =
        Polynomial.eval (β : ZMod p) (QeFactor p r) by
          rw [aeval_def]
          rfl]
    exact hroot
  exact hzero.elim (fun h => h hrootA.1) (fun h => h hrootA.2)

/-- **Reduction theorem.**  The single statement `res(Q_r, S') ≠ 0` implies all three
frontier hypotheses:
1. [CR] has no solution (A);
2. `H_{2r} ≠ 0` (B);
3. `res(F, G) ≠ 0` (C). -/
theorem resultant_Qr_midTailDerivative_ne_zero_implies_frontier (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hres : (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) ≠ 0) :
    (∀ β : ℕ, 1 ≤ β → β ≤ 2 * r → β ≠ r →
      ¬ (harmonicSum p β = harmonicSum p (β + r) ∧
        harmonicSum p β = harmonicSum p (2 * r - β))) ∧
      harmonicSum p (2 * r) ≠ 0 ∧
      (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0 := by
  have hiff := (resultant_Qr_midTailDerivative_ne_zero_iff p r hrE hmid).mp hres
  exact ⟨no_CR_of_resultant_Qr_midTailDerivative_ne_zero p r hrE hmid hres, hiff.1, hiff.2⟩

/-- The remaining unproved statement of Attack Line 2: for every intrinsic middle pair,
`res(Q_r, S') ≠ 0` in `ZMod p` (equivalently `gcd(Q_r, S') = 1`). -/
def HA_mid_resultant_Qr_midTailDerivative_ne_zero : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    (Polynomial.resultant (Q p r) (midTailDerivative p r) : ZMod p) ≠ 0

/-- The single Attack Line 2 statement implies the three frontier conjectures as
Propositions. -/
theorem HA_frontier_of_HA_mid_resultant_Qr_midTailDerivative_ne_zero
    (h : HA_mid_resultant_Qr_midTailDerivative_ne_zero) :
    HA_mid_harmonicSum_two_mul_r_ne_zero ∧ HA_mid_resultant_F_G_ne_zero ∧
      (∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
        ∀ β : ℕ, 1 ≤ β → β ≤ 2 * r → β ≠ r →
          ¬ (harmonicSum p β = harmonicSum p (β + r) ∧
            harmonicSum p β = harmonicSum p (2 * r - β))) := by
  have hH : HA_mid_harmonicSum_two_mul_r_ne_zero := by
    unfold HA_mid_harmonicSum_two_mul_r_ne_zero
    intro p r hp hmid hrE
    haveI : Fact p.Prime := ⟨hp⟩
    exact (resultant_Qr_midTailDerivative_ne_zero_iff p r hrE hmid).mp (h p r hp hmid hrE) |>.1
  have hFG : HA_mid_resultant_F_G_ne_zero := by
    unfold HA_mid_resultant_F_G_ne_zero
    intro p r hp hmid hrE
    haveI : Fact p.Prime := ⟨hp⟩
    exact (resultant_Qr_midTailDerivative_ne_zero_iff p r hrE hmid).mp (h p r hp hmid hrE) |>.2
  have hnoCR : ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
      ∀ β : ℕ, 1 ≤ β → β ≤ 2 * r → β ≠ r →
        ¬ (harmonicSum p β = harmonicSum p (β + r) ∧
          harmonicSum p β = harmonicSum p (2 * r - β)) := by
    intro p r hp hmid hrE
    haveI : Fact p.Prime := ⟨hp⟩
    exact no_CR_of_resultant_Qr_midTailDerivative_ne_zero p r hrE hmid (h p r hp hmid hrE)
  exact ⟨hH, hFG, hnoCR⟩

/-- Attack Line 2 implies the CR-free conjecture `HA_mid_CR_free`. -/
theorem HA_mid_CR_free_of_HA_mid_resultant_Qr_midTailDerivative_ne_zero
    (h : HA_mid_resultant_Qr_midTailDerivative_ne_zero) : HA_mid_CR_free := by
  intro p r hp hmid hrE β hβ1 hβ2 hβne hEq1 hEq2
  exact (HA_frontier_of_HA_mid_resultant_Qr_midTailDerivative_ne_zero h).2.2
    p r hp hmid hrE β hβ1 hβ2 hβne ⟨hEq1, hEq2⟩

/-- Attack Line 2 implies the intrinsic middle resultant conjecture. -/
theorem HA_mid_resultant_Qr_Qe_ne_zero_intrinsic_of_HA_mid_resultant_Qr_midTailDerivative_ne_zero
    (h : HA_mid_resultant_Qr_midTailDerivative_ne_zero) :
    HA_mid_resultant_Qr_Qe_ne_zero_intrinsic := by
  have hf := HA_frontier_of_HA_mid_resultant_Qr_midTailDerivative_ne_zero h
  exact HA_mid_resultant_Qr_Qe_ne_zero_intrinsic_of_resultant_F_G_ne_zero_and_harmonicSum_two_mul_r_ne_zero
    hf.1 hf.2.1

end

end Erdos291
