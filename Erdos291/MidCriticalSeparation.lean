import Erdos291.MidAttackLine2
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Erdős #291 — critical separation: Euclidean remainder and conditional gcd

The user-supplied proof sketch for `gcd(Q_r, Q_e) = 1` rests on the following
*separation lemma*:

> For a middle pair `(r, p)` with `p` prime, `4r+1 < p ≤ r^2` and `r ∈ E p`,
> Euclidean-reduce `Q_e` modulo `Q_r`.  The remainder `R` has degree exactly
> `r-2`, a nonzero constant term, and `gcd(Q_r, R) = 1`.

This file formalizes the Euclidean reduction and proves every step that does
*not* require the missing arithmetic content of that lemma:

1. We normalize `Q_r` to the monic polynomial `QrMonic p r = C r⁻¹ * Q_r` and
   define `midRemainder p r` (the remainder of `Q_e` modulo `QrMonic p r`) and
   `midQuotient p r`.
2. We prove the division identity, the degree bound `deg R < r-1`, and the
   equality `R(0) = Q_e(0)` (hence `R(0) ≠ 0 ↔ H_{2r} ≠ 0`).
3. We prove `gcd(Q_r, Q_e) = gcd(Q_r, R)` in the sense of `IsCoprime`.
4. We prove the unconditional equivalence
   `IsCoprime (Q_r) (Q_e) ↔ H_{2r} ≠ 0 ∧ IsCoprime (QrFactor) (QeFactor)`.
5. We record the remaining separation lemma as the documented definition
   `HA_mid_remainder_coprime_Qr` and derive from it the full middle-pair
   corollaries (gcd=1, resultant ≠ 0, `H_{2r} ≠ 0`, `res(F,G) ≠ 0`).

The two ingredients `HA_mid_harmonicSum_two_mul_r_ne_zero` and
`HA_mid_resultant_F_G_ne_zero` are already recorded in `MidConjectures.lean`.
Numeric evidence for them (0 counterexamples in the scanned ranges) is stated
there.  This file intentionally contains no unfinished proof placeholders.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Monic normalization and Euclidean remainder -/

/-- The monic normalization of `Q p r`: multiply by `(r : ZMod p)⁻¹`.
This is monic of degree `r-1` when `1 ≤ r < p`. -/
noncomputable def QrMonic (p r : ℕ) : Polynomial (ZMod p) :=
  Polynomial.C ((r : ZMod p)⁻¹) * Q p r

/-- The Euclidean quotient of `Q p (p-1-2r)` by the monic normalization of `Q p r`. -/
noncomputable def midQuotient (p r : ℕ) : Polynomial (ZMod p) :=
  Q p (p - 1 - 2 * r) /ₘ QrMonic p r

/-- The Euclidean remainder of `Q p (p-1-2r)` modulo the monic normalization of
`Q p r`.  This is the `R` of the user's sketch. -/
noncomputable def midRemainder (p r : ℕ) : Polynomial (ZMod p) :=
  Q p (p - 1 - 2 * r) %ₘ QrMonic p r

/-- `(r : ZMod p) ≠ 0` when `1 ≤ r < p` and `p` is prime. -/
lemma natCast_r_ne_zero (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrlt : r < p) :
    (r : ZMod p) ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  intro h0
  have hpdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
  exact (not_lt_of_ge (Nat.le_of_dvd h1r hpdvd)) hrlt

/-- `QrMonic p r` is monic of degree `r-1`. -/
lemma QrMonic_monic (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrlt : r < p) :
    (QrMonic p r).Monic := by
  have hr_ne : (r : ZMod p) ≠ 0 := natCast_r_ne_zero p r h1r hrlt
  have hinv_ne : ((r : ZMod p)⁻¹) ≠ 0 := inv_ne_zero hr_ne
  have hdeg : (QrMonic p r).natDegree = r - 1 := by
    rw [QrMonic, Polynomial.natDegree_C_mul hinv_ne]
    exact Q_natDegree p r h1r hrlt
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff, hdeg]
  rw [QrMonic]
  rw [Polynomial.coeff_C_mul]
  rw [Q_coeff_pred' p r h1r]
  exact inv_mul_cancel₀ hr_ne

/-- The degree of `QrMonic p r`. -/
lemma QrMonic_natDegree (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrlt : r < p) :
    (QrMonic p r).natDegree = r - 1 := by
  have hr_ne : (r : ZMod p) ≠ 0 := natCast_r_ne_zero p r h1r hrlt
  have hinv_ne : ((r : ZMod p)⁻¹) ≠ 0 := inv_ne_zero hr_ne
  rw [QrMonic, Polynomial.natDegree_C_mul hinv_ne]
  exact Q_natDegree p r h1r hrlt

/-- `QrMonic p r ≠ 1` as soon as `2 ≤ r`. -/
lemma QrMonic_ne_one (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrlt : r < p)
    (hr2 : 2 ≤ r) : QrMonic p r ≠ 1 := by
  have hdeg : (QrMonic p r).natDegree = r - 1 := QrMonic_natDegree p r h1r hrlt
  intro hq
  have hdeg0 : (QrMonic p r).natDegree = 0 := by simp [hq]
  rw [hdeg] at hdeg0
  omega

/-- The division identity for the normalized monic divisor. -/
lemma midRemainder_spec (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrlt : r < p) :
    midRemainder p r + QrMonic p r * midQuotient p r =
      Q p (p - 1 - 2 * r) := by
  dsimp [midRemainder, midQuotient]
  exact Polynomial.modByMonic_add_div (Q p (p - 1 - 2 * r)) (QrMonic p r)

/-- The remainder has degree `< r - 1`. -/
lemma midRemainder_natDegree_lt (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrlt : r < p)
    (hr2 : 2 ≤ r) :
    (midRemainder p r).natDegree < r - 1 := by
  have hmon : (QrMonic p r).Monic := QrMonic_monic p r h1r hrlt
  have hqdeg : (QrMonic p r).natDegree = r - 1 := QrMonic_natDegree p r h1r hrlt
  have hqne : QrMonic p r ≠ 1 := QrMonic_ne_one p r h1r hrlt hr2
  have h : (midRemainder p r).natDegree < (QrMonic p r).natDegree := by
    simpa [midRemainder] using
      (Polynomial.natDegree_modByMonic_lt (Q p (p - 1 - 2 * r)) hmon hqne)
  rwa [hqdeg] at h

/-- The division identity, expressed with the unnormalized divisor `Q p r`.
This is the identity `Q_e = R + Q_r * (C r⁻¹ * midQuotient)`. -/
lemma Q_e_eq_midRemainder_add_Q_r_mul_scaledQuotient (p r : ℕ) [Fact p.Prime]
    (h1r : 1 ≤ r) (hrlt : r < p) :
    Q p (p - 1 - 2 * r) =
      midRemainder p r + Q p r * (Polynomial.C ((r : ZMod p)⁻¹) * midQuotient p r) := by
  have h := midRemainder_spec p r h1r hrlt
  calc
    Q p (p - 1 - 2 * r) = midRemainder p r + QrMonic p r * midQuotient p r := h.symm
    _ = midRemainder p r + (Polynomial.C ((r : ZMod p)⁻¹) * Q p r) * midQuotient p r := by
          rw [QrMonic]
    _ = midRemainder p r + Q p r * (Polynomial.C ((r : ZMod p)⁻¹) * midQuotient p r) := by
          ring

/-! ## IsCoprime is invariant under the Euclidean step -/

/-- In a commutative ring, `x + y*z` is coprime to `y` iff `x` is. -/
lemma isCoprime_add_mul_right_iff {R : Type*} [CommRing R] (x y z : R) :
    IsCoprime (x + y * z) y ↔ IsCoprime x y := by
  constructor
  · intro h
    exact IsCoprime.of_add_mul_left_left h
  · intro h
    rcases h with ⟨a, b, hab⟩
    refine ⟨a, b - a * z, ?_⟩
    calc
      a * (x + y * z) + (b - a * z) * y = a * x + b * y := by ring
      _ = 1 := hab

/-- `IsCoprime (Q p r) (Q p e)` is equivalent to `IsCoprime (Q p r) (midRemainder p r)`:
the Euclidean step does not change coprimality. -/
lemma isCoprime_Qr_Qe_iff_isCoprime_Qr_midRemainder (p r : ℕ) [Fact p.Prime]
    (h1r : 1 ≤ r) (hrlt : r < p) :
    IsCoprime (Q p r) (Q p (p - 1 - 2 * r)) ↔
      IsCoprime (Q p r) (midRemainder p r) := by
  let z : Polynomial (ZMod p) := Polynomial.C ((r : ZMod p)⁻¹) * midQuotient p r
  have hQe := Q_e_eq_midRemainder_add_Q_r_mul_scaledQuotient p r h1r hrlt
  calc
    IsCoprime (Q p r) (Q p (p - 1 - 2 * r))
        ↔ IsCoprime (Q p r) (midRemainder p r + Q p r * z) := by
          rw [hQe]
    _ ↔ IsCoprime (Q p r) (midRemainder p r) := by
          exact Iff.trans
            (show IsCoprime (Q p r) (midRemainder p r + Q p r * z) ↔
              IsCoprime (midRemainder p r + Q p r * z) (Q p r) from isCoprime_comm)
            (Iff.trans (isCoprime_add_mul_right_iff (midRemainder p r) (Q p r) z)
              (show IsCoprime (midRemainder p r) (Q p r) ↔
                IsCoprime (Q p r) (midRemainder p r) from isCoprime_comm))

/-! ## Constant term of the remainder -/

/-- `R(0) = Q_e(0)` for a middle pair.  Hence the constant term of the remainder
controls `H_{2r}` (through `Q_e(0) = e! H_{2r}`). -/
lemma eval_zero_midRemainder_eq_eval_zero_Q_e (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    Polynomial.eval (0 : ZMod p) (midRemainder p r) =
      Polynomial.eval (0 : ZMod p) (Q p (p - 1 - 2 * r)) := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  have hQe := Q_e_eq_midRemainder_add_Q_r_mul_scaledQuotient p r h1r hrlt
  have heval := congrArg (fun f : Polynomial (ZMod p) => Polynomial.eval (0 : ZMod p) f) hQe
  rw [Polynomial.eval_add, Polynomial.eval_mul] at heval
  have hQr0 : Polynomial.eval (0 : ZMod p) (Q p r) = 0 := by
    rw [eval_zero_Q_eq_factorial_mul_harmonic p r hrlt,
      harmonicSum_middle_pair_zero p r hrE hrlt, mul_zero]
  rw [hQr0, zero_mul, add_zero] at heval
  exact heval.symm

/-- The remainder has nonzero constant term iff `H_{2r} ≠ 0`. -/
lemma eval_zero_midRemainder_ne_zero_iff_harmonicSum_two_mul_r_ne_zero
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    Polynomial.eval (0 : ZMod p) (midRemainder p r) ≠ 0 ↔ harmonicSum p (2 * r) ≠ 0 := by
  rw [eval_zero_midRemainder_eq_eval_zero_Q_e p r hrE hmid]
  have hiff := eval_zero_Q_p_e_eq_zero_iff_harmonicSum_two_mul_r_eq_zero p r hrE
    (by omega : 2 * r + 1 < p)
  simpa using (not_iff_not.mpr hiff)

/-! ## Unconditional equivalence: full gcd splits into `H_{2r}` and `F,G` -/

/-- The nonzero form of `MidResultant.resultant_Qr_Qe_eq_zero_iff`. -/
lemma resultant_Qr_Qe_ne_zero_iff (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p)
    (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) ≠ 0 ↔
      harmonicSum p (2 * r) ≠ 0 ∧
        (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0 := by
  have hzero := resultant_Qr_Qe_eq_zero_iff p r hrE (by omega : 2 * r + 1 < p)
  constructor
  · intro h
    constructor
    · intro hH
      exact h (hzero.mpr (Or.inl hH))
    · intro hFG
      exact h (hzero.mpr (Or.inr hFG))
  · intro h hres
    have hz := hzero.mp hres
    rcases hz with hH | hFG
    · exact h.1 hH
    · exact h.2 hFG

/-- For a middle pair, `gcd(Q_r, Q_e) = 1` is equivalent to the two frontier
conditions `H_{2r} ≠ 0` and `gcd(F,G) = 1`. -/
lemma isCoprime_Qr_Qe_iff (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p)
    (hmid : 4 * r + 1 < p) :
    IsCoprime (Q p r) (Q p (p - 1 - 2 * r)) ↔
      harmonicSum p (2 * r) ≠ 0 ∧ IsCoprime (QrFactor p r) (QeFactor p r) := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  have he_ge : 1 ≤ p - 1 - 2 * r := by omega
  have he_lt : p - 1 - 2 * r < p := by omega
  have hQr_ne : Q p r ≠ 0 := Q_ne_zero p r h1r hrlt
  have hQe_ne : Q p (p - 1 - 2 * r) ≠ 0 := Q_ne_zero p (p - 1 - 2 * r) he_ge he_lt
  have hF_ne : QrFactor p r ≠ 0 := QrFactor_ne_zero_of_middle_pair p r hrE hmid
  constructor
  · intro hcop
    have hres : (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) ≠ 0 := by
      intro hres0
      have hnot := (Polynomial.resultant_eq_zero_iff (f := Q p r)
        (g := Q p (p - 1 - 2 * r))).mp hres0
      exact hnot.2 hcop
    have h := (resultant_Qr_Qe_ne_zero_iff p r hrE hmid).mp hres
    have hFGcop : IsCoprime (QrFactor p r) (QeFactor p r) := by
      by_contra hncop
      have hresFG0 : (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) = 0 := by
        rw [Polynomial.resultant_eq_zero_iff]
        exact ⟨Or.inl hF_ne, hncop⟩
      exact h.2 hresFG0
    exact ⟨h.1, hFGcop⟩
  · intro h
    have hresFG : (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0 := by
      intro h0
      have hnot := (Polynomial.resultant_eq_zero_iff (f := QrFactor p r)
        (g := QeFactor p r)).mp h0
      exact hnot.2 h.2
    have hres := (resultant_Qr_Qe_ne_zero_iff p r hrE hmid).mpr ⟨h.1, hresFG⟩
    by_contra hncop
    have hres0 : (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) = 0 := by
      rw [Polynomial.resultant_eq_zero_iff]
      exact ⟨Or.inl hQr_ne, hncop⟩
    exact hres hres0

/-! ## The explicit remainder shape found by computation

Over `ZMod p`, let `D = intervalProduct p 1 (2*r)` (the product `∏_{j=1}^{2r} (X-j)`).
Whenever `gcd(Q_r, D) = 1` (which holds for all eight task pairs), the Euclidean
remainder has the closed form

    `R = -X^(p-2) * D⁻¹ - (X^(p-1)-1) * D' * D⁻²  (mod Q_r)`,

obtained by solving `Q_e * D² = -X^(p-2) * D - (X^(p-1)-1) * D'`
(`MidRoots.Q_e_mul_R_sq_eq_neg_X_pow_pred_two_mul_R_sub_mul_derivative`) for
`Q_e` modulo `Q_r`.  Pure-Python verification of the eight task pairs confirms
`deg R = r-2`, `R(0) ≠ 0`, and `gcd(Q_r, R) = 1`; the same computation
confirms the displayed formula in those cases.  A proof for all intrinsic pairs
still requires showing the right-hand side has nonzero constant term and is
coprime to `Q_r`, which is exactly the remaining hypothesis below. -/

/-! ## Remaining hypotheses and the conditional middle-pair theorems -/

/-- **Remaining separation lemma (documented hypothesis).**  For every middle pair
`(p, r)` with `p` prime, `4r+1 < p ≤ r^2` and `r ∈ E p`, the Euclidean remainder
`R = midRemainder p r` is coprime to `Q p r`.

The user's sketch asserts this can be proved by a Euclidean reduction whose final
remainder has nonzero constant term and no common root with `Q_r`.  The first
half (nonzero constant term) is equivalent to `H_{2r} ≠ 0` (proved in this file);
the second half (no common root) is equivalent to `res(F,G) ≠ 0`.  Numeric scans
(see `MidConjectures.lean`) give 0 counterexamples for both among all tested
intrinsic MID pairs; for the eight pairs listed in the task
`(61,10),(97,11),(109,25),(137,5),(199,38),(227,22),(227,51),(269,33)` the
remainder `R` has degree exactly `r-2`, nonzero constant term, and
`gcd(Q_r, R) = 1`. -/
def HA_mid_remainder_coprime_Qr : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
    IsCoprime (Q p r) (midRemainder p r)

/-- The constant-term part of the separation lemma, stated separately as in the
task.  It is equivalent to `H_{2r} ≠ 0` (see
`eval_zero_midRemainder_ne_zero_iff_harmonicSum_two_mul_r_ne_zero`). -/
def HA_mid_remainder_constant_nonzero : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
    Polynomial.eval (0 : ZMod p) (midRemainder p r) ≠ 0

/-- The full `gcd(Q_r, Q_e) = 1` theorem, conditional on the separation lemma. -/
theorem isCoprime_Qr_Qe_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    (h : HA_mid_remainder_coprime_Qr) :
    ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
      IsCoprime (Q p r) (Q p (p - 1 - 2 * r)) := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  exact (isCoprime_Qr_Qe_iff_isCoprime_Qr_midRemainder p r h1r hrlt).mpr
    (h p r hp hmid hrE hle)

/-- The full separation lemma implies the constant-term part: `R(0) ≠ 0`. -/
theorem HA_mid_remainder_constant_nonzero_of_HA_mid_remainder_coprime_Qr
    (h : HA_mid_remainder_coprime_Qr) : HA_mid_remainder_constant_nonzero := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop := isCoprime_Qr_Qe_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    h p r hp hmid hrE hle
  have hH := ((isCoprime_Qr_Qe_iff p r hrE hmid).mp hcop).1
  exact (eval_zero_midRemainder_ne_zero_iff_harmonicSum_two_mul_r_ne_zero p r hrE hmid).mpr hH

/-- Conditional corollary: `H_{2r} ≠ 0`. -/
theorem harmonicSum_two_mul_r_ne_zero_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    (h : HA_mid_remainder_coprime_Qr) :
    ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
      harmonicSum p (2 * r) ≠ 0 := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop := isCoprime_Qr_Qe_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    h p r hp hmid hrE hle
  exact ((isCoprime_Qr_Qe_iff p r hrE hmid).mp hcop).1

/-- Conditional corollary: `res(Q_r, Q_e) ≠ 0`. -/
theorem resultant_Qr_Qe_ne_zero_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    (h : HA_mid_remainder_coprime_Qr) :
    ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
      (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) ≠ 0 := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop := isCoprime_Qr_Qe_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    h p r hp hmid hrE hle
  intro hres0
  have hnot := (Polynomial.resultant_eq_zero_iff (f := Q p r)
    (g := Q p (p - 1 - 2 * r))).mp hres0
  exact hnot.2 hcop

/-- Conditional corollary: `res(F, G) ≠ 0`, i.e. `QrFactor` and `QeFactor`
have no common root (including over the algebraic closure). -/
theorem resultant_QrFactor_QeFactor_ne_zero_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    (h : HA_mid_remainder_coprime_Qr) :
    ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
      (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0 := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop := isCoprime_Qr_Qe_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    h p r hp hmid hrE hle
  have hFGcop := ((isCoprime_Qr_Qe_iff p r hrE hmid).mp hcop).2
  intro h0
  have hnot := (Polynomial.resultant_eq_zero_iff (f := QrFactor p r)
    (g := QeFactor p r)).mp h0
  exact hnot.2 hFGcop

/-- Conditional corollary: `QrFactor` and `QeFactor` are coprime. -/
theorem isCoprime_QrFactor_QeFactor_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    (h : HA_mid_remainder_coprime_Qr) :
    ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
      IsCoprime (QrFactor p r) (QeFactor p r) := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop := isCoprime_Qr_Qe_of_middle_pair_of_HA_mid_remainder_coprime_Qr
    h p r hp hmid hrE hle
  exact ((isCoprime_Qr_Qe_iff p r hrE hmid).mp hcop).2

/-! ## The two established frontier hypotheses imply the full middle-pair gcd -/

/-- From the two recorded frontier hypotheses (`H_{2r} ≠ 0` and `res(F,G) ≠ 0`)
the full `gcd(Q_r, Q_e) = 1` follows unconditionally. -/
theorem isCoprime_Qr_Qe_of_middle_pair_of_frontier
    (hH : HA_mid_harmonicSum_two_mul_r_ne_zero)
    (hFG : HA_mid_resultant_F_G_ne_zero) :
    ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
      IsCoprime (Q p r) (Q p (p - 1 - 2 * r)) := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have hH' : harmonicSum p (2 * r) ≠ 0 := hH p r hp hmid hrE
  have hFG' : (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0 :=
    hFG p r hp hmid hrE
  have hFGcop : IsCoprime (QrFactor p r) (QeFactor p r) :=
    isCoprime_QrFactor_QeFactor_of_resultant_ne_zero p r hrE hmid hFG'
  exact (isCoprime_Qr_Qe_iff p r hrE hmid).mpr ⟨hH', hFGcop⟩

/-- The two frontier hypotheses imply the remainder separation lemma. -/
theorem HA_mid_remainder_coprime_Qr_of_frontier
    (hH : HA_mid_harmonicSum_two_mul_r_ne_zero)
    (hFG : HA_mid_resultant_F_G_ne_zero) :
    HA_mid_remainder_coprime_Qr := by
  intro p r hp hmid hrE hle
  haveI : Fact p.Prime := ⟨hp⟩
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  have hcop := isCoprime_Qr_Qe_of_middle_pair_of_frontier hH hFG p r hp hmid hrE hle
  exact (isCoprime_Qr_Qe_iff_isCoprime_Qr_midRemainder p r h1r hrlt).mp hcop

end

end Erdos291
