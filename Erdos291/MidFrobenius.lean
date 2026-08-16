import Erdos291.MidRoots
import Erdos291.MidAttackLine2
import Erdos291.MidCriticalSeparation
import Mathlib.RingTheory.Coprime.Basic

/-!
# Erdős #291 — Frobenius/degree elimination for the MID common-root problem

The user-supplied derivation tries to show that any common root `α ∉ F_p` of
`Q p r` and `Q p (p - 1 - 2r)` is a root of

    `U(X) = (X^p - X) * D'(X) + D(X)`,   `D = ∏_{a=1}^{2r} (X - a)`,

and then to eliminate such roots by proving `gcd(Q_r, U) = 1`.

This file records exactly which part of that plan is sound and which part is not.

## What is sound

For `D = intervalProduct p 1 (2*r)` and `e = p - 1 - 2r`, the identity

    `P p e * D = X^(p-1) - 1`     (`MidRoots.P_e_mul_R_eq_X_pow_pred_sub_one`)

differentiated gives

    `Q p e * D^2 = -X^(p-2) * D - (X^(p-1) - 1) * D'`.

Multiplying by `-X` gives the **corrected** Frobenius relation

    `U_corr = (X^p - X) * D' + X^(p-1) * D = -X * D^2 * Q p e`.

Hence `U_corr` is a multiple of `Q p e`: any root of `Q p e` (in particular any
common root of `Q p r` and `Q p e`) is a root of `U_corr`.  This is proved
purely polynomially below.

## What is not sound

The user's polynomial `U` (defined as `midFrobeniusPoly` below) is **not** a
consequence of the common-root configuration.  The step

    `Σ_{a=1}^{2r} 1/(α-a) = -1/(α^p-α)`

drops the `a = 0` term in the complement of the middle interval.  The correct
identity is

    `Σ_{a=0}^{2r} 1/(α-a) = -1/(α^p-α)`,

equivalently

    `(α^p - α) * (α * D)' + α * D = 0`,
    i.e.
    `(α^p - α) * D'(α) + α^(p-1) * D(α) = 0`.

The corrected annihilator `midFrobeniusPolyCorrected` is a multiple of `Q p e`
(proved below), so it gives no new information beyond `Q p e` itself.

Moreover the user's proposed universal statement `HA_mid_frobenius_coprime`
(`gcd(Q_r, midFrobeniusPoly) = 1` for every intrinsic MID pair) is **false**.
For `(p,r) = (271,58)` and `(401,76)` (both with `r ∈ E p`, `4r+1 < p`,
`p ≤ r^2`) the polynomial `Q p r` has F_p roots in `[1, 2r]` (`3,106` resp.
`90`), and since `eval x (midFrobeniusPoly p r) = eval x (intervalProduct p 1 (2r))`
for every `x : ZMod p`, those roots are common roots of `Q p r` and
`midFrobeniusPoly p r`.  Hence `gcd ≠ 1`.  We keep the definition below only as
a reference to the user-specified statement.

## Residual statement

The Frobenius/degree elimination does not yield a new coprime polynomial:
the only Frobenius annihilator that follows from the common-root configuration
is a multiple of `Q p e` (namely `midFrobeniusPolyCorrected`).  Therefore the
problem remains to prove `gcd(Q_r, Q_e) = 1` (equivalently
`HA_mid_resultant_Qr_Qe_ne_zero_intrinsic`); the corrected Frobenius polynomial
can only be used in the trivial implication

    `gcd(Q_r, U_corr) = 1  ⇒  gcd(Q_r, Q_e) = 1`,

whose hypothesis is strictly stronger than the conclusion and is itself false
for some intrinsic pairs (e.g. `(271,58)`).
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The user-specified Frobenius polynomial
`U = (X^p - X) * D' + D` with `D = intervalProduct p 1 (2*r)`.

**Warning:** this is not a consequence of the common-root configuration (the
derivation drops the `a = 0` complement term).  Moreover the universal
coprimality statement with this polynomial is false: see file docstring.
-/
noncomputable def midFrobeniusPoly (p r : ℕ) : Polynomial (ZMod p) :=
  ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) *
    Polynomial.derivative (intervalProduct p 1 (2 * r)) + intervalProduct p 1 (2 * r)

/-- The corrected Frobenius polynomial
`U_corr = (X^p - X) * D' + X^(p-1) * D` with `D = intervalProduct p 1 (2*r)`.

This is the polynomial that actually follows from the common-root configuration
(once the `a = 0` term is kept).  It is a multiple of `Q p e`; see
`midFrobeniusPolyCorrected_eq_neg_X_mul_D_sq_mul_Qe`.
-/
noncomputable def midFrobeniusPolyCorrected (p r : ℕ) : Polynomial (ZMod p) :=
  ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) *
    Polynomial.derivative (intervalProduct p 1 (2 * r)) +
    (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) * intervalProduct p 1 (2 * r)

/-- `X^p - X = X * (X^(p-1) - 1)` in the polynomial ring, for `0 < p`. -/
lemma X_pow_p_sub_X_eq_X_mul_X_pow_pred_sub_one (p : ℕ) (hp_pos : 0 < p) :
    ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) =
      Polynomial.X * ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) := by
  have hpp : p = (p - 1) + 1 := by omega
  have hpow : (Polynomial.X : Polynomial (ZMod p)) ^ p =
      (Polynomial.X : Polynomial (ZMod p)) ^ ((p - 1) + 1) := by
    exact congrArg (fun n => (Polynomial.X : Polynomial (ZMod p)) ^ n) hpp
  calc
    (Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X
        = Polynomial.X ^ ((p - 1) + 1) - Polynomial.X := by rw [hpow]
    _ = Polynomial.X ^ (p - 1) * Polynomial.X - Polynomial.X := by rw [pow_succ]
    _ = Polynomial.X * Polynomial.X ^ (p - 1) - Polynomial.X := by ring
    _ = Polynomial.X * (Polynomial.X ^ (p - 1) - 1) := by ring

/-- The corrected Frobenius polynomial equals `-X * D^2 * Q p e`; in particular
it is a multiple of `Q p e`.  This is the corrected version of the user's
Frobenius/degree elimination: the only annihilator that follows from the
common-root configuration carries no information beyond `Q p e`. -/
lemma midFrobeniusPolyCorrected_eq_neg_X_mul_D_sq_mul_Qe
    (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) :
    midFrobeniusPolyCorrected p r =
      -Polynomial.X * intervalProduct p 1 (2 * r) ^ 2 * Q p (p - 1 - 2 * r) := by
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hp_ge_two : 2 ≤ p := hp.two_le
  have hpp : p = (p - 1) + 1 := by omega
  have hp2 : p - 2 + 1 = p - 1 := by omega
  have hX : ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) =
      Polynomial.X * ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) :=
    X_pow_p_sub_X_eq_X_mul_X_pow_pred_sub_one p hp_pos
  have hXpow : Polynomial.X * (Polynomial.X : Polynomial (ZMod p)) ^ (p - 2) =
      (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) := by
    calc
      Polynomial.X * Polynomial.X ^ (p - 2) = Polynomial.X ^ (p - 2) * Polynomial.X := by ring
      _ = Polynomial.X ^ ((p - 2) + 1) := by rw [pow_succ]
      _ = Polynomial.X ^ (p - 1) :=
        congrArg (fun n => (Polynomial.X : Polynomial (ZMod p)) ^ n) hp2
  have hkey := Q_e_mul_R_sq_eq_neg_X_pow_pred_two_mul_R_sub_mul_derivative p r h2r
  let D : Polynomial (ZMod p) := intervalProduct p 1 (2 * r)
  have hkeyD : Q p (p - 1 - 2 * r) * D ^ 2 =
      -((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2) * D) -
        ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) * Polynomial.derivative D := by
    simpa [D] using hkey
  have hmul : -Polynomial.X * (Q p (p - 1 - 2 * r) * D ^ 2) =
      (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) * D +
        ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) *
          Polynomial.derivative D := by
    calc
      -Polynomial.X * (Q p (p - 1 - 2 * r) * D ^ 2)
          = -Polynomial.X * (-((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2) * D) -
              ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) * Polynomial.derivative D) := by
                rw [hkeyD]
      _ = (Polynomial.X * Polynomial.X ^ (p - 2)) * D +
            (Polynomial.X * (Polynomial.X ^ (p - 1) - 1)) * Polynomial.derivative D := by
              ring
      _ = Polynomial.X ^ (p - 1) * D +
            ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) * Polynomial.derivative D := by
              rw [hXpow, ← hX]
  calc
    midFrobeniusPolyCorrected p r
        = ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) *
            Polynomial.derivative D +
            (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) * D := by
              simp [midFrobeniusPolyCorrected, D]
    _ = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) * D +
            ((Polynomial.X : Polynomial (ZMod p)) ^ p - Polynomial.X) *
              Polynomial.derivative D := by ring
    _ = -Polynomial.X * (Q p (p - 1 - 2 * r) * D ^ 2) := by
              rw [← hmul]
    _ = -Polynomial.X * D ^ 2 * Q p (p - 1 - 2 * r) := by ring

/-- The user's polynomial differs from the corrected one by
`(1 - X^(p-1)) * D`. -/
lemma midFrobeniusPoly_eq_midFrobeniusPolyCorrected_add (p r : ℕ) :
    midFrobeniusPoly p r = midFrobeniusPolyCorrected p r +
      (1 - (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1)) *
        intervalProduct p 1 (2 * r) := by
  dsimp [midFrobeniusPoly, midFrobeniusPolyCorrected]
  ring

/-- The user's polynomial expressed through the corrected identity. -/
lemma midFrobeniusPoly_eq_neg_X_mul_D_sq_mul_Qe_add
    (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) :
    midFrobeniusPoly p r =
      -Polynomial.X * intervalProduct p 1 (2 * r) ^ 2 * Q p (p - 1 - 2 * r) +
        (1 - (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1)) *
          intervalProduct p 1 (2 * r) := by
  rw [midFrobeniusPoly_eq_midFrobeniusPolyCorrected_add,
    midFrobeniusPolyCorrected_eq_neg_X_mul_D_sq_mul_Qe p r h2r]

/-- The corrected Frobenius polynomial is divisible by `Q p e`. -/
lemma Qe_dvd_midFrobeniusPolyCorrected (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) :
    Q p (p - 1 - 2 * r) ∣ midFrobeniusPolyCorrected p r := by
  refine ⟨-(Polynomial.X * intervalProduct p 1 (2 * r) ^ 2), ?_⟩
  rw [midFrobeniusPolyCorrected_eq_neg_X_mul_D_sq_mul_Qe p r h2r]
  ring

/-- Trivial consequence of the corrected identity: any root of `Q p e` (over
`ZMod p`) is a root of the corrected Frobenius polynomial. -/
lemma eval_midFrobeniusPolyCorrected_eq_zero_of_eval_Q_e_eq_zero
    (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) (x : ZMod p)
    (hx : Polynomial.eval x (Q p (p - 1 - 2 * r)) = 0) :
    Polynomial.eval x (midFrobeniusPolyCorrected p r) = 0 := by
  rw [midFrobeniusPolyCorrected_eq_neg_X_mul_D_sq_mul_Qe p r h2r]
  simp [hx]

/-- The only sound Frobenius reduction: if `Q p r` is coprime to the corrected
Frobenius polynomial, then it is coprime to `Q p e`.  This is an immediate
consequence of `Q p e ∣ midFrobeniusPolyCorrected p r`.

Note: the hypothesis is strictly stronger than the conclusion (the corrected
polynomial contains the extra factor `-X * D^2`), and it is false for some
intrinsic pairs, e.g. `(271,58)`.  So this implication is logically correct but
does not help finish the proof. -/
lemma isCoprime_Qr_Qe_of_isCoprime_Qr_midFrobeniusPolyCorrected
    (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p)
    (h : IsCoprime (Q p r) (midFrobeniusPolyCorrected p r)) :
    IsCoprime (Q p r) (Q p (p - 1 - 2 * r)) := by
  exact h.of_isCoprime_of_dvd_right (Qe_dvd_midFrobeniusPolyCorrected p r h2r)

/-- For `x : ZMod p`, the user's Frobenius polynomial evaluates to `D(x)`
because `x^p = x`.  This explains why it shares the F_p roots of `D`
(`1, …, 2r`) with `Q p r` whenever `Q p r` has such roots. -/
lemma eval_midFrobeniusPoly_eq_eval_intervalProduct (p r : ℕ) [Fact p.Prime] (x : ZMod p) :
    Polynomial.eval x (midFrobeniusPoly p r) =
      Polynomial.eval x (intervalProduct p 1 (2 * r)) := by
  dsimp [midFrobeniusPoly]
  rw [Polynomial.eval_add, Polynomial.eval_mul]
  have hx : x ^ p = x := ZMod.pow_card x
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx]
  simp

/-- For `x : ZMod p`, the corrected Frobenius polynomial evaluates to
`x^(p-1) * D(x)`. -/
lemma eval_midFrobeniusPolyCorrected_eq_X_pow_pred_mul_eval_intervalProduct
    (p r : ℕ) [Fact p.Prime] (x : ZMod p) :
    Polynomial.eval x (midFrobeniusPolyCorrected p r) =
      x ^ (p - 1) * Polynomial.eval x (intervalProduct p 1 (2 * r)) := by
  dsimp [midFrobeniusPolyCorrected]
  rw [Polynomial.eval_add, Polynomial.eval_mul]
  have hx : x ^ p = x := ZMod.pow_card x
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hx]
  simp

/-- **User-specified hypothesis, false in general.**
The statement is: for every intrinsic MID pair, `Q p r` and
`midFrobeniusPoly p r` are coprime.

Computed evidence:
* `(61,10)`, `(109,25)`, `(227,22)`: `gcd = 1`.
* Counterexamples: `(271,58)` and `(401,76)` (both intrinsic, `r ∈ E p`,
  `4r+1 < p`, `p ≤ r^2`) have `gcd(Q_r, midFrobeniusPoly) ≠ 1`; for
  `(271,58)` the F_p roots `3` and `106` of `Q p r` lie in `[1, 2r]`, and
  `eval x (midFrobeniusPoly p r) = eval x D` for `x : ZMod p`.

Do not use this definition as an assumption in a proof of the middle
resultant: the implication claimed in the Frobenius/degree elimination is not
available because `midFrobeniusPoly` is not an annihilator of the common roots.
-/
def HA_mid_frobenius_coprime : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → p ≤ r ^ 2 →
    IsCoprime (Q p r) (midFrobeniusPoly p r)

end

end Erdos291
