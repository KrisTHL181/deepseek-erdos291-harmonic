import Erdos291.MidQuarterLine
import Erdos291.MiddlePairStructure

/-!
# Erdős #291 — consequences of the quarter-line structure

This file wires the quarter-line results of `MidQuarterLine` into the
middle-pair coordinate system of `MiddlePairStructure` and the quartic
content route of `MidAttackLine3` (via `MidQuarterLine`'s import).

1. For a middle pair (`r ∈ E p`) the duplication shadow `2·H_{2r} = H_r + 2·C_r`
   gives `C_r = H_{2r}`; in particular `H_r = H_{2r} = 0` forces `C_r = 0`.
2. The sextic divisibility `D_mod p r ∣ Q p r` is *equivalent* to `H_{2r} = 0`
   for a middle pair, generalizing the quartic `A_poly_mod` equivalence of
   `MidTwoHalves`.
3. On the dangerous line `p = 4r + 5`, a middle pair forces `H_{2r} = 0`
   (equivalently the sextic divisibility and `C_r = 0`); numerically no such
   pair exists, so this reduces the dangerous-line case to `H_{2r} ≠ 0`.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## The odd walk under `H_r = 0` -/

/-- For `H_r = 0`, the duplication shadow `2·H_{2r} = H_r + 2·C_r` identifies
the odd walk at `r` with `H_{2r}`. -/
theorem oddWalk_eq_harmonicSum_two_mul_of_harmonicSum_zero
    (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hHr : harmonicSum p r = 0) :
    oddWalk p r = harmonicSum p (2 * r) := by
  have h2u : IsUnit (2 : ZMod p) := two_isUnit p hp
  have htwo : (2 : ZMod p) * harmonicSum p (2 * r) = (2 : ZMod p) * oddWalk p r := by
    rw [two_mul_harmonicSum_two_mul_eq_harmonicSum_add_two_mul_oddWalk p r hp, hHr]
    ring
  calc
    oddWalk p r = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * oddWalk p r) := by
          field_simp [h2u.ne_zero]
    _ = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * harmonicSum p (2 * r)) := by
          rw [htwo.symm]
    _ = harmonicSum p (2 * r) := by
          field_simp [h2u.ne_zero]

/-- `H_r = H_{2r} = 0` forces the odd walk at `r` to vanish. -/
theorem oddWalk_eq_zero_of_harmonicSum_zero (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hHr : harmonicSum p r = 0) (hH2r : harmonicSum p (2 * r) = 0) :
    oddWalk p r = 0 := by
  rw [oddWalk_eq_harmonicSum_two_mul_of_harmonicSum_zero p r hp hHr, hH2r]

/-! ## The sextic divisibility is equivalent to `H_{2r} = 0` -/

/-- The factor `X - C r` divides the sextic `D_mod p r`. -/
lemma X_sub_C_r_dvd_D_mod (p r : ℕ) :
    (Polynomial.X - Polynomial.C (r : ZMod p) : Polynomial (ZMod p)) ∣ D_mod p r := by
  refine ⟨Polynomial.X * (Polynomial.X + Polynomial.C ((r + 1 : ℕ) : ZMod p)) *
      (Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ZMod p)) *
      ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C (1 : ZMod p)) *
      ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ZMod p)), ?_⟩
  rw [D_mod]
  ring_nf

/-- For a middle pair, `D_mod p r ∣ Q p r` forces `H_{2r} = 0`: the divisor
contains `X - r`, and `Q p r(r) = (r+1)↑r · H_{2r}` with the rising factorial
a unit. -/
lemma harmonicSum_two_mul_eq_zero_of_D_mod_dvd_Q
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hD : D_mod p r ∣ Q p r) : harmonicSum p (2 * r) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  have hsub : (Polynomial.X - Polynomial.C (r : ZMod p) : Polynomial (ZMod p)) ∣ Q p r :=
    (X_sub_C_r_dvd_D_mod p r).trans hD
  rcases hsub with ⟨T, hT⟩
  have heval := congrArg (fun f : Polynomial (ZMod p) => Polynomial.eval (r : ZMod p) f) hT
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    sub_self, zero_mul] at heval
  have hQeq := eval_Q_p_r_eq_ascFactorial_mul_harmonicSum_two_mul_of_mem_E p r hrE
    (by omega : 2 * r + 1 < p)
  rw [hQeq] at heval
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
    have hlt : r + 1 + i < p := by omega
    intro hz
    have hpdvd : p ∣ r + 1 + i := (ZMod.natCast_eq_zero_iff (r + 1 + i) p).mp hz
    exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
  exact (mul_eq_zero.mp heval).resolve_left hasc_ne

/-- For a middle pair in the intrinsic regime, `H_{2r} = 0` iff the sextic
`D_mod p r` divides `Q p r` (the forward direction is
`MidQuarterLine.D_mod_dvd_Q_of_harmonicSum_zero`). -/
theorem harmonicSum_two_mul_eq_zero_iff_D_mod_dvd_Q
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    harmonicSum p (2 * r) = 0 ↔ D_mod p r ∣ Q p r := by
  constructor
  · intro hH2r
    have hHr : harmonicSum p r = 0 :=
      harmonicSum_middle_pair_zero p r hrE (by omega : r < p)
    exact D_mod_dvd_Q_of_harmonicSum_zero p r (mem_E_ge_one p r hrE) hmid hHr hH2r
  · intro hD
    exact harmonicSum_two_mul_eq_zero_of_D_mod_dvd_Q p r hrE hmid hD

/-! ## The sextic contains the quartic `A_poly_mod` -/

/-- `D_mod p r` is the quartic `A_poly_mod p r` times the two half-line factors
`(2X + 1)(2X + 2r + 1)`. -/
lemma D_mod_eq_A_poly_mod_mul_half_factors (p r : ℕ) :
    D_mod p r = A_poly_mod p r *
      (((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C (1 : ZMod p)) *
        ((2 : Polynomial (ZMod p)) * Polynomial.X + Polynomial.C ((2 * r + 1 : ℕ) : ZMod p))) := by
  rw [D_mod, A_poly_mod_eq]
  push_cast
  ring_nf

/-- Sextic divisibility implies quartic divisibility. -/
lemma A_poly_mod_dvd_Q_of_D_mod_dvd_Q (p r : ℕ) (hD : D_mod p r ∣ Q p r) :
    A_poly_mod p r ∣ Q p r := by
  have hsub : A_poly_mod p r ∣ D_mod p r := by
    rw [D_mod_eq_A_poly_mod_mul_half_factors]
    exact dvd_mul_right _ _
  exact hsub.trans hD

/-! ## The dangerous line `p = 4r + 5` -/

/-- On the dangerous line `p = 4r + 5`, the inverse of `r + 2` is `4 · 3⁻¹`. -/
lemma inv_r_add_two_of_p_eq_four_r_add_five (p r : ℕ) [Fact p.Prime]
    (hp : p = 4 * r + 5) : ((r + 2 : ℕ) : ZMod p)⁻¹ =
      (4 : ZMod p) * (3 : ZMod p)⁻¹ := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have h4u : IsUnit (4 : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro hz
    have hdvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hz
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h4mul : (4 : ZMod p) * ((r + 2 : ℕ) : ZMod p) = (3 : ZMod p) := by
    have hnat : 4 * (r + 2) = p + 3 := by omega
    have hcast : ((4 * (r + 2) : ℕ) : ZMod p) = ((p + 3 : ℕ) : ZMod p) := by rw [hnat]
    rw [Nat.cast_mul, Nat.cast_add] at hcast
    simpa using hcast
  have hdiv : ((r + 2 : ℕ) : ZMod p) = (3 : ZMod p) * (4 : ZMod p)⁻¹ := by
    calc
      ((r + 2 : ℕ) : ZMod p) = (4 : ZMod p)⁻¹ * ((4 : ZMod p) * ((r + 2 : ℕ) : ZMod p)) := by
            field_simp [h4u.ne_zero]
      _ = (4 : ZMod p)⁻¹ * (3 : ZMod p) := by rw [h4mul]
      _ = (3 : ZMod p) * (4 : ZMod p)⁻¹ := by ring
  have hInvEq := congrArg Inv.inv hdiv
  rw [mul_inv_rev, inv_inv] at hInvEq
  exact hInvEq

/-- On the dangerous line `p = 4r + 5`, a middle pair forces `H_{2r} = 0`. -/
theorem harmonicSum_two_mul_eq_zero_of_middle_pair_dangerous_line
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hp : p = 4 * r + 5) :
    harmonicSum p (2 * r) = 0 := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp3 : 3 ≤ p := by omega
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrlt : r < p := by omega
  have hmid : 2 * r + 1 < p := by omega
  have h3u : IsUnit (3 : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro hz
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hHr0 : harmonicSum p r = 0 := harmonicSum_middle_pair_zero p r hrE hrlt
  have hid := harmonicSum_middle_pair_identity p r hp3 hrE hmid
  have ht : (p - 1 - 2 * r) / 2 = r + 2 := by
    have hmul : 2 * (r + 2) = p - 1 - 2 * r := by omega
    rw [← hmul]
    exact Nat.mul_div_right (r + 2) (by norm_num : 0 < 2)
  rw [ht] at hid
  have h3q : (3 : ZMod p) * (fermatQuotient p : ZMod p) = (4 : ZMod p) :=
    (harmonicSum_eq_zero_iff_three_fermatQuotient_eq_four_of_p_eq_four_r_add_five p r hp).mp hHr0
  have hq : (fermatQuotient p : ZMod p) = (4 : ZMod p) * (3 : ZMod p)⁻¹ := by
    calc
      (fermatQuotient p : ZMod p) = (3 : ZMod p)⁻¹ * ((3 : ZMod p) * (fermatQuotient p : ZMod p)) := by
            field_simp [h3u.ne_zero]
      _ = (3 : ZMod p)⁻¹ * (4 : ZMod p) := by rw [h3q]
      _ = (4 : ZMod p) * (3 : ZMod p)⁻¹ := by ring
  have hHr1 : harmonicSum p (r + 1) = -(3 : ZMod p) * (fermatQuotient p : ZMod p) :=
    harmonicSum_quarter_eq_neg_three_mul_fermatQuotient p (r + 1) (by omega : p = 4 * (r + 1) + 1)
  have hHr2 : harmonicSum p (r + 2) =
      harmonicSum p (r + 1) + ((r + 2 : ℕ) : ZMod p)⁻¹ := by
    simpa [show r + 2 = (r + 1) + 1 by omega] using harmonicSum_succ p (r + 1)
  have hInv : ((r + 2 : ℕ) : ZMod p)⁻¹ = (4 : ZMod p) * (3 : ZMod p)⁻¹ :=
    inv_r_add_two_of_p_eq_four_r_add_five p r hp
  have hid0 : (0 : ZMod p) = (2 : ZMod p) * harmonicSum p (2 * r)
      - harmonicSum p (r + 2) - (2 : ZMod p) * (fermatQuotient p : ZMod p) := by
    rw [hHr0] at hid
    exact hid
  have hmain : (2 : ZMod p) * harmonicSum p (2 * r) = 0 := by
    rw [hHr2, hHr1, hInv, hq] at hid0
    have hsim : (2 : ZMod p) * harmonicSum p (2 * r)
        - (-(3 : ZMod p) * ((4 : ZMod p) * (3 : ZMod p)⁻¹) + (4 : ZMod p) * (3 : ZMod p)⁻¹)
        - (2 : ZMod p) * ((4 : ZMod p) * (3 : ZMod p)⁻¹)
        = (2 : ZMod p) * harmonicSum p (2 * r) := by
      field_simp [h3u.ne_zero]
      ring
    rw [hsim] at hid0
    exact hid0.symm
  have h2u : IsUnit (2 : ZMod p) := two_isUnit p hp3
  calc
    harmonicSum p (2 * r) = (2 : ZMod p)⁻¹ * ((2 : ZMod p) * harmonicSum p (2 * r)) := by
          field_simp [h2u.ne_zero]
    _ = (2 : ZMod p)⁻¹ * 0 := by rw [hmain]
    _ = 0 := by simp

/-- On the dangerous line `p = 4r + 5`, a middle pair forces `C_r = 0`. -/
theorem oddWalk_eq_zero_of_middle_pair_dangerous_line
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hp : p = 4 * r + 5) :
    oddWalk p r = 0 := by
  have hpge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  have hp3 : 3 ≤ p := by omega
  have hHr0 : harmonicSum p r = 0 :=
    harmonicSum_middle_pair_zero p r hrE (by omega : r < p)
  exact oddWalk_eq_zero_of_harmonicSum_zero p r hp3 hHr0
    (harmonicSum_two_mul_eq_zero_of_middle_pair_dangerous_line p r hrE hp)

/-- On the dangerous line `p = 4r + 5`, a middle pair forces the sextic
divisibility `D_mod p r ∣ Q p r`. -/
theorem D_mod_dvd_Q_of_middle_pair_dangerous_line
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hp : p = 4 * r + 5) :
    D_mod p r ∣ Q p r := by
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hmid : 4 * r + 1 < p := by omega
  have hHr : harmonicSum p r = 0 :=
    harmonicSum_middle_pair_zero p r hrE (by omega : r < p)
  exact D_mod_dvd_Q_of_harmonicSum_zero p r h1r hmid hHr
    (harmonicSum_two_mul_eq_zero_of_middle_pair_dangerous_line p r hrE hp)

end

end Erdos291
