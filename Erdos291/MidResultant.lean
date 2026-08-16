import Erdos291.BadDensity
import Erdos291.MidBlockRestrictions
import Erdos291.MiddlePairStructure
import Erdos291.GapPolynomial
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Div

/-!
# Erdős #291 — resultant structure of middle pairs

For a middle pair `(r, p)` (`2r + 1 < p` and `r ∈ E p`) the distance polynomials
`Q p r` and `Q p (p - 1 - 2r)` vanish at `0` and at `r` respectively.  Factoring
these linear factors out defines the two quotient polynomials

    `F = (Q p r) /ₘ X`, `G = (Q p (p - 1 - 2r)) /ₘ (X - C r)`,

and the resultant factors exactly over `ZMod p`:

    `resultant (Q p r) (Q p (p-1-2r)) =
       (-1)^{r-2} · e! · (r+1).ascFactorial r · r⁻¹ · H_{2r}² · resultant F G`

where `e = p - 1 - 2r`.  Consequences: `H_{2r} = 0` implies the resultant
vanishes (so `Nde r e` and `Nde (p-1-4r) (p-1-3r)` are divisible by `p`); the
resultant vanishes iff `H_{2r} = 0` or `F` and `G` share a root.

Numeric support: for 10924 intrinsic MID pairs (`4r+1 < p`, `r ≤ 20000`) both
`H_{2r}` and `H_t` are nonzero.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The quotient of `Q p r` by the factor `X` (which is a factor because `r ∈ E p`). -/
noncomputable def QrFactor (p r : ℕ) : Polynomial (ZMod p) :=
  (Q p r) /ₘ (Polynomial.X : Polynomial (ZMod p))

/-- The quotient of `Q p (p-1-2r)` by the factor `X - C r` (which is a factor for a middle
pair). -/
noncomputable def QeFactor (p r : ℕ) : Polynomial (ZMod p) :=
  (Q p (p - 1 - 2 * r)) /ₘ (Polynomial.X - Polynomial.C (r : ZMod p))

/-! ## Evaluation identities -/

/-- `eval 0 (Q p d) = d! * H_d` in `ZMod p`, for `d < p`. -/
lemma eval_zero_Q_eq_factorial_mul_harmonic (p d : ℕ) [Fact p.Prime] (hdlt : d < p) :
    Polynomial.eval (0 : ZMod p) (Q p d) = (Nat.factorial d : ZMod p) * harmonicSum p d := by
  have hp : Nat.Prime p := Fact.out
  have hunits : ∀ i ∈ Finset.Icc 1 d, IsUnit ((i : ℕ) : ZMod p) := by
    intro i hi
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
    exact (not_lt_of_ge (Nat.le_of_dvd hi'.1 hdvd)) (lt_of_le_of_lt hi'.2 hdlt)
  have hprodNat : (∏ j ∈ Finset.Icc 1 d, j) = Nat.factorial d := by
    rw [← Finset.prod_range_add_one_eq_factorial d]
    refine Finset.prod_bij (fun i hi => i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_range]
      have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ h
      have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ d := Finset.mem_Icc.mp hi₁
      have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ d := Finset.mem_Icc.mp hi₂
      omega
    · intro j hj
      have hj' : j < d := Finset.mem_range.mp hj
      refine ⟨j + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro i hi
      have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
      omega
  have hprodCast : (∏ j ∈ Finset.Icc 1 d, ((j : ℕ) : ZMod p)) = (Nat.factorial d : ZMod p) := by
    rw [← Nat.cast_prod]
    exact congrArg (fun n : ℕ => (n : ZMod p)) hprodNat
  rw [show Polynomial.eval (0 : ZMod p) (Q p d) =
    Polynomial.eval ((0 : ℕ) : ZMod p) (Q p d) by simp]
  rw [eval_Q_eq_sum_prod_erase]
  simp only [zero_add]
  rw [sum_prod_erase_eq_mul_inv (Finset.Icc 1 d) (fun i => ((i : ℕ) : ZMod p)) hunits]
  rw [hprodCast]
  rfl

/-- `eval r (Q p r) = (r+1).ascFactorial r · ∑_{j=r+1}^{2r} j⁻¹`, for `2r < p`. -/
lemma eval_Q_p_r_eq_ascFactorial_mul_sum_inv_Icc (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) :
    Polynomial.eval (r : ZMod p) (Q p r) =
      ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) *
        (∑ j ∈ Finset.Icc (r + 1) (2 * r), ((j : ZMod p)⁻¹)) := by
  have hp : Nat.Prime p := Fact.out
  have hunits : ∀ i ∈ Finset.Icc 1 r, IsUnit (((r + i : ℕ) : ZMod p)) := by
    intro i hi
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hge : 1 ≤ r + i := by omega
    have hle : r + i ≤ 2 * r := by omega
    exact (not_lt_of_ge (Nat.le_of_dvd hge hdvd)) (lt_of_le_of_lt hle h2r)
  have hprodNat : (∏ i ∈ Finset.Icc 1 r, (r + i)) = Nat.ascFactorial (r + 1) r := by
    rw [Nat.ascFactorial_eq_prod_range]
    refine Finset.prod_bij (fun i hi => i - 1) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_range]
      have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ h
      have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ r := Finset.mem_Icc.mp hi₁
      have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ r := Finset.mem_Icc.mp hi₂
      omega
    · intro j hj
      have hj' : j < r := Finset.mem_range.mp hj
      refine ⟨j + 1, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro i hi
      have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
      omega
  have hprodCast : (∏ i ∈ Finset.Icc 1 r, (((r + i : ℕ) : ZMod p))) =
      ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) := by
    rw [← Nat.cast_prod]
    exact congrArg (fun n : ℕ => (n : ZMod p)) hprodNat
  have hsumReindex : (∑ i ∈ Finset.Icc 1 r, (((r + i : ℕ) : ZMod p)⁻¹)) =
      (∑ j ∈ Finset.Icc (r + 1) (2 * r), ((j : ZMod p)⁻¹)) := by
    refine Finset.sum_bij (fun i hi => r + i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc]
      have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ h
      omega
    · intro j hj
      have hj' : r + 1 ≤ j ∧ j ≤ 2 * r := Finset.mem_Icc.mp hj
      refine ⟨j - r, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro i hi
      rfl
  rw [eval_Q_eq_sum_prod_erase]
  rw [sum_prod_erase_eq_mul_inv (Finset.Icc 1 r) (fun i => (((r + i : ℕ) : ZMod p))) hunits]
  rw [hprodCast, hsumReindex]

/-- For `r ∈ E p` and `2r+1 < p`, the `Icc (r+1) (2r)` harmonic block equals `H_{2r}`. -/
lemma sum_inv_Icc_add_eq_harmonicSum_two_mul_of_middle_pair (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    (∑ j ∈ Finset.Icc (r + 1) (2 * r), ((j : ZMod p)⁻¹)) = harmonicSum p (2 * r) := by
  have hr_lt : r < p := by omega
  have h2r : 2 * r < p := by omega
  have hsum2r : harmonicSum p (2 * r) = harmonicSum p r +
      (∑ j ∈ Finset.Icc (r + 1) (2 * r), ((j : ZMod p)⁻¹)) := by
    have hsplit := sum_Icc_split_add (fun j => ((j : ZMod p)⁻¹)) r r
    have hrr : r + r = 2 * r := by omega
    simpa [harmonicSum, hrr] using hsplit.symm
  rw [hsum2r, harmonicSum_middle_pair_zero p r hrE hr_lt, zero_add]

/-- `eval r (Q p r) = (r+1).ascFactorial r · H_{2r}` for a middle pair. -/
lemma eval_Q_p_r_eq_ascFactorial_mul_harmonicSum_two_mul_of_mem_E (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    Polynomial.eval (r : ZMod p) (Q p r) =
      ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r) := by
  have h2r : 2 * r < p := by omega
  rw [eval_Q_p_r_eq_ascFactorial_mul_sum_inv_Icc p r h2r]
  rw [sum_inv_Icc_add_eq_harmonicSum_two_mul_of_middle_pair p r hrE hmid]

/-- For a middle pair, `Q p (p-1-2r)` vanishes at `r`. -/
lemma eval_Q_p_e_eq_zero_of_middle_pair (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    Polynomial.eval (r : ZMod p) (Q p (p - 1 - 2 * r)) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hrIcc : r ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h1r, by omega⟩
  have hpmrE : p - 1 - r ∈ E p := (mem_E_iff_pm_sub p r hrIcc).mp hrE
  have he : 1 ≤ p - 1 - 2 * r := by omega
  have hle : r + (p - 1 - 2 * r) ≤ p - 1 := by omega
  have hradd : r + (p - 1 - 2 * r) ∈ E p := by
    have h : r + (p - 1 - 2 * r) = p - 1 - r := by omega
    simpa [h] using hpmrE
  exact eval_Q_eq_zero_of_mem_E_add p (p - 1 - 2 * r) r he hrE hradd hle

/-! ## Divisibility lemmas -/

/-- Two middle digits in an interval `[R, 2R)` force divisibility of two `Nde` values. -/
lemma Nde_dvd_of_two_mid_digits (p R r₁ r₂ : ℕ) [Fact p.Prime]
    (hR : 4 * R + 1 < p) (hr₁ : r₁ ∈ E p) (hr₂ : r₂ ∈ E p)
    (hR1 : R ≤ r₁) (h12 : r₁ < r₂) (h2 : r₂ < 2 * R) :
    p ∣ Nde (r₂ - r₁) (p - 1 - 2 * r₁) ∧ p ∣ Nde (r₂ - r₁) (p - 1 - r₁ - r₂) := by
  have hp : Nat.Prime p := Fact.out
  have h1r₁ : 1 ≤ r₁ := mem_E_ge_one p r₁ hr₁
  have h1r₂ : 1 ≤ r₂ := mem_E_ge_one p r₂ hr₂
  have hr₁Icc : r₁ ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h1r₁, by omega⟩
  have hr₂Icc : r₂ ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h1r₂, by omega⟩
  have hpmr₁E : p - 1 - r₁ ∈ E p := (mem_E_iff_pm_sub p r₁ hr₁Icc).mp hr₁
  have hpmr₂E : p - 1 - r₂ ∈ E p := (mem_E_iff_pm_sub p r₂ hr₂Icc).mp hr₂
  have hd : 1 ≤ r₂ - r₁ := by omega
  have he₁ : 1 ≤ p - 1 - 2 * r₁ := by omega
  have he₂ : 1 ≤ p - 1 - r₁ - r₂ := by omega
  have hle₁ : r₁ + max (r₂ - r₁) (p - 1 - 2 * r₁) ≤ p - 1 := by omega
  have hle₂ : r₁ + max (r₂ - r₁) (p - 1 - r₁ - r₂) ≤ p - 1 := by omega
  constructor
  · exact Nde_dvd_of_triple p (r₂ - r₁) (p - 1 - 2 * r₁) r₁ hd he₁ hr₁
      (by simpa [show r₁ + (r₂ - r₁) = r₂ by omega] using hr₂)
      (by simpa [show r₁ + (p - 1 - 2 * r₁) = p - 1 - r₁ by omega] using hpmr₁E)
      hle₁
  · exact Nde_dvd_of_triple p (r₂ - r₁) (p - 1 - r₁ - r₂) r₁ hd he₂ hr₁
      (by simpa [show r₁ + (r₂ - r₁) = r₂ by omega] using hr₂)
      (by simpa [show r₁ + (p - 1 - r₁ - r₂) = p - 1 - r₂ by omega] using hpmr₂E)
      hle₂

/-- If `H_{2r} = 0` for a middle pair in the intrinsic MID regime, then two `Nde` values
are divisible by `p`. -/
lemma Nde_dvd_of_harmonicSum_two_mul_r_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) (hH2r : harmonicSum p (2 * r) = 0) :
    p ∣ Nde r (p - 1 - 2 * r) ∧ p ∣ Nde (p - 1 - 4 * r) (p - 1 - 3 * r) := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have h2r_ge : 1 ≤ 2 * r := by omega
  have h2r_lt : 2 * r < p := by omega
  have hdvd2r : (p : ℤ) ∣ (harmonic (2 * r)).num :=
    (num_dvd_iff_sum_inv_zero p (2 * r) h2r_lt).mpr hH2r
  have h2rE : 2 * r ∈ E p := (mem_E_iff_dvd_num p (2 * r) hp h2r_ge h2r_lt).mpr hdvd2r
  have hrIcc : r ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h1r, by omega⟩
  have h2rIcc : 2 * r ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h2r_ge, by omega⟩
  have hpmrE : p - 1 - r ∈ E p := (mem_E_iff_pm_sub p r hrIcc).mp hrE
  have hpm2rE : p - 1 - 2 * r ∈ E p := (mem_E_iff_pm_sub p (2 * r) h2rIcc).mp h2rE
  have hd₁ : 1 ≤ r := h1r
  have he₁ : 1 ≤ p - 1 - 2 * r := by omega
  have hle₁ : r + max r (p - 1 - 2 * r) ≤ p - 1 := by omega
  have hd₂ : 1 ≤ p - 1 - 4 * r := by omega
  have he₂ : 1 ≤ p - 1 - 3 * r := by omega
  have hle₂ : 2 * r + max (p - 1 - 4 * r) (p - 1 - 3 * r) ≤ p - 1 := by omega
  constructor
  · exact Nde_dvd_of_triple p r (p - 1 - 2 * r) r hd₁ he₁ hrE
      (by simpa [show r + r = 2 * r by omega] using h2rE)
      (by simpa [show r + (p - 1 - 2 * r) = p - 1 - r by omega] using hpmrE)
      hle₁
  · exact Nde_dvd_of_triple p (p - 1 - 4 * r) (p - 1 - 3 * r) (2 * r) hd₂ he₂ h2rE
      (by simpa [show 2 * r + (p - 1 - 4 * r) = p - 1 - 2 * r by omega] using hpm2rE)
      (by simpa [show 2 * r + (p - 1 - 3 * r) = p - 1 - r by omega] using hpmrE)
      hle₂

/-- If `H_t = 0`, where `t = (p-1-2r)/2`, then four `Nde` values are divisible by `p`. -/
lemma Nde_dvd_of_harmonicSum_t_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hHt : harmonicSum p ((p - 1 - 2 * r) / 2) = 0) :
    p ∣ Nde (((p - 1 - 2 * r) / 2) - r) (p - 1 - 2 * r) ∧
    p ∣ Nde (((p - 1 - 2 * r) / 2) - r) (((p - 1 - 2 * r) / 2) + r) ∧
    p ∣ Nde (2 * r) (((p - 1 - 2 * r) / 2) + r) ∧
    p ∣ Nde (((p - 1 - 2 * r) / 2) + r) (p - 1 - 2 * r) := by
  set t : ℕ := (p - 1 - 2 * r) / 2 with ht
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hp_ne_two : p ≠ 2 := by omega
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp hp_ne_two
  have h2div : 2 ∣ p - 1 - 2 * r := by
    rcases hodd with ⟨m, hm⟩
    use m - r
    omega
  have ht2 : 2 * t = p - 1 - 2 * r := by
    rw [ht]
    exact Nat.mul_div_cancel' h2div
  have htr : r < t := by omega
  have h1t : 1 ≤ t := by omega
  have ht_lt_p : t < p := by omega
  have hHt' : harmonicSum p t = 0 := by
    simpa [t, ht] using hHt
  have hsum_t : (∑ j ∈ Finset.Icc 1 t, ((j : ZMod p)⁻¹)) = 0 := by
    simpa [harmonicSum] using hHt'
  have hdvd_t : (p : ℤ) ∣ (harmonic t).num :=
    (num_dvd_iff_sum_inv_zero p t ht_lt_p).mpr hsum_t
  have htE : t ∈ E p := (mem_E_iff_dvd_num p t hp h1t ht_lt_p).mpr hdvd_t
  have htIcc : t ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h1t, by omega⟩
  have hrIcc : r ∈ Finset.Icc 1 (p - 2) := by
    rw [Finset.mem_Icc]
    exact ⟨h1r, by omega⟩
  have hpmtE : p - 1 - t ∈ E p := (mem_E_iff_pm_sub p t htIcc).mp htE
  have hpmrE : p - 1 - r ∈ E p := (mem_E_iff_pm_sub p r hrIcc).mp hrE
  have hd₁ : 1 ≤ t - r := by omega
  have he₁ : 1 ≤ p - 1 - 2 * r := by omega
  have he₂ : 1 ≤ t + r := by omega
  have hd₃ : 1 ≤ 2 * r := by omega
  have hle₁ : r + max (t - r) (p - 1 - 2 * r) ≤ p - 1 := by omega
  have hle₂ : r + max (t - r) (t + r) ≤ p - 1 := by omega
  have hle₃ : t + max (2 * r) (t + r) ≤ p - 1 := by omega
  have hle₄ : r + max (t + r) (p - 1 - 2 * r) ≤ p - 1 := by omega
  have h1 := Nde_dvd_of_triple p (t - r) (p - 1 - 2 * r) r hd₁ he₁ hrE
    (by simpa [show r + (t - r) = t by omega] using htE)
    (by simpa [show r + (p - 1 - 2 * r) = p - 1 - r by omega] using hpmrE)
    hle₁
  have h2 := Nde_dvd_of_triple p (t - r) (t + r) r hd₁ he₂ hrE
    (by simpa [show r + (t - r) = t by omega] using htE)
    (by simpa [show r + (t + r) = p - 1 - t by omega] using hpmtE)
    hle₂
  have h3 := Nde_dvd_of_triple p (2 * r) (t + r) t hd₃ he₂ htE
    (by simpa [show t + 2 * r = p - 1 - t by omega] using hpmtE)
    (by simpa [show t + (t + r) = p - 1 - r by omega] using hpmrE)
    hle₃
  have h4 := Nde_dvd_of_triple p (t + r) (p - 1 - 2 * r) r he₂ he₁ hrE
    (by simpa [show r + (t + r) = p - 1 - t by omega] using hpmtE)
    (by simpa [show r + (p - 1 - 2 * r) = p - 1 - r by omega] using hpmrE)
    hle₄
  exact ⟨h1, h2, h3, h4⟩

/-! ## One-way resultant lemma -/

/-- If `H_{2r} = 0`, then the resultant of the two middle distance polynomials vanishes. -/
lemma resultant_Qr_Qe_eq_zero_of_harmonicSum_two_mul_r_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) (hH2r : harmonicSum p (2 * r) = 0) :
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) = 0 := by
  let d : ℕ := r
  let e : ℕ := p - 1 - 2 * r
  have hdvdNde : p ∣ Nde d e := by
    have h := Nde_dvd_of_harmonicSum_two_mul_r_zero p r hrE hmid hH2r
    simpa [d, e] using h.1
  have hdvdZ : (p : ℤ) ∣ (Polynomial.resultant (Qd d) (Qd e) : ℤ) :=
    (Int.natCast_dvd (m := p) (n := Polynomial.resultant (Qd d) (Qd e))).mpr hdvdNde
  have hz : ((Polynomial.resultant (Qd d) (Qd e) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.resultant (Qd d) (Qd e)) p).mpr hdvdZ
  have hd_ge : 1 ≤ d := by dsimp [d]; exact mem_E_ge_one p r hrE
  have hd_lt : d < p := by dsimp [d]; omega
  have he_ge : 1 ≤ e := by dsimp [e]; omega
  have he_lt : e < p := by dsimp [e]; omega
  have hdegd : ((Qd d).map (Int.castRingHom (ZMod p))).natDegree = (Qd d).natDegree := by
    rw [Qd_map p d]
    rw [Q_natDegree p d hd_ge hd_lt]
    rw [Qd_natDegree d]
  have hdege : ((Qd e).map (Int.castRingHom (ZMod p))).natDegree = (Qd e).natDegree := by
    rw [Qd_map p e]
    rw [Q_natDegree p e he_ge he_lt]
    rw [Qd_natDegree e]
  have hmap : Polynomial.resultant ((Qd d).map (Int.castRingHom (ZMod p)))
      ((Qd e).map (Int.castRingHom (ZMod p))) (Qd d).natDegree (Qd e).natDegree = 0 := by
    rw [Polynomial.resultant_map_map]
    exact hz
  have hres : (Polynomial.resultant (Q p d) (Q p e) : ZMod p) = 0 := by
    rw [← Qd_map p d, ← Qd_map p e]
    simpa [hdegd, hdege] using hmap
  simpa [d, e] using hres

/-! ## The exact factorization -/

/-- **Exact resultant factorization.** For a middle pair `(r, p)`,
`resultant (Q p r) (Q p (p-1-2r))` factors as
`(-1)^{r-2} · e! · (r+1).ascFactorial r · r⁻¹ · H_{2r}² · resultant F G`,
where `F = (Q p r)/ₘ X`, `G = (Q p (p-1-2r))/ₘ (X - C r)` and `e = p-1-2r`. -/
theorem resultant_Qr_Qe_factorization (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) =
      (-1 : ZMod p) ^ (r - 2) * (Nat.factorial (p - 1 - 2 * r) : ZMod p) *
      ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹ *
      (harmonicSum p (2 * r)) ^ 2 * Polynomial.resultant (QrFactor p r) (QeFactor p r) := by
  set e : ℕ := p - 1 - 2 * r with he
  let A : Polynomial (ZMod p) := Polynomial.X
  let B : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (r : ZMod p)
  let F : Polynomial (ZMod p) := QrFactor p r
  let G : Polynomial (ZMod p) := QeFactor p r
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hp3 : 3 ≤ p := by omega
  have hr_lt : r < p := by omega
  have h2rle : 2 * r ≤ p - 1 := by omega
  have he_ge : 1 ≤ e := by dsimp [e]; omega
  have he_lt : e < p := by dsimp [e]; omega
  -- Linear factors and their roots
  have hroot0 : (Q p r).IsRoot 0 := by
    rw [Polynomial.IsRoot, eval_zero_Q_eq_factorial_mul_harmonic p r hr_lt,
      harmonicSum_middle_pair_zero p r hrE hr_lt, mul_zero]
  have hrootR : (Q p e).IsRoot (r : ZMod p) := by
    rw [Polynomial.IsRoot]
    dsimp [e]
    exact eval_Q_p_e_eq_zero_of_middle_pair p r hrE hmid
  have hmulX : A * F = Q p r := by
    have h := (mul_divByMonic_eq_iff_isRoot (p := Q p r) (a := (0 : ZMod p))).2 hroot0
    simpa [A, F, QrFactor] using h
  have hmulE : B * G = Q p e := by
    have h := (mul_divByMonic_eq_iff_isRoot (p := Q p e) (a := (r : ZMod p))).2 hrootR
    simpa [B, G, QeFactor] using h
  -- Nonzero quotient polynomials and degree facts
  have hQr_ne : Q p r ≠ 0 := Q_ne_zero p r h1r hr_lt
  have hQe_ne : Q p e ≠ 0 := Q_ne_zero p e he_ge he_lt
  have hF_ne : F ≠ 0 := by
    intro hF0
    have hm := hmulX
    rw [hF0, mul_zero] at hm
    exact hQr_ne hm.symm
  have hG_ne : G ≠ 0 := by
    intro hG0
    have hm := hmulE
    rw [hG0, mul_zero] at hm
    exact hQe_ne hm.symm
  have hAFdeg : (A * F).natDegree = A.natDegree + F.natDegree := by
    dsimp [A]
    rw [Polynomial.natDegree_X_mul hF_ne]
    simp
    omega
  have hBGdeg : (B * G).natDegree = B.natDegree + G.natDegree := by
    dsimp [B]
    rw [Polynomial.natDegree_mul' (by
      rw [Polynomial.leadingCoeff_X_sub_C, one_mul]
      exact mt Polynomial.leadingCoeff_eq_zero.mp hG_ne)]
  have hQFdeg : (Q p r).natDegree = F.natDegree + 1 := by
    rw [← hmulX, hAFdeg]
    simp [A]
    omega
  have hBdeg : B.natDegree = 1 := by
    dsimp [B]
    rw [Polynomial.natDegree_X_sub_C]
  have hQGdeg : (Q p e).natDegree = G.natDegree + 1 := by
    rw [← hmulE, hBGdeg, hBdeg]
    omega
  have hQrdeg : (Q p r).natDegree = r - 1 := Q_natDegree p r h1r hr_lt
  have hFdeg : F.natDegree = r - 2 := by omega
  -- Unit `r` and evaluation of the two linear factors
  have hr_unit : IsUnit (r : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    exact (not_lt_of_ge (Nat.le_of_dvd h1r hdvd)) hr_lt
  have hr_ne : (r : ZMod p) ≠ 0 := hr_unit.ne_zero
  have hA0 : Polynomial.eval (0 : ZMod p) A = 0 := by simp [A]
  have hAr : Polynomial.eval (r : ZMod p) A = r := by simp [A]
  have hB0 : Polynomial.eval (0 : ZMod p) B = -(r : ZMod p) := by simp [B]
  -- Evaluation identities
  have hQe0 : Polynomial.eval (0 : ZMod p) (Q p e) =
      (Nat.factorial e : ZMod p) * harmonicSum p (2 * r) := by
    rw [eval_zero_Q_eq_factorial_mul_harmonic p e he_lt]
    have hH : harmonicSum p e = harmonicSum p (2 * r) := by
      have hsym := (harmonicSum_two_mul_r_eq_harmonicSum_pred_sub_two_mul_r p r hp3 h2rle).symm
      simpa [e, he] using hsym
    rw [hH]
  have hprod0 : (-(r : ZMod p)) * Polynomial.eval (0 : ZMod p) G =
      (Nat.factorial e : ZMod p) * harmonicSum p (2 * r) := by
    calc
      (-(r : ZMod p)) * Polynomial.eval (0 : ZMod p) G
          = Polynomial.eval (0 : ZMod p) (B * G) := by rw [Polynomial.eval_mul, hB0]
      _ = Polynomial.eval (0 : ZMod p) (Q p e) := by rw [hmulE]
      _ = (Nat.factorial e : ZMod p) * harmonicSum p (2 * r) := hQe0
  have hG0 : Polynomial.eval (0 : ZMod p) G =
      (-(r : ZMod p))⁻¹ * ((Nat.factorial e : ZMod p) * harmonicSum p (2 * r)) := by
    calc
      Polynomial.eval (0 : ZMod p) G
          = (-(r : ZMod p))⁻¹ * (-(r : ZMod p) * Polynomial.eval (0 : ZMod p) G) := by
              rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr hr_ne), one_mul]
      _ = (-(r : ZMod p))⁻¹ * ((Nat.factorial e : ZMod p) * harmonicSum p (2 * r)) := by
              rw [hprod0]
  have hQrR : Polynomial.eval (r : ZMod p) (Q p r) =
      ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r) :=
    eval_Q_p_r_eq_ascFactorial_mul_harmonicSum_two_mul_of_mem_E p r hrE hmid
  have hprodR : (r : ZMod p) * Polynomial.eval (r : ZMod p) F =
      ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r) := by
    calc
      (r : ZMod p) * Polynomial.eval (r : ZMod p) F
          = Polynomial.eval (r : ZMod p) (A * F) := by rw [Polynomial.eval_mul, hAr]
      _ = Polynomial.eval (r : ZMod p) (Q p r) := by rw [hmulX]
      _ = ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r) := hQrR
  have hFr : Polynomial.eval (r : ZMod p) F =
      (r : ZMod p)⁻¹ * ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) *
        harmonicSum p (2 * r) := by
    calc
      Polynomial.eval (r : ZMod p) F
          = (r : ZMod p)⁻¹ * ((r : ZMod p) * Polynomial.eval (r : ZMod p) F) := by
              rw [← mul_assoc, inv_mul_cancel₀ hr_ne, one_mul]
      _ = (r : ZMod p)⁻¹ * ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) *
            harmonicSum p (2 * r) := by
              rw [hprodR]
              rw [mul_assoc]
  -- Resultant of the product factorization
  have hleft := Polynomial.resultant_mul_left A F (B * G) (B.natDegree + G.natDegree)
    (by exact Polynomial.natDegree_mul_le)
  have hrightA := Polynomial.resultant_mul_right A B G A.natDegree le_rfl
  have hrightF := Polynomial.resultant_mul_right F B G F.natDegree le_rfl
  have hres : Polynomial.resultant (A * F) (B * G) (A.natDegree + F.natDegree)
      (B.natDegree + G.natDegree) =
      Polynomial.resultant A B A.natDegree B.natDegree *
      Polynomial.resultant A G A.natDegree G.natDegree *
      Polynomial.resultant F B F.natDegree B.natDegree *
      Polynomial.resultant F G F.natDegree G.natDegree := by
    rw [hleft, hrightA, hrightF]
    ring
  have hAB : Polynomial.resultant A B A.natDegree B.natDegree = -(r : ZMod p) := by
    rw [hBdeg]
    rw [Polynomial.resultant_X_sub_C_right (r : ZMod p) (f := A) (m := A.natDegree) le_rfl]
    simp [A]
  have hAG : Polynomial.resultant A G A.natDegree G.natDegree =
      Polynomial.eval (0 : ZMod p) G := by
    dsimp [A]
    rw [Polynomial.natDegree_X]
    rw [show Polynomial.X = Polynomial.X - Polynomial.C (0 : ZMod p) by simp]
    rw [Polynomial.resultant_X_sub_C_left (0 : ZMod p) (g := G) (n := G.natDegree) le_rfl]
  have hFB : Polynomial.resultant F B F.natDegree B.natDegree =
      (-1 : ZMod p) ^ F.natDegree * Polynomial.eval (r : ZMod p) F := by
    rw [hBdeg]
    rw [Polynomial.resultant_X_sub_C_right (r : ZMod p) (f := F) (m := F.natDegree) le_rfl]
  have hres_val : Polynomial.resultant (A * F) (B * G) (A.natDegree + F.natDegree)
      (B.natDegree + G.natDegree) =
      (-(r : ZMod p)) * Polynomial.eval (0 : ZMod p) G *
        ((-1 : ZMod p) ^ F.natDegree * Polynomial.eval (r : ZMod p) F) *
        Polynomial.resultant F G F.natDegree G.natDegree := by
    rw [hres, hAB, hAG, hFB]
  have hneg_inv : (-(r : ZMod p)) * (-(r : ZMod p))⁻¹ = 1 :=
    mul_inv_cancel₀ (neg_ne_zero.mpr hr_ne)
  have hrinv : (r : ZMod p) * (r : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hr_ne
  have hres_main : Polynomial.resultant (A * F) (B * G) (A.natDegree + F.natDegree)
      (B.natDegree + G.natDegree) =
      (-1 : ZMod p) ^ F.natDegree * (Nat.factorial e : ZMod p) *
        ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹ *
        (harmonicSum p (2 * r)) ^ 2 * Polynomial.resultant F G F.natDegree G.natDegree := by
    rw [hres_val, hG0, hFr]
    calc
      (-(r : ZMod p)) * ((-(r : ZMod p))⁻¹ * ((Nat.factorial e : ZMod p) * harmonicSum p (2 * r))) *
          ((-1 : ZMod p) ^ F.natDegree *
            ((r : ZMod p)⁻¹ * ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r))) *
          Polynomial.resultant F G F.natDegree G.natDegree
          = ((-(r : ZMod p)) * (-(r : ZMod p))⁻¹) * ((Nat.factorial e : ZMod p) * harmonicSum p (2 * r)) *
              ((-1 : ZMod p) ^ F.natDegree *
                ((r : ZMod p)⁻¹ * ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r))) *
              Polynomial.resultant F G F.natDegree G.natDegree := by ring
      _ = ((Nat.factorial e : ZMod p) * harmonicSum p (2 * r)) *
              ((-1 : ZMod p) ^ F.natDegree *
                ((r : ZMod p)⁻¹ * ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * harmonicSum p (2 * r))) *
              Polynomial.resultant F G F.natDegree G.natDegree := by rw [hneg_inv, one_mul]
      _ = (-1 : ZMod p) ^ F.natDegree * (Nat.factorial e : ZMod p) *
            ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹ *
            (harmonicSum p (2 * r)) * (harmonicSum p (2 * r)) *
            Polynomial.resultant F G F.natDegree G.natDegree := by ring
      _ = (-1 : ZMod p) ^ F.natDegree * (Nat.factorial e : ZMod p) *
            ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹ *
            (harmonicSum p (2 * r)) ^ 2 *
            Polynomial.resultant F G F.natDegree G.natDegree := by ring
  -- Relate the explicit-degree resultant to the default one
  have hres_default :
      Polynomial.resultant (Q p r) (Q p e) (Q p r).natDegree (Q p e).natDegree =
        Polynomial.resultant (A * F) (B * G) (A.natDegree + F.natDegree)
          (B.natDegree + G.natDegree) := by
    rw [← hmulX, ← hmulE]
    rw [hAFdeg, hBGdeg]
  calc
    Polynomial.resultant (Q p r) (Q p e)
        = Polynomial.resultant (Q p r) (Q p e) (Q p r).natDegree (Q p e).natDegree := rfl
    _ = Polynomial.resultant (A * F) (B * G) (A.natDegree + F.natDegree)
          (B.natDegree + G.natDegree) := hres_default
    _ = (-1 : ZMod p) ^ F.natDegree * (Nat.factorial e : ZMod p) *
          ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹ *
          (harmonicSum p (2 * r)) ^ 2 *
          Polynomial.resultant F G F.natDegree G.natDegree := hres_main
    _ = (-1 : ZMod p) ^ (r - 2) * (Nat.factorial (p - 1 - 2 * r) : ZMod p) *
          ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹ *
          (harmonicSum p (2 * r)) ^ 2 *
          Polynomial.resultant (QrFactor p r) (QeFactor p r) := by
            simp [e, F, G, hFdeg]

/-! ## Resultant zero criterion -/

/-- For a middle pair, the middle resultant vanishes iff `H_{2r} = 0` or the quotient
resultant `resultant F G` vanishes. -/
lemma resultant_Qr_Qe_eq_zero_iff (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p)
    (hmid : 2 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) = 0 ↔
      harmonicSum p (2 * r) = 0 ∨ Polynomial.resultant (QrFactor p r) (QeFactor p r) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have he_lt : p - 1 - 2 * r < p := by omega
  have hneg_ne : (-1 : ZMod p) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hpow_ne : (-1 : ZMod p) ^ (r - 2) ≠ 0 := pow_ne_zero _ hneg_ne
  have hfact_ne : (Nat.factorial (p - 1 - 2 * r) : ZMod p) ≠ 0 := by
    intro hz
    have hpdvd : p ∣ Nat.factorial (p - 1 - 2 * r) :=
      (ZMod.natCast_eq_zero_iff (Nat.factorial (p - 1 - 2 * r)) p).mp hz
    have hp_le : p ≤ p - 1 - 2 * r := (hp.dvd_factorial).mp hpdvd
    omega
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
  have hr_ne : (r : ZMod p) ≠ 0 := by
    intro hz
    have hpdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp hz
    exact (not_lt_of_ge (Nat.le_of_dvd h1r hpdvd)) hr_lt
  have hpref_ne : ((-1 : ZMod p) ^ (r - 2) * (Nat.factorial (p - 1 - 2 * r) : ZMod p) *
        ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) * (r : ZMod p)⁻¹) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpow_ne hfact_ne) hasc_ne) (inv_ne_zero hr_ne)
  constructor
  · intro h
    rw [resultant_Qr_Qe_factorization p r hrE hmid] at h
    rcases mul_eq_zero.mp h with h1 | hF
    · rcases mul_eq_zero.mp h1 with hpref | hHsq
      · exfalso
        exact hpref_ne hpref
      · left
        have hHmul : harmonicSum p (2 * r) * harmonicSum p (2 * r) = 0 := by
          simpa [pow_two] using hHsq
        exact (mul_eq_zero.mp hHmul).elim id id
    · right
      exact hF
  · intro h
    rcases h with hH | hF
    · rw [resultant_Qr_Qe_factorization p r hrE hmid, hH]
      simp
    · rw [resultant_Qr_Qe_factorization p r hrE hmid, hF]
      simp

end

end Erdos291
