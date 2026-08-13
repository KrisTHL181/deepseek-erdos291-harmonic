import Erdos291.Basic
import Erdos291.Characterization
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Erdős #291 — the "bad set" and the count `G`

For each prime `p`, the set `E p` collects the *bad* base-`p` digits `r ∈ [1, p - 1]`,
i.e. those for which `p` divides the numerator of the harmonic number `H_r` in lowest
terms. The definition is expressed purely in terms of `Rat.num (harmonic r)`, with no
prime assumption and no `ZMod` inverses, so that it is well-defined for every `p`. The
"rivet" section below then proves that for a prime `p` this is equivalent to the harmonic
sum `∑_{j=1}^r j⁻¹` vanishing mod `p`, linking `E p` back to the characterization in
`Characterization.lean`.

The count `G x` records how many `n ≤ x` have `gcd (a n) (L n) = 1`, and `c p` is the
density `|E p| / (p - 1)` of bad digits modulo `p`.
-/

open scoped BigOperators

namespace Erdos291

/-- The "bad" digits modulo `p`: `r ∈ [1, p - 1]` such that `p` divides the numerator
of the harmonic number `H_r` (in lowest terms). Defined for every `p` with no prime
assumption. -/
def E (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).filter fun r => (p : ℤ) ∣ (harmonic r).num

/-- `G x` is the number of `n` with `1 ≤ n ≤ x` such that `gcd (a n) (L n) = 1`. -/
def G (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => Nat.gcd (a n) (L n) = 1).card

/-- The density `|E p| / (p - 1)` of bad digits modulo `p`. -/
def c (p : ℕ) : ℚ := ((E p).card : ℚ) / ((p - 1) : ℚ)

/-! ## The rivet: `p ∣ (harmonic r).num` iff the `ZMod p` harmonic sum vanishes -/

/-- Reindex `∑_{i ∈ range r} f (i+1)` as `∑_{k ∈ Icc 1 r} f k`. -/
lemma sum_range_one_add (r : ℕ) (f : ℕ → ℚ) :
    (∑ i ∈ Finset.range r, f (i + 1)) = ∑ k ∈ Finset.Icc 1 r, f k := by
  refine Finset.sum_bij (fun i hi => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    have hi' : i < r := Finset.mem_range.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    omega
  · intro k hk
    have hk' : 1 ≤ k ∧ k ≤ r := Finset.mem_Icc.mp hk
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

/-- `harmonic r = a r / L r` as rationals. -/
lemma harmonic_eq_a_div_L (r : ℕ) : harmonic r = (a r : ℚ) / (L r : ℚ) := by
  rw [harmonic, sum_range_one_add r (fun k => (k : ℚ)⁻¹)]
  rw [a]
  have hcast : ((∑ k ∈ Finset.Icc 1 r, L r / k : ℕ) : ℚ) =
      ∑ k ∈ Finset.Icc 1 r, ((L r / k : ℕ) : ℚ) := by
    simp
  rw [hcast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkL : k ∣ L r := dvd_L_of_mem_Icc r k hk
  have hkpos : 0 < k := by
    have h1k : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    omega
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
  have hL0 : (L r : ℚ) ≠ 0 := by exact_mod_cast (L_ne_zero r)
  rw [Rat.natCast_div (L r) k hkL]
  field_simp [hk0, hL0]

/-- If `r < p`, then `p` does not divide `L r`. -/
lemma not_dvd_L_of_lt (p r : ℕ) [Fact p.Prime] (hrp : r < p) : ¬ p ∣ L r := by
  intro hdvd
  have hp : Nat.Prime p := Fact.out
  have hpadic : padicValNat p (L r) = 0 := by
    rw [lcmUpto_padicValNat p r hp]
    rw [Nat.log_eq_zero_iff]
    exact Or.inl hrp
  have hle : 1 ≤ padicValNat p (L r) := by
    have hdvd' : p ^ 1 ∣ L r := by simpa using hdvd
    exact (padicValNat_dvd_iff_le (p := p) (a := L r) (n := 1) (L_ne_zero r)).mp hdvd'
  omega

/-- The numerator of `a / b` (with `a, b : ℕ` coprime) is `a`. -/
lemma num_div_eq_of_coprime_nat (a b : ℕ) (hb : b ≠ 0) (h : Nat.Coprime a b) :
    (((a : ℚ) / (b : ℚ)).num) = (a : ℤ) := by
  have h' : (((a : ℤ) : ℚ) / ((b : ℤ) : ℚ)).num = (a : ℤ) :=
    Rat.num_div_eq_of_coprime (a := (a : ℤ)) (b := (b : ℤ))
      (by exact_mod_cast (Nat.pos_of_ne_zero hb)) (by simpa using h)
  simpa using h'

/-- The numerator of `a / b` (with `a, b : ℕ`) in lowest terms is `a / Nat.gcd a b`. -/
lemma num_div_eq_div_gcd (a b : ℕ) (hb : b ≠ 0) :
    (((a : ℚ) / (b : ℚ)).num) = ((a / Nat.gcd a b : ℕ) : ℤ) := by
  have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hb)
  have hgne : (Nat.gcd a b : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hgpos)
  have ha : (Nat.gcd a b : ℚ) * ((a / Nat.gcd a b : ℕ) : ℚ) = (a : ℚ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)]
  have hbg : (Nat.gcd a b : ℚ) * ((b / Nat.gcd a b : ℕ) : ℚ) = (b : ℚ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]
  have hred : (a : ℚ) / (b : ℚ) =
      ((a / Nat.gcd a b : ℕ) : ℚ) / ((b / Nat.gcd a b : ℕ) : ℚ) := by
    rw [← ha, ← hbg]
    field_simp [hgne]
  rw [hred]
  have hb0 : b / Nat.gcd a b ≠ 0 := by
    intro hz
    have hb_eq : Nat.gcd a b * (b / Nat.gcd a b) = b :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
    rw [hz, mul_zero] at hb_eq
    exact hb hb_eq.symm
  have hcop : Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  exact num_div_eq_of_coprime_nat (a / Nat.gcd a b) (b / Nat.gcd a b) hb0 hcop

/-- `p ∣ (harmonic r).num ↔ p ∣ a r` for `r < p`. -/
lemma num_dvd_iff_a_dvd (p r : ℕ) [Fact p.Prime] (hrp : r < p) :
    (p : ℤ) ∣ (harmonic r).num ↔ p ∣ a r := by
  have hp : Nat.Prime p := Fact.out
  let g := Nat.gcd (a r) (L r)
  have hnum : (harmonic r).num = ((a r / g : ℕ) : ℤ) := by
    rw [harmonic_eq_a_div_L r]
    exact num_div_eq_div_gcd (a r) (L r) (L_ne_zero r)
  have h1 : (p : ℤ) ∣ (harmonic r).num ↔ p ∣ (a r / g) := by
    rw [hnum]
    exact Int.natCast_dvd_natCast
  have hnotg : ¬ p ∣ g := by
    have hgL : g ∣ L r := Nat.gcd_dvd_right (a r) (L r)
    intro h
    exact not_dvd_L_of_lt p r hrp (dvd_trans h hgL)
  have hcop : Nat.Coprime p g := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnotg
  have hg_a : g ∣ a r := Nat.gcd_dvd_left (a r) (L r)
  have h2 : p ∣ (a r / g) ↔ p ∣ a r := by
    have har : a r = (a r / g) * g :=
      (Nat.mul_div_cancel' hg_a).symm.trans (mul_comm g (a r / g))
    constructor
    · intro h
      rw [har]
      exact dvd_mul_of_dvd_left h g
    · intro h
      have hmul : p ∣ (a r / g) * g := by
        rw [har] at h
        exact h
      exact (hcop.dvd_mul_right (m := a r / g)).mp hmul
  exact h1.trans h2

/-- `a r ≡ (L r) · Σ_{j≤r} j⁻¹  (mod p)`. -/
lemma a_mod_p_eq_L_mul_sum_inv (p r : ℕ) [Fact p.Prime] (hrp : r < p) :
    (a r : ZMod p) = ((L r : ℕ) : ZMod p) * (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) := by
  have hp : Nat.Prime p := Fact.out
  rw [a]
  have hcast : ((∑ k ∈ Finset.Icc 1 r, L r / k : ℕ) : ZMod p) =
      ∑ k ∈ Finset.Icc 1 r, ((L r / k : ℕ) : ZMod p) := by
    simp
  rw [hcast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k ≤ r := (Finset.mem_Icc.mp hk).2
  have hkp : k < p := lt_of_le_of_lt hkr hrp
  have hkpos : 0 < k := by
    have h1k : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    omega
  have hunit : IsUnit (k : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact (not_lt_of_ge (Nat.le_of_dvd hkpos hd)) hkp
  have hkL : k ∣ L r := dvd_L_of_mem_Icc r k hk
  exact zmod_div_mul_inv (p := p) (j := k) (m := L r) hkL hunit

/-- `p ∣ a r ↔ Σ_{j≤r} j⁻¹ = 0` in `ZMod p`, for `r < p`. -/
lemma p_dvd_a_iff_sum_inv_zero (p r : ℕ) [Fact p.Prime] (hrp : r < p) :
    p ∣ a r ↔ (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hc : (a r : ZMod p) =
      ((L r : ℕ) : ZMod p) * (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) :=
    a_mod_p_eq_L_mul_sum_inv p r hrp
  have hLunit : IsUnit ((L r : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact not_dvd_L_of_lt p r hrp
  rw [← ZMod.natCast_eq_zero_iff (a r) p]
  rw [hc]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hL0 | hS
    · exfalso
      exact hLunit.ne_zero hL0
    · exact hS
  · intro h
    rw [h, mul_zero]

/-- The rivet lemma: for `r < p`, `p ∣ (harmonic r).num` iff the harmonic-type sum
`Σ_{j≤r} j⁻¹` vanishes mod `p`. -/
lemma num_dvd_iff_sum_inv_zero (p r : ℕ) [Fact p.Prime] (hrp : r < p) :
    (p : ℤ) ∣ (harmonic r).num ↔
      (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) = 0 :=
  (num_dvd_iff_a_dvd p r hrp).trans (p_dvd_a_iff_sum_inv_zero p r hrp)

/-! ## Wolstenholme and pairing symmetry -/

/-- `Σ_{j=1}^{p-1} j⁻¹ = 0` in `ZMod p` for an odd prime `p` (Wolstenholme, the `p ∣ H_{p-1}`
part). -/
lemma sum_inv_Icc_one_pred_eq_zero (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod p)⁻¹)) = 0 := by
  have hp' : Nat.Prime p := Fact.out
  refine Finset.sum_involution (fun j hj => p - j) ?_ ?_ ?_ ?_
  · intro j hj
    have hj_le : j ≤ p - 1 := (Finset.mem_Icc.mp hj).2
    have hjp : j ≤ p := by omega
    have hcast : ((p - j : ℕ) : ZMod p) = -((j : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hjp]
      simp
    rw [hcast, inv_neg]
    ring
  · intro j hj hf
    have hj' : 1 ≤ j ∧ j ≤ p - 1 := Finset.mem_Icc.mp hj
    have hjp : j ≤ p := by omega
    intro h
    have hp_eq : p = 2 * j := by omega
    have h2 : 2 ∣ p := by
      rw [hp_eq]
      exact dvd_mul_right 2 j
    have heven : Even p := even_iff_two_dvd.mpr h2
    have hp_eq2 : p = 2 := (Nat.Prime.even_iff hp').mp heven
    omega
  · intro j hj
    have hj' : 1 ≤ j ∧ j ≤ p - 1 := Finset.mem_Icc.mp hj
    rw [Finset.mem_Icc]
    omega
  · intro j hj
    have hj' : 1 ≤ j ∧ j ≤ p - 1 := Finset.mem_Icc.mp hj
    omega

/-- `p - 1 ∈ E p` (Wolstenholme's `p ∣ H_{p-1}`). -/
lemma wolstenholme_mem_E (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : p - 1 ∈ E p := by
  rw [E]
  rw [Finset.mem_filter]
  constructor
  · rw [Finset.mem_Icc]
    omega
  · have hp1_lt : p - 1 < p := by omega
    rw [num_dvd_iff_sum_inv_zero p (p - 1) hp1_lt]
    exact sum_inv_Icc_one_pred_eq_zero p hp

/-- `Σ_{j ∈ Ico 1 (p-r)} j⁻¹ = -Σ_{j ∈ Ico (r+1) p} j⁻¹` via the involution `j ↦ p - j`. -/
lemma sum_inv_Ico_one_sub_eq_neg (p r : ℕ) [Fact p.Prime] (_hr : r ≤ p - 1) :
    (∑ j ∈ Finset.Ico 1 (p - r), ((j : ZMod p)⁻¹)) =
      -(∑ j ∈ Finset.Ico (r + 1) p, ((j : ZMod p)⁻¹)) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun j hj => p - j) ?_ ?_ ?_ ?_
  · intro j hj
    have hj' : 1 ≤ j ∧ j < p - r := Finset.mem_Ico.mp hj
    rw [Finset.mem_Ico]
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    have hj₁' : 1 ≤ j₁ ∧ j₁ < p - r := Finset.mem_Ico.mp hj₁
    have hj₂' : 1 ≤ j₂ ∧ j₂ < p - r := Finset.mem_Ico.mp hj₂
    omega
  · intro k hk
    have hk' : r + 1 ≤ k ∧ k < p := Finset.mem_Ico.mp hk
    refine ⟨p - k, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      omega
    · omega
  · intro j hj
    have hj' : 1 ≤ j ∧ j < p - r := Finset.mem_Ico.mp hj
    have hjp : j ≤ p := by omega
    have hcast : ((p - j : ℕ) : ZMod p) = -((j : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hjp]
      simp
    rw [hcast, inv_neg]
    ring

/-- `Ico 1 (n + 1) = Icc 1 n` for naturals. -/
lemma Ico_one_add_eq_Icc_one (n : ℕ) : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- `Ico 1 p = Icc 1 (p - 1)` for `1 ≤ p`. -/
lemma Ico_one_eq_Icc_one_pred (p : ℕ) (hp : 1 ≤ p) :
    Finset.Ico 1 p = Finset.Icc 1 (p - 1) := by
  ext x
  simp only [Finset.mem_Ico, Finset.mem_Icc]
  omega

/-- `Σ_{j=1}^{p-1-r} j⁻¹ = Σ_{j=1}^{r} j⁻¹` in `ZMod p` for an odd prime `p`. -/
lemma sum_inv_Icc_sub_eq_sum_inv (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hr : r ≤ p - 1) :
    (∑ j ∈ Finset.Icc 1 (p - 1 - r), ((j : ZMod p)⁻¹)) =
      (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) := by
  have hIco :
      (∑ j ∈ Finset.Ico 1 (p - r), ((j : ZMod p)⁻¹)) =
        (∑ j ∈ Finset.Ico 1 (r + 1), ((j : ZMod p)⁻¹)) := by
    have hreindex : (∑ j ∈ Finset.Ico 1 (p - r), ((j : ZMod p)⁻¹)) =
        -(∑ j ∈ Finset.Ico (r + 1) p, ((j : ZMod p)⁻¹)) :=
      sum_inv_Ico_one_sub_eq_neg p r hr
    have hsplit : (∑ j ∈ Finset.Ico 1 (r + 1), ((j : ZMod p)⁻¹)) +
        (∑ j ∈ Finset.Ico (r + 1) p, ((j : ZMod p)⁻¹)) =
        (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹)) :=
      Finset.sum_Ico_consecutive (fun j => ((j : ZMod p)⁻¹))
        (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ p)
    have htotal : (∑ j ∈ Finset.Ico 1 p, ((j : ZMod p)⁻¹)) = 0 := by
      rw [Ico_one_eq_Icc_one_pred p (by omega : 1 ≤ p)]
      exact sum_inv_Icc_one_pred_eq_zero p hp
    have hCB : (∑ j ∈ Finset.Ico 1 (r + 1), ((j : ZMod p)⁻¹)) =
        -(∑ j ∈ Finset.Ico (r + 1) p, ((j : ZMod p)⁻¹)) := by
      rw [← hsplit] at htotal
      exact eq_neg_of_add_eq_zero_left htotal
    exact hreindex.trans hCB.symm
  rw [← Ico_one_add_eq_Icc_one (p - 1 - r)]
  rw [show (p - 1 - r) + 1 = p - r by omega]
  rw [← Ico_one_add_eq_Icc_one r]
  exact hIco

/-- Pairing symmetry: for `r ∈ [1, p - 2]`, `r ∈ E p ↔ p - 1 - r ∈ E p`. -/
lemma mem_E_iff_pm_sub (p r : ℕ) [Fact p.Prime] (hr : r ∈ Finset.Icc 1 (p - 2)) :
    r ∈ E p ↔ p - 1 - r ∈ E p := by
  have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr_le : r ≤ p - 2 := (Finset.mem_Icc.mp hr).2
  have hr' : r ∈ Finset.Icc 1 (p - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hpmr : p - 1 - r ∈ Finset.Icc 1 (p - 1) := by
    rw [Finset.mem_Icc]
    omega
  have hp3 : 3 ≤ p := by omega
  have hr_lt : r < p := by omega
  have hpmr_lt : p - 1 - r < p := by omega
  have hsum : (∑ j ∈ Finset.Icc 1 (p - 1 - r), ((j : ZMod p)⁻¹)) =
      (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) :=
    sum_inv_Icc_sub_eq_sum_inv p r hp3 (by omega : r ≤ p - 1)
  rw [E]
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [hr', hpmr, true_and]
  rw [num_dvd_iff_sum_inv_zero p r hr_lt]
  rw [num_dvd_iff_sum_inv_zero p (p - 1 - r) hpmr_lt]
  rw [hsum]

/-! ## No two adjacent bad digits -/

/-- If `(r + 1) / 2 = (s + 1) / 2` then `s ≤ r + 1` (the map `r ↦ (r + 1) / 2` collapses
exactly the adjacent pairs `{2k - 1, 2k}`). -/
lemma div_two_eq_imp_le_succ (r s : ℕ) (h : (r + 1) / 2 = (s + 1) / 2) : s ≤ r + 1 := by
  have h1 : 2 * ((r + 1) / 2) ≤ r + 1 := by
    have hdiv : (r + 1) / 2 * 2 ≤ r + 1 := Nat.div_mul_le_self (r + 1) 2
    omega
  have h4 : s + 1 < 2 * ((s + 1) / 2 + 1) :=
    Nat.lt_mul_div_succ (s + 1) (by norm_num : 0 < 2)
  rw [← h] at h4
  omega

/-- If `(r + 1) / 2 = (s + 1) / 2` then `r` and `s` are either equal or adjacent. -/
lemma div_two_eq_imp_eq_or_adjacent (r s : ℕ) (h : (r + 1) / 2 = (s + 1) / 2) :
    r = s ∨ r + 1 = s ∨ s + 1 = r := by
  by_cases heq : r = s
  · exact Or.inl heq
  · have hs_le : s ≤ r + 1 := div_two_eq_imp_le_succ r s h
    have hr_le : r ≤ s + 1 := div_two_eq_imp_le_succ s r h.symm
    omega

/-- For an odd `p`, `p / 2 = (p - 1) / 2`. -/
lemma odd_div_two_eq (p : ℕ) (hp : Odd p) : p / 2 = (p - 1) / 2 := by
  rcases hp with ⟨k, rfl⟩
  omega

/-- `E p` contains no two consecutive integers: if `r ∈ E p` then `r + 1 ∉ E p`.  Indeed
`r, r + 1 ∈ E p` would give `∑_{j≤r} j⁻¹ = 0 = ∑_{j≤r+1} j⁻¹`, hence `(r + 1)⁻¹ = 0` in
`ZMod p`, impossible for a unit. -/
lemma not_mem_E_succ (p r : ℕ) [Fact p.Prime] (hp : 2 ≤ p) (hrE : r ∈ E p) :
    r + 1 ∉ E p := by
  intro hsuccE
  have hprime : Nat.Prime p := Fact.out
  have hrIcc : r + 1 ∈ Finset.Icc 1 (p - 1) := by
    unfold E at hsuccE
    exact (Finset.mem_filter.mp hsuccE).1
  have hsucc_lt_p : r + 1 < p := by
    have hle : r + 1 ≤ p - 1 := (Finset.mem_Icc.mp hrIcc).2
    omega
  have hr_lt_p : r < p := by omega
  have hdvd_r : (p : ℤ) ∣ (harmonic r).num := by
    unfold E at hrE
    exact (Finset.mem_filter.mp hrE).2
  have hdvd_succ : (p : ℤ) ∣ (harmonic (r + 1)).num := by
    unfold E at hsuccE
    exact (Finset.mem_filter.mp hsuccE).2
  have hsum_r : (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) = 0 :=
    (num_dvd_iff_sum_inv_zero p r hr_lt_p).mp hdvd_r
  have hsum_succ : (∑ j ∈ Finset.Icc 1 (r + 1), ((j : ZMod p)⁻¹)) = 0 :=
    (num_dvd_iff_sum_inv_zero p (r + 1) hsucc_lt_p).mp hdvd_succ
  have hsplit : (∑ j ∈ Finset.Icc 1 (r + 1), ((j : ZMod p)⁻¹)) =
      (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) + ((r + 1 : ℕ) : ZMod p)⁻¹ := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ r + 1)]
  have h_inv_zero : ((r + 1 : ℕ) : ZMod p)⁻¹ = 0 := by
    rw [hsplit] at hsum_succ
    rw [hsum_r] at hsum_succ
    simpa using hsum_succ
  have hunit : IsUnit ((r + 1 : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    intro hdvd
    have hpos : 0 < r + 1 := by omega
    exact (not_lt_of_ge (Nat.le_of_dvd hpos hdvd)) hsucc_lt_p
  exact (hunit.inv).ne_zero h_inv_zero

/-- For an odd prime `p`, the bad set `E p` has at most `(p - 1) / 2` elements: the
`(p - 1) / 2` consecutive pairs `{1, 2}, {3, 4}, …` each contribute at most one bad digit. -/
lemma E_card_le_half (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : (E p).card ≤ (p - 1) / 2 := by
  have hp2 : 2 ≤ p := by omega
  have hcard : (E p).card ≤ (Finset.Icc 1 (p / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun r => (r + 1) / 2) ?_ ?_
    · intro r hr
      have hrIcc : r ∈ Finset.Icc 1 (p - 1) := by
        unfold E at hr
        exact (Finset.mem_filter.mp hr).1
      have hr_lower : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
      have hr_upper : r ≤ p - 1 := (Finset.mem_Icc.mp hrIcc).2
      change (r + 1) / 2 ∈ Finset.Icc 1 (p / 2)
      rw [Finset.mem_Icc]
      constructor
      · have hdivpos : 0 < (r + 1) / 2 :=
          Nat.div_pos (by omega : 2 ≤ r + 1) (by norm_num : 0 < 2)
        omega
      · exact Nat.div_le_div_right (by omega : r + 1 ≤ p)
    · intro r hr s hs hf
      by_cases heq : r = s
      · exact heq
      · have hrel : r = s ∨ r + 1 = s ∨ s + 1 = r := div_two_eq_imp_eq_or_adjacent r s hf
        rcases hrel with heq' | hrel
        · exact (heq heq').elim
        · rcases hrel with hsucc | hpred
          · have hnot : r + 1 ∉ E p := not_mem_E_succ p r hp2 hr
            rw [← hsucc] at hs
            exact (hnot hs).elim
          · have hnot : s + 1 ∉ E p := not_mem_E_succ p s hp2 hs
            rw [← hpred] at hr
            exact (hnot hr).elim
  have hcardIcc : (Finset.Icc 1 (p / 2)).card = p / 2 := by
    rw [Nat.card_Icc]
    omega
  have hp_odd : Odd p := Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime p) (by omega : p ≠ 2)
  have hdiv : p / 2 = (p - 1) / 2 := odd_div_two_eq p hp_odd
  omega

/-! ## Small prime tables -/

lemma E_three : E 3 = {2} := by
  native_decide

lemma E_five : E 5 = {4} := by
  native_decide

lemma E_seven : E 7 = {6} := by
  native_decide

end Erdos291
