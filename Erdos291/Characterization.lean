import Erdos291.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Erdős #291 — the main characterization

The central lemma: for a prime `p` and an integer `n ≥ p`, with `e = Nat.log p n`
(the largest `e` with `p^e ≤ n`) and `r = n / p^e` (the leading base-`p` digit), we have

    p ∣ a n  ↔  ∑_{j=1}^r j⁻¹ = 0 in `ZMod p`.

Here `j⁻¹` is the multiplicative inverse of `j` modulo `p`. In particular, for `n = 2·3^e`
we have `r = 2`, and `1 + 1/2 = 3/2 ≡ 0 (mod 3)`, giving the `gcd > 1` direction of #291.
-/

open scoped BigOperators

namespace Erdos291

open Nat

/-- `padicValNat p (L n) = Nat.log p n`: the p-adic valuation of `lcm(1..n)` is
`⌊log_p n⌋`. This is already in mathlib as `Nat.factorization_lcmUpto`. -/
lemma lcmUpto_padicValNat (p n : ℕ) (hp : Nat.Prime p) :
    padicValNat p (L n) = Nat.log p n := by
  have h : (Nat.lcmUpto n).factorization p = Nat.log p n := Nat.factorization_lcmUpto n hp
  rw [Nat.factorization_def (Nat.lcmUpto n) hp] at h
  simpa [L] using h

/-- `p^Nat.log p n` divides `L n`. -/
lemma pow_log_dvd_L (p n : ℕ) (hp : Nat.Prime p) : p ^ Nat.log p n ∣ L n := by
  rw [L]
  rw [Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.lcmUpto_ne_zero n)]
  exact le_of_eq (Nat.factorization_lcmUpto n hp).symm

/-- The leading digit `r = n / p^e` is `< p`, hence every `j ≤ r` is a unit mod `p`. -/
lemma leadingDigit_lt (p n : ℕ) (hp : 1 < p) : n / p ^ Nat.log p n < p := by
  rw [Nat.div_lt_iff_lt_mul (pow_pos (lt_of_le_of_lt (by decide) hp) (Nat.log p n))]
  simpa [pow_succ, mul_comm] using (Nat.lt_pow_succ_log_self hp n)

/-- `padicValNat p (a / b) = padicValNat p a - padicValNat p b` when `b ∣ a`. -/
lemma padicValNat_div_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ∣ a) (ha : a ≠ 0) :
    padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
  rcases hb with ⟨c, hc⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    omega
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    omega
  have hdiv : a / b = c := by
    rw [hc]
    exact Nat.mul_div_right c (Nat.pos_of_ne_zero hb0)
  rw [hdiv]
  have hmul : padicValNat p (b * c) = padicValNat p b + padicValNat p c :=
    padicValNat.mul (p := p) hb0 hc0
  rw [← hc] at hmul
  omega

/-- If `p^Nat.log p n` does not divide `k` (with `1 ≤ k ≤ n`), then `p ∣ L n / k`. -/
lemma p_dvd_L_div_of_not_dvd_pow (p n k : ℕ) (hp : Nat.Prime p) (hk : k ∈ Finset.Icc 1 n)
    (h : ¬ p ^ Nat.log p n ∣ k) : p ∣ L n / k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hkL : k ∣ L n := dvd_L_of_mem_Icc n k hk
  have hk0 : k ≠ 0 := by
    have : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    omega
  have hdiv : padicValNat p (L n / k) = padicValNat p (L n) - padicValNat p k :=
    padicValNat_div_of_dvd (p := p) hkL (L_ne_zero n)
  have hvp : padicValNat p (L n) = Nat.log p n := lcmUpto_padicValNat p n hp
  rw [hvp] at hdiv
  have hk_le : padicValNat p k < Nat.log p n := by
    by_contra hkge
    have : Nat.log p n ≤ padicValNat p k := Nat.le_of_not_gt hkge
    have hpow : p ^ Nat.log p n ∣ k := by
      exact (padicValNat_dvd_iff_le (p := p) (a := k) (n := Nat.log p n) hk0).2 this
    exact h hpow
  have hle : 1 ≤ padicValNat p (L n / k) := by
    rw [hdiv]
    exact Nat.succ_le_iff.mpr (by omega)
  have hLk_ne : L n / k ≠ 0 := by
    intro hz
    have hpos : 0 < L n / k := Nat.div_pos (Nat.le_of_dvd (L_pos n) hkL) (Nat.pos_of_ne_zero hk0)
    omega
  simpa using (padicValNat_dvd_iff_le (p := p) (a := L n / k) (n := 1) hLk_ne).2 hle

/-- The terms of `a n` with `p^e ∤ k` vanish mod `p`. -/
lemma sum_a_eq_sum_filter (p n : ℕ) [Fact p.Prime] (hpn : p ≤ n) :
    (a n : ZMod p) =
      ∑ k ∈ (Finset.Icc 1 n).filter (fun k => p ^ Nat.log p n ∣ k), ((L n / k : ℕ) : ZMod p) := by
  have hp : Nat.Prime p := Fact.out
  let P : ℕ → Prop := fun k => p ^ Nat.log p n ∣ k
  rw [a]
  have hcast : (↑(∑ k ∈ Finset.Icc 1 n, L n / k) : ZMod p) =
      ∑ k ∈ Finset.Icc 1 n, ((L n / k : ℕ) : ZMod p) := by
    simpa using (map_sum (Nat.castRingHom (ZMod p)) (fun k => L n / k) (Finset.Icc 1 n))
  rw [hcast]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 n) P (fun k => ((L n / k : ℕ) : ZMod p))]
  have hzero : (∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ P k), ((L n / k : ℕ) : ZMod p)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkIcc : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hk).1
    have hnot : ¬ P k := (Finset.mem_filter.mp hk).2
    have hpdvd : p ∣ L n / k := p_dvd_L_div_of_not_dvd_pow p n k hp hkIcc hnot
    exact (ZMod.natCast_eq_zero_iff (L n / k) p).2 hpdvd
  simp [hzero, P]

/-- `j ∣ L n / p^e` whenever `p^e * j ∣ L n`. -/
lemma dvd_div_of_mul_dvd {p e j n : ℕ} (hp : 0 < p ^ e) (h : p ^ e * j ∣ L n) :
    j ∣ L n / p ^ e := by
  rcases h with ⟨q, hq⟩
  have hdiv : L n / p ^ e = j * q := by
    rw [hq, mul_assoc]
    rw [Nat.mul_div_right]
    exact hp
  rw [hdiv]
  exact Nat.dvd_mul_right j q

/-- In `ZMod p`, `↑(m / j) = ↑m * (↑j)⁻¹` when `j ∣ m` and `j` is a unit mod `p`. -/
lemma zmod_div_mul_inv {p j m : ℕ} [Fact p.Prime] (hjm : j ∣ m) (hunit : IsUnit (j : ZMod p)) :
    ((m / j : ℕ) : ZMod p) = ((m : ℕ) : ZMod p) * ((j : ZMod p)⁻¹) := by
  have hjm' : j * (m / j) = m := Nat.mul_div_cancel' hjm
  have hj0 : (j : ZMod p) ≠ 0 := hunit.ne_zero
  have hcast : (j : ZMod p) * ((m / j : ℕ) : ZMod p) = (m : ZMod p) := by
    rw [← Nat.cast_mul, hjm']
  calc
    ((m / j : ℕ) : ZMod p)
        = (j : ZMod p)⁻¹ * ((j : ZMod p) * ((m / j : ℕ) : ZMod p)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hj0, one_mul]
    _ = (j : ZMod p)⁻¹ * (m : ZMod p) := by rw [hcast]
    _ = (m : ZMod p) * (j : ZMod p)⁻¹ := by rw [mul_comm]

/-- The main congruence: `a n ≡ (L n / p^e) · Σ_{j=1}^r j⁻¹  (mod p)`. -/
lemma a_eq_mul_sum_inv (p n : ℕ) [Fact p.Prime] (hpn : p ≤ n) :
    (a n : ZMod p) =
      ((L n / p ^ Nat.log p n : ℕ) : ZMod p) *
        (∑ j ∈ Finset.Icc 1 (n / p ^ Nat.log p n), ((j : ZMod p)⁻¹)) := by
  have hp : Nat.Prime p := Fact.out
  have h1p : 1 < p := hp.one_lt
  rw [sum_a_eq_sum_filter p n hpn]
  rw [Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun j _ => p ^ Nat.log p n * j)
  · -- hi
    intro j hj
    have hjr : j ≤ n / p ^ Nat.log p n := (Finset.mem_Icc.mp hj).2
    have hjpos : 0 < j := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hj).1
    have hpej_le : p ^ Nat.log p n * j ≤ n := by
      calc
        p ^ Nat.log p n * j ≤ p ^ Nat.log p n * (n / p ^ Nat.log p n) :=
          Nat.mul_le_mul_left _ hjr
        _ ≤ n := Nat.mul_div_le n (p ^ Nat.log p n)
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos (pow_pos hp.pos _) hjpos), hpej_le⟩,
      Nat.dvd_mul_right (p ^ Nat.log p n) j⟩
  · -- i_inj
    intro j₁ hj₁ j₂ hj₂ h
    exact Nat.mul_left_cancel (pow_pos hp.pos _) h
  · -- i_surj
    intro k hk
    have hkIcc : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hk).1
    have hkP : p ^ Nat.log p n ∣ k := (Finset.mem_filter.mp hk).2
    have hkpos : 0 < k := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hkIcc).1
    refine ⟨k / p ^ Nat.log p n, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_of_lt (Nat.div_pos (Nat.le_of_dvd hkpos hkP) (pow_pos hp.pos _)),
        Nat.div_le_div_right (Finset.mem_Icc.mp hkIcc).2⟩
    · exact Nat.mul_div_cancel' hkP
  · -- value match
    intro j hj
    have hjr : j ≤ n / p ^ Nat.log p n := (Finset.mem_Icc.mp hj).2
    have hjpos : 0 < j := lt_of_lt_of_le (by decide) (Finset.mem_Icc.mp hj).1
    have hrlt : n / p ^ Nat.log p n < p := leadingDigit_lt p n h1p
    have hjp : j < p := lt_of_le_of_lt hjr hrlt
    have hunit : IsUnit (j : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_comm]
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      exact (not_lt_of_ge (Nat.le_of_dvd hjpos hd)) hjp
    have hpej_le : p ^ Nat.log p n * j ≤ n := by
      calc
        p ^ Nat.log p n * j ≤ p ^ Nat.log p n * (n / p ^ Nat.log p n) :=
          Nat.mul_le_mul_left _ hjr
        _ ≤ n := Nat.mul_div_le n (p ^ Nat.log p n)
    have hdvdL : p ^ Nat.log p n * j ∣ L n :=
      dvd_L_of_mem_Icc n (p ^ Nat.log p n * j) (by
        rw [Finset.mem_Icc]
        exact ⟨Nat.succ_le_of_lt (Nat.mul_pos (pow_pos hp.pos _) hjpos), hpej_le⟩)
    have hjdiv : j ∣ L n / p ^ Nat.log p n :=
      dvd_div_of_mul_dvd (p := p) (e := Nat.log p n) (j := j) (n := n) (pow_pos hp.pos _) hdvdL
    symm
    rw [show L n / (p ^ Nat.log p n * j) = (L n / p ^ Nat.log p n) / j by
          simpa using (Nat.div_div_eq_div_mul (L n) (p ^ Nat.log p n) j).symm]
    exact zmod_div_mul_inv (p := p) (j := j) (m := L n / p ^ Nat.log p n) hjdiv hunit

/-- `L n / p^e` is coprime to `p`. -/
lemma not_dvd_L_div_pow_log (p n : ℕ) (hp : Nat.Prime p) : ¬ p ∣ L n / p ^ Nat.log p n := by
  letI : Fact p.Prime := ⟨hp⟩
  have hdiv : padicValNat p (L n / p ^ Nat.log p n) = 0 := by
    rw [padicValNat.div_pow (p := p) (pow_log_dvd_L p n hp)]
    rw [lcmUpto_padicValNat p n hp]
    rw [Nat.sub_self]
  intro h
  have hle : 1 ≤ padicValNat p (L n / p ^ Nat.log p n) := by
    exact (padicValNat_dvd_iff_le (p := p) (a := L n / p ^ Nat.log p n) (n := 1)
      (by
        intro hz
        have hpos : 0 < L n / p ^ Nat.log p n := by
          apply Nat.div_pos
          · exact Nat.le_of_dvd (L_pos n) (pow_log_dvd_L p n hp)
          · exact pow_pos hp.pos (Nat.log p n)
        omega)).mp (by simpa using h)
  omega

/-- The characterization: `p ∣ a n` iff the harmonic-type sum `Σ_{j≤r} j⁻¹` vanishes mod `p`. -/
theorem dvd_a_iff_sum_inv_eq_zero (p n : ℕ) [Fact p.Prime] (hpn : p ≤ n) :
    p ∣ a n ↔
      (∑ j ∈ Finset.Icc 1 (n / p ^ Nat.log p n), ((j : ZMod p)⁻¹)) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hc : (a n : ZMod p) =
      ((L n / p ^ Nat.log p n : ℕ) : ZMod p) *
        (∑ j ∈ Finset.Icc 1 (n / p ^ Nat.log p n), ((j : ZMod p)⁻¹)) :=
    a_eq_mul_sum_inv p n hpn
  have hLp : IsUnit ((L n / p ^ Nat.log p n : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact not_dvd_L_div_pow_log p n hp
  rw [← ZMod.natCast_eq_zero_iff (a n) p]
  rw [hc]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hL0 | hS
    · exfalso
      exact hLp.ne_zero hL0
    · exact hS
  · intro h
    rw [h, mul_zero]

end Erdos291
