import Erdos291.MidTwoHalves
import Mathlib.Algebra.BigOperators.ModEq

/-!
# Erdős #291 — pairing divisibility for `h_r` and `c_r`

The three parity-dependent integrality lemmas used to pass from the two half sums
`hN r` and `cN r` to the arithmetic gcd identity
`HA_arithmetic_gcd_hN_cN_dvd_factorial`:

1. If `r` is even, then `r + 1 ∣ hN r` (the `r+1`-denominator harmonic sum pairs
   into multiples of `r+1`).
2. If `r` is odd, then `r(2r+1) ∣ cN r - hN r` (stated over `ℤ`).
3. If `r` is even, then
   `r(r+1)(2r+1)(3r+1) ∣ (r+1)·cN r - (3r+1)·hN r` (stated over `ℤ`).

The common engine is a product-difference lemma: for a finite set `s ⊆ [1,r]`
closed under the reflection `i ↦ r+1-i`, the difference
`∏_{i∈s}(r+i) - ∏_{i∈s} i` is divisible by `r` (termwise expansion) and, when
`s.card` is even, by `2r+1` (each factor `r+i` is congruent to
`-(r+1-i)` modulo `2r+1`).  The odd-card variant with coefficients
`(3r+1)` and `(r+1)` is the pair contribution for the odd `r` case.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Small arithmetic helpers -/

private lemma add_div_div_eq_mul_div_of_dvd_mul {n a b : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a * b ∣ n) :
    n / a + n / b = (a + b) * (n / (a * b)) := by
  classical
  rcases hab with ⟨q, hq⟩
  have hmul_a : a * (b * q) = n := by
    rw [← Nat.mul_assoc]
    exact hq.symm
  have hdiva : b * q = n / a := Nat.eq_div_of_mul_eq_right ha0 hmul_a
  have hmul_b : b * (a * q) = n := by
    rw [← Nat.mul_assoc]
    rw [Nat.mul_comm b a]
    exact hq.symm
  have hdivb : a * q = n / b := Nat.eq_div_of_mul_eq_right hb0 hmul_b
  have hq' : q = n / (a * b) := by
    exact Nat.eq_div_of_mul_eq_right (Nat.mul_ne_zero ha0 hb0) hq.symm
  rw [← hdiva, ← hdivb, hq']
  ring

private lemma mul_dvd_factorial_of_lt_of_le {a b n : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hab : a ≠ b) (han : a ≤ n) (hbn : b ≤ n)
    (hle : a ≤ b) : a * b ∣ Nat.factorial n := by
  have hlt : a < b := lt_of_le_of_ne hle hab
  have hdvd_ab_b : a * b ∣ Nat.factorial b := by
    have hb_eq : b = (b - 1) + 1 := by omega
    have hfac : Nat.factorial b = b * Nat.factorial (b - 1) := by
      rw [hb_eq, Nat.factorial_succ]
      have harg : b - 1 + 1 - 1 = b - 1 := by omega
      rw [harg]
    have ha_le_bm1 : a ≤ b - 1 := by omega
    have hdvd_a_pred : a ∣ Nat.factorial (b - 1) := Nat.dvd_factorial ha0 ha_le_bm1
    have hmain : a * b ∣ Nat.factorial (b - 1) * b := Nat.mul_dvd_mul_right hdvd_a_pred b
    simpa [Nat.mul_comm, hfac] using hmain
  exact Nat.dvd_trans hdvd_ab_b (Nat.factorial_dvd_factorial hbn)

private lemma mul_dvd_factorial_of_lt {a b n : ℕ}
    (ha0 : 0 < a) (hb0 : 0 < b) (hab : a ≠ b) (han : a ≤ n) (hbn : b ≤ n) :
    a * b ∣ Nat.factorial n := by
  by_cases hle : a ≤ b
  · exact mul_dvd_factorial_of_lt_of_le ha0 hb0 hab han hbn hle
  · have hba : b ≤ a := le_of_not_ge hle
    have h := mul_dvd_factorial_of_lt_of_le hb0 ha0 (Ne.symm hab) hbn han hba
    simpa [Nat.mul_comm] using h

/-! ## The product-difference engine -/

private lemma int_dvd_r_prod_add_sub_prod (r : ℕ) (s : Finset ℕ) :
    (r : ℤ) ∣ (∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hcast : ((r + a : ℕ) : ℤ) = (r : ℤ) + (a : ℤ) := by
      norm_num [Nat.cast_add]
    rw [hcast]
    have h1 : (r : ℤ) ∣ (a : ℤ) *
        ((∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ))) :=
      dvd_mul_of_dvd_right ih (a : ℤ)
    have h2 : (r : ℤ) ∣ (r : ℤ) * (∏ i ∈ s, ((r + i : ℕ) : ℤ)) :=
      dvd_mul_right (r : ℤ) _
    rw [show ((r : ℤ) + (a : ℤ)) * (∏ i ∈ s, ((r + i : ℕ) : ℤ)) -
        (a : ℤ) * (∏ i ∈ s, (i : ℤ)) =
        (a : ℤ) * ((∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ))) +
          (r : ℤ) * (∏ i ∈ s, ((r + i : ℕ) : ℤ)) by ring]
    exact Int.dvd_add h1 h2

private lemma prod_symm_eq (r : ℕ) (s : Finset ℕ)
    (hsr : ∀ i ∈ s, i ≤ r) (hsym : ∀ i ∈ s, r + 1 - i ∈ s) :
    (∏ i ∈ s, ((r + 1 - i : ℕ) : ℤ)) = (∏ i ∈ s, (i : ℤ)) := by
  classical
  refine Finset.prod_bij (fun i hi => r + 1 - i) ?_ ?_ ?_ ?_
  · intro i hi
    exact hsym i hi
  · intro i₁ hi₁ i₂ hi₂ h
    have hi₁r : i₁ ≤ r := hsr i₁ hi₁
    have hi₂r : i₂ ≤ r := hsr i₂ hi₂
    omega
  · intro j hj
    refine ⟨r + 1 - j, hsym j hj, ?_⟩
    have hjr : j ≤ r := hsr j hj
    omega
  · intro i hi
    have hir : i ≤ r := hsr i hi
    omega

private lemma int_modEq_prod_add_sub_aux (r i : ℕ) (hi : i ≤ r) :
    ((r + i : ℕ) : ℤ) ≡ -((r + 1 - i : ℕ) : ℤ) [ZMOD (2 * r + 1 : ℕ)] := by
  have hsum : ((r + i : ℕ) : ℤ) + ((r + 1 - i : ℕ) : ℤ) = ((2 * r + 1 : ℕ) : ℤ) := by
    have hicast : ((r + 1 - i : ℕ) : ℤ) = ((r + 1 : ℕ) : ℤ) - (i : ℤ) := by
      rw [Nat.cast_sub (by omega : i ≤ r + 1)]
    rw [Nat.cast_add, hicast]
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [Int.modEq_iff_dvd]
  have hneg : -((r + 1 - i : ℕ) : ℤ) - ((r + i : ℕ) : ℤ) = -((2 * r + 1 : ℕ) : ℤ) := by
    rw [← hsum]
    ring
  rw [hneg]
  exact ⟨-1, by ring⟩

private lemma int_modEq_prod_add_sub (r : ℕ) (s : Finset ℕ)
    (hsr : ∀ i ∈ s, i ≤ r) (hsym : ∀ i ∈ s, r + 1 - i ∈ s) :
    (∏ i ∈ s, ((r + i : ℕ) : ℤ)) ≡
      ((-1 : ℤ) ^ s.card * (∏ i ∈ s, (i : ℤ))) [ZMOD (2 * r + 1 : ℕ)] := by
  classical
  have hpoint : ∀ i ∈ s, ((r + i : ℕ) : ℤ) ≡ -((r + 1 - i : ℕ) : ℤ)
      [ZMOD (2 * r + 1 : ℕ)] := by
    intro i hi
    exact int_modEq_prod_add_sub_aux r i (hsr i hi)
  have hprod := Int.ModEq.prod hpoint
  have hneg : (∏ i ∈ s, -((r + 1 - i : ℕ) : ℤ)) =
      (-1 : ℤ) ^ s.card * (∏ i ∈ s, ((r + 1 - i : ℕ) : ℤ)) := by
    rw [Finset.prod_neg]
  have hsymprod : (∏ i ∈ s, ((r + 1 - i : ℕ) : ℤ)) = (∏ i ∈ s, (i : ℤ)) :=
    prod_symm_eq r s hsr hsym
  simpa [hneg, hsymprod] using hprod

private lemma int_dvd_two_mul_add_one_prod_sub (r : ℕ) (s : Finset ℕ)
    (hsr : ∀ i ∈ s, i ≤ r) (hsym : ∀ i ∈ s, r + 1 - i ∈ s)
    (hcard : s.card % 2 = 0) :
    ((2 * r + 1 : ℕ) : ℤ) ∣
      ((∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ))) := by
  have hmod := int_modEq_prod_add_sub r s hsr hsym
  have hcard_even : Even s.card := by
    refine ⟨s.card / 2, ?_⟩
    have hdiv := Nat.div_add_mod s.card 2
    omega
  have hsign : (-1 : ℤ) ^ s.card = 1 := hcard_even.neg_one_pow
  have hAB : (∏ i ∈ s, ((r + i : ℕ) : ℤ)) ≡ (∏ i ∈ s, (i : ℤ))
      [ZMOD (2 * r + 1 : ℕ)] := by
    simpa [hsign] using hmod
  exact Int.modEq_iff_dvd.mp hAB.symm

private lemma int_dvd_two_mul_add_one_odd_comb (r : ℕ) (s : Finset ℕ)
    (hsr : ∀ i ∈ s, i ≤ r) (hsym : ∀ i ∈ s, r + 1 - i ∈ s)
    (hcard : s.card % 2 = 1) :
    ((2 * r + 1 : ℕ) : ℤ) ∣
      (((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ s, ((r + i : ℕ) : ℤ)) -
        ((r + 1 : ℕ) : ℤ) * (∏ i ∈ s, (i : ℤ))) := by
  let A : ℤ := ∏ i ∈ s, ((r + i : ℕ) : ℤ)
  let B : ℤ := ∏ i ∈ s, (i : ℤ)
  have hmod := int_modEq_prod_add_sub r s hsr hsym
  have hcard_odd : Odd s.card := by
    refine ⟨s.card / 2, ?_⟩
    have hdiv := Nat.div_add_mod s.card 2
    omega
  have hsign : (-1 : ℤ) ^ s.card = -1 := hcard_odd.neg_one_pow
  have hA : A ≡ -B [ZMOD (2 * r + 1 : ℕ)] := by
    simpa [A, B, hsign] using hmod
  have hsum : ((2 * r + 1 : ℕ) : ℤ) ∣ A + B := by
    simpa using (Int.modEq_iff_dvd.mp hA.symm)
  rcases hsum with ⟨c, hc⟩
  have hdec : ((3 * r + 1 : ℕ) : ℤ) * A - ((r + 1 : ℕ) : ℤ) * B =
      -((r + 1 : ℕ) : ℤ) * (A + B) + ((2 * r + 1 : ℕ) : ℤ) * (2 * A) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  rw [hdec]
  refine ⟨-((r + 1 : ℕ) : ℤ) * c + 2 * A, ?_⟩
  rw [hc]
  ring

private lemma coprime_r_two_mul_add_one (r : ℕ) : Nat.Coprime r (2 * r + 1) := by
  have h1 : Nat.Coprime r 1 := Nat.coprime_one_right r
  have h2 : Nat.Coprime r (r + 1) := (Nat.coprime_self_add_right (m := r) (n := 1)).mpr h1
  have h3 : Nat.Coprime r (r + (r + 1)) :=
    (Nat.coprime_self_add_right (m := r) (n := r + 1)).mpr h2
  simp [two_mul, Nat.add_assoc]

private lemma isCoprime_int_r_two_mul_add_one (r : ℕ) :
    IsCoprime (r : ℤ) ((2 * r + 1 : ℕ) : ℤ) := by
  have hnat : Nat.Coprime r (2 * r + 1) := coprime_r_two_mul_add_one r
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
  exact hnat

private lemma int_dvd_r_mul_two_mul_add_one_prod_sub (r : ℕ) (s : Finset ℕ)
    (hsr : ∀ i ∈ s, i ≤ r) (hsym : ∀ i ∈ s, r + 1 - i ∈ s)
    (hcard : s.card % 2 = 0) :
    ((r * (2 * r + 1) : ℕ) : ℤ) ∣
      ((∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ))) := by
  have hr_dvd : (r : ℤ) ∣
      (∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ)) :=
    int_dvd_r_prod_add_sub_prod r s
  have hm_dvd : ((2 * r + 1 : ℕ) : ℤ) ∣
      (∏ i ∈ s, ((r + i : ℕ) : ℤ)) - (∏ i ∈ s, (i : ℤ)) :=
    int_dvd_two_mul_add_one_prod_sub r s hsr hsym hcard
  have hcop : IsCoprime (r : ℤ) ((2 * r + 1 : ℕ) : ℤ) := isCoprime_int_r_two_mul_add_one r
  have hprod := hcop.mul_dvd hr_dvd hm_dvd
  have hcast : ((r * (2 * r + 1) : ℕ) : ℤ) = (r : ℤ) * ((2 * r + 1 : ℕ) : ℤ) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  exact hprod

private lemma int_dvd_r_mul_two_mul_add_one_odd_comb (r : ℕ) (s : Finset ℕ)
    (hsr : ∀ i ∈ s, i ≤ r) (hsym : ∀ i ∈ s, r + 1 - i ∈ s)
    (hcard : s.card % 2 = 1) :
    ((r * (2 * r + 1) : ℕ) : ℤ) ∣
      (((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ s, ((r + i : ℕ) : ℤ)) -
        ((r + 1 : ℕ) : ℤ) * (∏ i ∈ s, (i : ℤ))) := by
  let A : ℤ := ∏ i ∈ s, ((r + i : ℕ) : ℤ)
  let B : ℤ := ∏ i ∈ s, (i : ℤ)
  have hr_dvd : (r : ℤ) ∣ A - B := by
    dsimp [A, B]
    exact int_dvd_r_prod_add_sub_prod r s
  have hdec_r : ((3 * r + 1 : ℕ) : ℤ) * A - ((r + 1 : ℕ) : ℤ) * B =
      (A - B) + (r : ℤ) * (3 * A - B) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    ring
  have hr_dvd_comb : (r : ℤ) ∣ ((3 * r + 1 : ℕ) : ℤ) * A - ((r + 1 : ℕ) : ℤ) * B := by
    rw [hdec_r]
    exact Int.dvd_add hr_dvd (dvd_mul_right (r : ℤ) (3 * A - B))
  have hm_dvd : ((2 * r + 1 : ℕ) : ℤ) ∣
      ((3 * r + 1 : ℕ) : ℤ) * A - ((r + 1 : ℕ) : ℤ) * B := by
    dsimp [A, B]
    exact int_dvd_two_mul_add_one_odd_comb r s hsr hsym hcard
  have hcop : IsCoprime (r : ℤ) ((2 * r + 1 : ℕ) : ℤ) := isCoprime_int_r_two_mul_add_one r
  have hprod := hcop.mul_dvd hr_dvd_comb hm_dvd
  have hcast : ((r * (2 * r + 1) : ℕ) : ℤ) = (r : ℤ) * ((2 * r + 1 : ℕ) : ℤ) := by
    norm_num [Nat.cast_mul]
  rw [hcast]
  exact hprod

/-! ## The two half sums and their reindexed terms -/

private def cP (r : ℕ) : ℕ := ∏ i ∈ Finset.Icc (r + 1) (2 * r), i

private def cTerm (r j : ℕ) : ℕ := cP r / j

private def hTerm (r k : ℕ) : ℕ := Nat.factorial r / k

private def pairSet (r k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 r).erase k |>.erase (r + 1 - k)

private lemma cTerm_eq_prod_erase (r j : ℕ) (hj : j ∈ Finset.Icc (r + 1) (2 * r)) :
    cTerm r j = ∏ i ∈ (Finset.Icc (r + 1) (2 * r)).erase j, i := by
  classical
  unfold cTerm cP
  have hpos : j ≠ 0 := by
    rw [Finset.mem_Icc] at hj
    omega
  have hmul : j * (∏ i ∈ (Finset.Icc (r + 1) (2 * r)).erase j, i) =
      ∏ i ∈ Finset.Icc (r + 1) (2 * r), i := by
    rw [Finset.mul_prod_erase (Finset.Icc (r + 1) (2 * r)) (fun i => i) hj]
  exact (Nat.eq_div_of_mul_eq_right hpos hmul).symm

private lemma cN_eq_sum_cTerm (r : ℕ) :
    cN r = ∑ j ∈ Finset.Icc (r + 1) (2 * r), cTerm r j := by
  rw [cN]
  apply Finset.sum_congr rfl
  intro j hj
  exact (cTerm_eq_prod_erase r j hj).symm

private lemma cN_eq_sum_cTerm_Icc_one (r : ℕ) :
    cN r = ∑ k ∈ Finset.Icc 1 r, cTerm r (r + k) := by
  classical
  rw [cN_eq_sum_cTerm]
  refine (Finset.sum_bij (fun k hk => r + k) ?_ ?_ ?_ ?_).symm
  · intro k hk
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    omega
  · intro k₁ hk₁ k₂ hk₂ h
    rw [Finset.mem_Icc] at hk₁ hk₂
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨j - r, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro k hk
    rfl

private lemma hN_eq_sum_hTerm (r : ℕ) :
    hN r = ∑ k ∈ Finset.Icc 1 r, hTerm r k := by
  rw [hN, harmonicFactorial]
  rfl

private lemma cP_eq_prod_Icc_one_add (r : ℕ) :
    cP r = ∏ i ∈ Finset.Icc 1 r, (r + i) := by
  classical
  unfold cP
  refine (Finset.prod_bij (fun i hi => r + i) ?_ ?_ ?_ ?_).symm
  · intro i hi
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    rw [Finset.mem_Icc] at hi₁ hi₂
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨j - r, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    rfl

private lemma mul_prod_erase_two {s : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    f a * f b * (∏ i ∈ (s.erase a).erase b, f i) = ∏ i ∈ s, f i := by
  classical
  have hb' : b ∈ s.erase a := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hab, hb⟩
  rw [Nat.mul_assoc]
  rw [← Finset.mul_prod_erase s f ha]
  rw [← Finset.mul_prod_erase (s.erase a) f hb']

private lemma prod_div_mul_prod_erase_two {s : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hf0 : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i) / (f a * f b) = ∏ i ∈ (s.erase a).erase b, f i := by
  classical
  have hb' : b ∈ s.erase a := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hab, hb⟩
  have hmul_a := Finset.mul_prod_erase s f ha
  have hmul_b := Finset.mul_prod_erase (s.erase a) f hb'
  have hdiv_a : (∏ i ∈ s.erase a, f i) = (∏ i ∈ s, f i) / f a := by
    apply Nat.eq_div_of_mul_eq_right (hf0 a ha)
    simpa [Nat.mul_comm] using hmul_a
  have hdiv_b : (∏ i ∈ (s.erase a).erase b, f i) = (∏ i ∈ s.erase a, f i) / f b := by
    apply Nat.eq_div_of_mul_eq_right (hf0 b hb)
    simpa [Nat.mul_comm] using hmul_b
  calc
    (∏ i ∈ s, f i) / (f a * f b) = ((∏ i ∈ s, f i) / f a) / f b := by
          rw [Nat.div_div_eq_div_mul]
    _ = (∏ i ∈ s.erase a, f i) / f b := by rw [← hdiv_a]
    _ = ∏ i ∈ (s.erase a).erase b, f i := by rw [← hdiv_b]

private lemma cP_div_mul_eq_prod_pairSet (r k : ℕ) (hk : k ∈ Finset.Icc 1 r)
    (hk_ne : k ≠ r + 1 - k) :
    cP r / ((r + k) * (r + (r + 1 - k))) = ∏ i ∈ pairSet r k, (r + i) := by
  classical
  have hk' : r + 1 - k ∈ Finset.Icc 1 r := by
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    omega
  have hf0 : ∀ i ∈ Finset.Icc 1 r, (r + i) ≠ 0 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    omega
  have hprod : cP r = ∏ i ∈ Finset.Icc 1 r, (r + i) := cP_eq_prod_Icc_one_add r
  rw [hprod]
  have h := prod_div_mul_prod_erase_two (s := Finset.Icc 1 r) (f := fun i => (r + i))
    hk hk' hk_ne hf0
  simpa [pairSet] using h

private lemma factorial_div_mul_eq_prod_pairSet (r k : ℕ) (hk : k ∈ Finset.Icc 1 r)
    (hk_ne : k ≠ r + 1 - k) :
    Nat.factorial r / (k * (r + 1 - k)) = ∏ i ∈ pairSet r k, i := by
  classical
  have hk' : r + 1 - k ∈ Finset.Icc 1 r := by
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    omega
  have hf0 : ∀ i ∈ Finset.Icc 1 r, i ≠ 0 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    omega
  have hprod : Nat.factorial r = ∏ i ∈ Finset.Icc 1 r, i := (prod_Icc_one_eq_factorial r).symm
  rw [hprod]
  have h := prod_div_mul_prod_erase_two (s := Finset.Icc 1 r) (f := fun i => i)
    hk hk' hk_ne hf0
  simpa [pairSet] using h

private lemma cP_mul_dvd_pair (r k : ℕ) (hk : k ∈ Finset.Icc 1 r)
    (hk_ne : k ≠ r + 1 - k) :
    (r + k) * (r + (r + 1 - k)) ∣ cP r := by
  classical
  have hk' : r + 1 - k ∈ Finset.Icc 1 r := by
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    omega
  have hmul := mul_prod_erase_two (s := Finset.Icc 1 r) (f := fun i => (r + i))
    hk hk' hk_ne
  have hprod : cP r = ∏ i ∈ Finset.Icc 1 r, (r + i) := cP_eq_prod_Icc_one_add r
  rw [hprod]
  refine ⟨∏ i ∈ (Finset.Icc 1 r).erase k |>.erase (r + 1 - k), (r + i), ?_⟩
  simpa [pairSet] using hmul.symm

private lemma cTerm_pair_eq (r k : ℕ) (hk : k ∈ Finset.Icc 1 r)
    (hk_ne : k ≠ r + 1 - k) :
    cTerm r (r + k) + cTerm r (r + (r + 1 - k)) =
      (3 * r + 1) * (∏ i ∈ pairSet r k, (r + i)) := by
  classical
  have hdvd := cP_mul_dvd_pair r k hk hk_ne
  have ha0 : r + k ≠ 0 := by
    rw [Finset.mem_Icc] at hk
    omega
  have hb0 : r + (r + 1 - k) ≠ 0 := by
    rw [Finset.mem_Icc] at hk
    omega
  have hdiv := add_div_div_eq_mul_div_of_dvd_mul (n := cP r) (a := r + k)
    (b := r + (r + 1 - k)) ha0 hb0 hdvd
  unfold cTerm
  rw [hdiv]
  have hsum : (r + k) + (r + (r + 1 - k)) = 3 * r + 1 := by
    rw [Finset.mem_Icc] at hk
    omega
  rw [hsum]
  rw [cP_div_mul_eq_prod_pairSet r k hk hk_ne]

private lemma hTerm_pair_eq (r k : ℕ) (hk : k ∈ Finset.Icc 1 r)
    (hk_ne : k ≠ r + 1 - k) :
    hTerm r k + hTerm r (r + 1 - k) = (r + 1) * (∏ i ∈ pairSet r k, i) := by
  classical
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkr : k ≤ r := (Finset.mem_Icc.mp hk).2
  have hk'1 : 1 ≤ r + 1 - k := by omega
  have hk'r : r + 1 - k ≤ r := by omega
  have hdvd : k * (r + 1 - k) ∣ Nat.factorial r := by
    apply mul_dvd_factorial_of_lt
    · omega
    · omega
    · exact hk_ne
    · exact hkr
    · exact hk'r
  have hdiv := add_div_div_eq_mul_div_of_dvd_mul (n := Nat.factorial r) (a := k)
    (b := r + 1 - k) (by omega : k ≠ 0) (by omega : r + 1 - k ≠ 0) hdvd
  unfold hTerm
  rw [hdiv]
  have hsum : k + (r + 1 - k) = r + 1 := by omega
  rw [hsum]
  rw [factorial_div_mul_eq_prod_pairSet r k hk hk_ne]

/-! ## Membership, symmetry and cardinality of the pair set -/

private lemma pairSet_subset (r k : ℕ) :
    pairSet r k ⊆ Finset.Icc 1 r := by
  intro i hi
  simp only [pairSet, Finset.mem_erase] at hi
  rcases hi with ⟨hi_ne1, hi_ne2, hiI⟩
  exact hiI

private lemma pairSet_symm (r k : ℕ) (hk : k ∈ Finset.Icc 1 r) :
    ∀ i ∈ pairSet r k, r + 1 - i ∈ pairSet r k := by
  intro i hi
  rw [Finset.mem_Icc] at hk
  rcases Finset.mem_erase.mp hi with ⟨hi_ne, hi_erase⟩
  rcases Finset.mem_erase.mp hi_erase with ⟨hi_ne_k, hiI⟩
  rw [Finset.mem_Icc] at hiI
  simp only [pairSet, Finset.mem_erase, Finset.mem_Icc]
  omega

private lemma pairSet_card (r k : ℕ) (hk : k ∈ Finset.Icc 1 r)
    (hk_ne : k ≠ r + 1 - k) : (pairSet r k).card = r - 2 := by
  classical
  have hk' : r + 1 - k ∈ Finset.Icc 1 r := by
    rw [Finset.mem_Icc]
    rw [Finset.mem_Icc] at hk
    omega
  have hk'_mem : r + 1 - k ∈ (Finset.Icc 1 r).erase k := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hk_ne, hk'⟩
  rw [pairSet]
  rw [Finset.card_erase_of_mem hk'_mem]
  rw [Finset.card_erase_of_mem hk]
  rw [Nat.card_Icc]
  omega

private lemma card_pairSet_even_of_even {r k : ℕ} (hr : r % 2 = 0)
    (hk : k ∈ Finset.Icc 1 r) (hk_ne : k ≠ r + 1 - k) :
    (pairSet r k).card % 2 = 0 := by
  rw [Finset.mem_Icc] at hk
  rw [pairSet_card r k (Finset.mem_Icc.mpr hk) hk_ne]
  have hr_eq : r = 2 * (r / 2) := by
    have hdiv := Nat.div_add_mod r 2
    omega
  omega

private lemma card_pairSet_odd_of_odd {r k : ℕ} (hr : r % 2 = 1)
    (hk : k ∈ Finset.Icc 1 r) (hk_ne : k ≠ r + 1 - k) :
    (pairSet r k).card % 2 = 1 := by
  rw [Finset.mem_Icc] at hk
  rw [pairSet_card r k (Finset.mem_Icc.mpr hk) hk_ne]
  have hr_eq : r = 2 * (r / 2) + 1 := by
    have hdiv := Nat.div_add_mod r 2
    omega
  omega

private lemma card_erase_Icc_one (r k : ℕ) (hk : k ∈ Finset.Icc 1 r) :
    ((Finset.Icc 1 r).erase k).card = r - 1 := by
  rw [Finset.card_erase_of_mem hk]
  rw [Nat.card_Icc]
  omega

private lemma card_erase_Icc_one_even_of_odd {r k : ℕ} (hr : r % 2 = 1)
    (hk : k ∈ Finset.Icc 1 r) :
    ((Finset.Icc 1 r).erase k).card % 2 = 0 := by
  rw [Finset.mem_Icc] at hk
  rw [card_erase_Icc_one r k (Finset.mem_Icc.mpr hk)]
  have hr_eq : r = 2 * (r / 2) + 1 := by
    have hdiv := Nat.div_add_mod r 2
    omega
  omega

private lemma pairSet_subset_le {r k i : ℕ} (hi : i ∈ pairSet r k) : i ≤ r := by
  have h := pairSet_subset r k hi
  rw [Finset.mem_Icc] at h
  exact h.2

private lemma erase_Icc_one_subset_le {r k i : ℕ} (hi : i ∈ (Finset.Icc 1 r).erase k) :
    i ≤ r := by
  rw [Finset.mem_erase] at hi
  exact (Finset.mem_Icc.mp hi.2).2

private lemma erase_Icc_one_symm_of_fixed {r k : ℕ} (hk_fixed : k = r + 1 - k) :
    ∀ i ∈ (Finset.Icc 1 r).erase k, r + 1 - i ∈ (Finset.Icc 1 r).erase k := by
  intro i hi
  rw [Finset.mem_erase] at hi
  have hiI : i ∈ Finset.Icc 1 r := hi.2
  rw [Finset.mem_Icc] at hiI
  simp only [Finset.mem_erase, Finset.mem_Icc]
  omega

/-! ## Middle term (odd `r`) identities -/

private lemma cP_div_eq_prod_midSet (r k : ℕ) (hk : k ∈ Finset.Icc 1 r) :
    cP r / (r + k) = ∏ i ∈ (Finset.Icc 1 r).erase k, (r + i) := by
  classical
  have hprod : cP r = ∏ i ∈ Finset.Icc 1 r, (r + i) := cP_eq_prod_Icc_one_add r
  rw [hprod]
  have hf0 : r + k ≠ 0 := by
    rw [Finset.mem_Icc] at hk
    omega
  have hmul := Finset.mul_prod_erase (Finset.Icc 1 r) (fun i => (r + i)) hk
  symm
  apply Nat.eq_div_of_mul_eq_right hf0
  simpa [Nat.mul_comm] using hmul

private lemma cTerm_eq_prod_midSet_int (r k : ℕ) (hk : k ∈ Finset.Icc 1 r) :
    (cTerm r (r + k) : ℤ) = ∏ i ∈ (Finset.Icc 1 r).erase k, ((r + i : ℕ) : ℤ) := by
  unfold cTerm
  rw [cP_div_eq_prod_midSet r k hk]
  simp [Nat.cast_prod]

private lemma hTerm_eq_prod_midSet_int (r k : ℕ) (hk : k ∈ Finset.Icc 1 r) :
    (hTerm r k : ℤ) = ∏ i ∈ (Finset.Icc 1 r).erase k, (i : ℤ) := by
  unfold hTerm
  rw [← prod_Icc_one_erase_eq_factorial_div r k hk]
  simp [Nat.cast_prod]

/-! ## Lemma 1: `r+1 ∣ hN r` for even `r` -/

lemma hN_dvd_add_one_of_even (r : ℕ) (hr1 : 1 ≤ r) (hr : r % 2 = 0) :
    (r + 1) ∣ hN r := by
  classical
  have hreindex : hN r = ∑ k ∈ Finset.Icc 1 r, hTerm r (r + 1 - k) := by
    rw [hN_eq_sum_hTerm]
    refine Finset.sum_bij (fun k hk => r + 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc]
      rw [Finset.mem_Icc] at hk
      omega
    · intro k₁ hk₁ k₂ hk₂ h
      rw [Finset.mem_Icc] at hk₁ hk₂
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      refine ⟨r + 1 - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro k hk
      congr 1
      rw [Finset.mem_Icc] at hk
      omega
  have h2 : 2 * hN r = ∑ k ∈ Finset.Icc 1 r, (hTerm r k + hTerm r (r + 1 - k)) := by
    calc
      2 * hN r = hN r + hN r := by ring
      _ = (∑ k ∈ Finset.Icc 1 r, hTerm r k) +
          (∑ k ∈ Finset.Icc 1 r, hTerm r (r + 1 - k)) := by
            conv_lhs =>
              lhs
              rw [hN_eq_sum_hTerm]
            conv_lhs =>
              rhs
              rw [hreindex]
      _ = ∑ k ∈ Finset.Icc 1 r, (hTerm r k + hTerm r (r + 1 - k)) := by
            rw [Finset.sum_add_distrib]
  have hpair_dvd : ∀ k ∈ Finset.Icc 1 r,
      (r + 1) ∣ (hTerm r k + hTerm r (r + 1 - k)) := by
    intro k hk_mem
    have hk : 1 ≤ k ∧ k ≤ r := Finset.mem_Icc.mp hk_mem
    have hk_ne : k ≠ r + 1 - k := by
      intro h
      have h2k : 2 * k = r + 1 := by omega
      omega
    have hpair := hTerm_pair_eq r k hk_mem hk_ne
    rw [hpair]
    exact dvd_mul_right (r + 1) _
  have hsum_dvd : (r + 1) ∣ ∑ k ∈ Finset.Icc 1 r, (hTerm r k + hTerm r (r + 1 - k)) :=
    Finset.dvd_sum hpair_dvd
  have h2_dvd : (r + 1) ∣ 2 * hN r := by
    simpa [h2] using hsum_dvd
  have hodd_r1 : Odd (r + 1) := by
    refine ⟨r / 2, ?_⟩
    have hdiv := Nat.div_add_mod r 2
    omega
  have hcop : Nat.Coprime (r + 1) 2 := hodd_r1.coprime_two_right
  exact (hcop.dvd_mul_right).mp (by simpa [Nat.mul_comm] using h2_dvd)

/-! ## Lemma 2: the odd numerator over `ℤ` -/

lemma odd_numerator_dvd_int (r : ℕ) (hr : r % 2 = 1) :
    ((r * (2 * r + 1) : ℕ) : ℤ) ∣ ((cN r : ℤ) - (hN r : ℤ)) := by
  classical
  let D : ℕ → ℤ := fun k => (cTerm r (r + k) : ℤ) - (hTerm r k : ℤ)
  have hDsum : ((cN r : ℤ) - (hN r : ℤ)) = ∑ k ∈ Finset.Icc 1 r, D k := by
    rw [cN_eq_sum_cTerm_Icc_one, hN_eq_sum_hTerm]
    simp [D, Nat.cast_sum, Finset.sum_sub_distrib]
  have hreindex : ((cN r : ℤ) - (hN r : ℤ)) = ∑ k ∈ Finset.Icc 1 r, D (r + 1 - k) := by
    rw [hDsum]
    refine Finset.sum_bij (fun k hk => r + 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc]
      rw [Finset.mem_Icc] at hk
      omega
    · intro k₁ hk₁ k₂ hk₂ h
      rw [Finset.mem_Icc] at hk₁ hk₂
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      refine ⟨r + 1 - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro k hk
      congr 1
      rw [Finset.mem_Icc] at hk
      omega
  have h2D : 2 * ((cN r : ℤ) - (hN r : ℤ)) =
      ∑ k ∈ Finset.Icc 1 r, (D k + D (r + 1 - k)) := by
    calc
      2 * ((cN r : ℤ) - (hN r : ℤ)) =
          ((cN r : ℤ) - (hN r : ℤ)) + ((cN r : ℤ) - (hN r : ℤ)) := by ring
      _ = (∑ k ∈ Finset.Icc 1 r, D k) + (∑ k ∈ Finset.Icc 1 r, D (r + 1 - k)) := by
            conv_lhs =>
              lhs
              rw [hDsum]
            conv_lhs =>
              rhs
              rw [hreindex]
      _ = ∑ k ∈ Finset.Icc 1 r, (D k + D (r + 1 - k)) := by
            rw [Finset.sum_add_distrib]
  have hpair_dvd : ∀ k ∈ Finset.Icc 1 r,
      ((r * (2 * r + 1) : ℕ) : ℤ) ∣ (D k + D (r + 1 - k)) := by
    intro k hk_mem
    have hk : 1 ≤ k ∧ k ≤ r := Finset.mem_Icc.mp hk_mem
    by_cases hk_eq : k = r + 1 - k
    · have hmid_dvd : ((r * (2 * r + 1) : ℕ) : ℤ) ∣ D k := by
        simpa [D, cTerm_eq_prod_midSet_int r k hk_mem, hTerm_eq_prod_midSet_int r k hk_mem,
          Nat.cast_add] using
          (int_dvd_r_mul_two_mul_add_one_prod_sub r ((Finset.Icc 1 r).erase k)
            (fun i hi => erase_Icc_one_subset_le hi) (erase_Icc_one_symm_of_fixed hk_eq)
            (card_erase_Icc_one_even_of_odd hr hk_mem))
      have hDk2 : D k + D (r + 1 - k) = 2 * D k := by
        rw [← hk_eq]
        ring
      rw [hDk2]
      exact dvd_mul_of_dvd_right hmid_dvd 2
    · have hD_pair : D k + D (r + 1 - k) =
          ((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) -
            ((r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, (i : ℤ)) := by
        let A : ℤ := ∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)
        let B : ℤ := ∏ i ∈ pairSet r k, (i : ℤ)
        have hc_pair := cTerm_pair_eq r k hk_mem hk_eq
        have hh_pair := hTerm_pair_eq r k hk_mem hk_eq
        have hc_sum : (cTerm r (r + k) : ℤ) + (cTerm r (r + (r + 1 - k)) : ℤ) =
            ((3 * r + 1 : ℕ) : ℤ) * A := by
          rw [← Nat.cast_add, hc_pair]
          simp [A, Nat.cast_prod]
        have hh_sum : (hTerm r k : ℤ) + (hTerm r (r + 1 - k) : ℤ) =
            ((r + 1 : ℕ) : ℤ) * B := by
          rw [← Nat.cast_add, hh_pair]
          simp [B, Nat.cast_prod]
        calc
          D k + D (r + 1 - k)
              = ((cTerm r (r + k) : ℤ) + (cTerm r (r + (r + 1 - k)) : ℤ)) -
                ((hTerm r k : ℤ) + (hTerm r (r + 1 - k) : ℤ)) := by
                  dsimp [D]; ring
          _ = ((3 * r + 1 : ℕ) : ℤ) * A - ((r + 1 : ℕ) : ℤ) * B := by
                  rw [hc_sum, hh_sum]
          _ = ((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) -
                ((r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, (i : ℤ)) := by
                  simp [A, B]
      rw [hD_pair]
      exact int_dvd_r_mul_two_mul_add_one_odd_comb r (pairSet r k)
        (fun i hi => pairSet_subset_le hi) (pairSet_symm r k hk_mem)
        (card_pairSet_odd_of_odd hr hk_mem hk_eq)
  have hsum_dvd : ((r * (2 * r + 1) : ℕ) : ℤ) ∣
      ∑ k ∈ Finset.Icc 1 r, (D k + D (r + 1 - k)) :=
    Finset.dvd_sum hpair_dvd
  have h2_dvd : ((r * (2 * r + 1) : ℕ) : ℤ) ∣ 2 * ((cN r : ℤ) - (hN r : ℤ)) := by
    simpa [h2D] using hsum_dvd
  have hOdd_r : Odd r := by
    refine ⟨r / 2, ?_⟩
    have hdiv := Nat.div_add_mod r 2
    omega
  have hodd : Odd (r * (2 * r + 1)) := hOdd_r.mul (odd_two_mul_add_one r)
  have hcop_nat : Nat.Coprime (r * (2 * r + 1)) 2 := hodd.coprime_two_right
  have hcop : IsCoprime ((r * (2 * r + 1) : ℕ) : ℤ) (2 : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    rw [Int.gcd_def, Int.natAbs_natCast]
    norm_num
    exact hodd
  exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using h2_dvd)

/-! ## Lemma 3: the even four-factor numerator over `ℤ` -/

private lemma sum_Icc_one_eq_sum_lower_pair (r : ℕ) (hr : r % 2 = 0) (f : ℕ → ℤ) :
    (∑ k ∈ Finset.Icc 1 r, f k) =
      ∑ k ∈ Finset.Icc 1 (r / 2), (f k + f (r + 1 - k)) := by
  classical
  have hr_eq : r = 2 * (r / 2) := by
    have hdiv := Nat.div_add_mod r 2
    omega
  let lower := Finset.Icc 1 (r / 2)
  let upper := Finset.Icc (r / 2 + 1) r
  have hIcc : Finset.Icc 1 r = lower ∪ upper := by
    ext i
    simp only [lower, upper, Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint lower upper := by
    rw [Finset.disjoint_left]
    intro i hi hu
    rw [Finset.mem_Icc] at hi hu
    omega
  have hsum : (∑ k ∈ Finset.Icc 1 r, f k) =
      (∑ k ∈ lower, f k) + (∑ k ∈ upper, f k) := by
    rw [hIcc, Finset.sum_union hdisj]
  have hupper : (∑ k ∈ upper, f k) = ∑ k ∈ lower, f (r + 1 - k) := by
    refine Finset.sum_bij (fun k hk => r + 1 - k) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k₁ hk₁ k₂ hk₂ h
      rw [Finset.mem_Icc] at hk₁ hk₂
      omega
    · intro j hj
      rw [Finset.mem_Icc] at hj
      refine ⟨r + 1 - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro k hk
      congr 1
      rw [Finset.mem_Icc] at hk
      omega
  calc
    (∑ k ∈ Finset.Icc 1 r, f k) = (∑ k ∈ lower, f k) + (∑ k ∈ upper, f k) := hsum
    _ = (∑ k ∈ lower, f k) + (∑ k ∈ lower, f (r + 1 - k)) := by rw [hupper]
    _ = ∑ k ∈ lower, (f k + f (r + 1 - k)) := by rw [Finset.sum_add_distrib]

lemma even_numerator_dvd_int (r : ℕ) (hr1 : 1 ≤ r) (hr : r % 2 = 0) :
    ((r * (r + 1) * (2 * r + 1) * (3 * r + 1) : ℕ) : ℤ) ∣
      (((r + 1 : ℕ) : ℤ) * (cN r : ℤ) - ((3 * r + 1 : ℕ) : ℤ) * (hN r : ℤ)) := by
  classical
  let f : ℕ → ℤ := fun k =>
    ((r + 1 : ℕ) : ℤ) * (cTerm r (r + k) : ℤ) - ((3 * r + 1 : ℕ) : ℤ) * (hTerm r k : ℤ)
  have hNsum : (((r + 1 : ℕ) : ℤ) * (cN r : ℤ) - ((3 * r + 1 : ℕ) : ℤ) * (hN r : ℤ)) =
      ∑ k ∈ Finset.Icc 1 r, f k := by
    calc
      ((r + 1 : ℕ) : ℤ) * (cN r : ℤ) - ((3 * r + 1 : ℕ) : ℤ) * (hN r : ℤ)
          = ((r + 1 : ℕ) : ℤ) * (∑ k ∈ Finset.Icc 1 r, (cTerm r (r + k) : ℤ)) -
            ((3 * r + 1 : ℕ) : ℤ) * (∑ k ∈ Finset.Icc 1 r, (hTerm r k : ℤ)) := by
              rw [cN_eq_sum_cTerm_Icc_one, hN_eq_sum_hTerm]
              simp [Nat.cast_sum]
      _ = ∑ k ∈ Finset.Icc 1 r, f k := by
              simp [f, Finset.mul_sum, Finset.sum_sub_distrib]
  have hNpair : (((r + 1 : ℕ) : ℤ) * (cN r : ℤ) - ((3 * r + 1 : ℕ) : ℤ) * (hN r : ℤ)) =
      ∑ k ∈ Finset.Icc 1 (r / 2), (f k + f (r + 1 - k)) := by
    rw [hNsum]
    exact sum_Icc_one_eq_sum_lower_pair r hr f
  have hpair_dvd : ∀ k ∈ Finset.Icc 1 (r / 2),
      ((r * (r + 1) * (2 * r + 1) * (3 * r + 1) : ℕ) : ℤ) ∣
        (f k + f (r + 1 - k)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_full : k ∈ Finset.Icc 1 r := by
      rw [Finset.mem_Icc]
      omega
    have hk_ne : k ≠ r + 1 - k := by
      intro h
      have h2k : 2 * k = r + 1 := by omega
      have hr_eq : r = 2 * (r / 2) := by
        have hdiv := Nat.div_add_mod r 2
        omega
      omega
    have hc_pair := cTerm_pair_eq r k hk_full hk_ne
    have hh_pair := hTerm_pair_eq r k hk_full hk_ne
    have hc_cast : ((cTerm r (r + k) + cTerm r (r + (r + 1 - k)) : ℕ) : ℤ) =
        ((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) := by
      rw [hc_pair]
      simp [Nat.cast_prod]
    have hh_cast : ((hTerm r k + hTerm r (r + 1 - k) : ℕ) : ℤ) =
        ((r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, (i : ℤ)) := by
      rw [hh_pair]
      simp [Nat.cast_prod]
    have hc_sum : (cTerm r (r + k) : ℤ) + (cTerm r (r + (r + 1 - k)) : ℤ) =
        ((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) := by
      rw [← Nat.cast_add, hc_pair]
      simp [Nat.cast_prod]
    have hh_sum : (hTerm r k : ℤ) + (hTerm r (r + 1 - k) : ℤ) =
        ((r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, (i : ℤ)) := by
      rw [← Nat.cast_add, hh_pair]
      simp [Nat.cast_prod]
    have hf_pair : f k + f (r + 1 - k) =
        (((r + 1) * (3 * r + 1) : ℕ) : ℤ) *
          ((∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) - (∏ i ∈ pairSet r k, (i : ℤ))) := by
      calc
        f k + f (r + 1 - k)
            = ((r + 1 : ℕ) : ℤ) *
                ((cTerm r (r + k) : ℤ) + (cTerm r (r + (r + 1 - k)) : ℤ)) -
              ((3 * r + 1 : ℕ) : ℤ) *
                ((hTerm r k : ℤ) + (hTerm r (r + 1 - k) : ℤ)) := by
                  dsimp [f]; ring
        _ = ((r + 1 : ℕ) : ℤ) *
              (((3 * r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ))) -
            ((3 * r + 1 : ℕ) : ℤ) *
              (((r + 1 : ℕ) : ℤ) * (∏ i ∈ pairSet r k, (i : ℤ))) := by
                  rw [hc_sum, hh_sum]
        _ = (((r + 1) * (3 * r + 1) : ℕ) : ℤ) *
              ((∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) -
                (∏ i ∈ pairSet r k, (i : ℤ))) := by
                  norm_num [Nat.cast_mul]
                  ring
    have hprod_dvd : ((r * (2 * r + 1) : ℕ) : ℤ) ∣
        ((∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) - (∏ i ∈ pairSet r k, (i : ℤ))) :=
      int_dvd_r_mul_two_mul_add_one_prod_sub r (pairSet r k)
        (fun i hi => pairSet_subset_le hi) (pairSet_symm r k hk_full)
        (card_pairSet_even_of_even hr hk_full hk_ne)
    have hmul_dvd : (((r + 1) * (3 * r + 1) : ℕ) : ℤ) * ((r * (2 * r + 1) : ℕ) : ℤ) ∣
        (((r + 1) * (3 * r + 1) : ℕ) : ℤ) *
          ((∏ i ∈ pairSet r k, ((r + i : ℕ) : ℤ)) - (∏ i ∈ pairSet r k, (i : ℤ))) :=
      mul_dvd_mul_left (((r + 1) * (3 * r + 1) : ℕ) : ℤ) hprod_dvd
    have hF : ((r * (r + 1) * (2 * r + 1) * (3 * r + 1) : ℕ) : ℤ) =
        (((r + 1) * (3 * r + 1) : ℕ) : ℤ) * ((r * (2 * r + 1) : ℕ) : ℤ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [hf_pair]
    simpa [hF] using hmul_dvd
  have hsum_dvd : ((r * (r + 1) * (2 * r + 1) * (3 * r + 1) : ℕ) : ℤ) ∣
      ∑ k ∈ Finset.Icc 1 (r / 2), (f k + f (r + 1 - k)) :=
    Finset.dvd_sum hpair_dvd
  rw [hNpair]
  exact hsum_dvd

end

end Erdos291
