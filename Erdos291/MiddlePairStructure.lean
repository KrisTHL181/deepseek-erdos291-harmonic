import Erdos291.WmidBound
import Erdos291.OddHarmonicWalk
import Erdos291.Eisenstein
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Erdős #291 — elementary congruence structure of middle pairs

A *middle pair* is a pair `(r, p)` with `2r + 1 < p`, `r ∈ E p` (so
`p ∣ num H_r`).  This file records the elementary congruences such pairs
force:

1. the Fermat quotient `q_p(2)` equals the odd-harmonic walk at half the gap
   `t = (p - 1 - 2r) / 2`;
2. the harmonic identity
   `H_r = 2·H_{2r} - H_t - 2·q_p(2)` in `ZMod p`;
3. gap-2 middle pairs (`p = 2r + 3`) force `q_p(2) = 1`;
4. quarter middle pairs (`p = 4r + 1`) force `q_p(2) = 0` (Wieferich);
5. the gap `p - 1 - 2r` is coprime to the shifted row `2r + 1`.

Numeric support: a C scan verified all 3029 middle pairs with `p ≤ 200000`.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The harmonic sum `H_n = ∑_{j=1}^n j⁻¹` in `ZMod p`. -/
noncomputable def harmonicSum (p n : ℕ) : ZMod p :=
  ∑ j ∈ Finset.Icc 1 n, ((j : ZMod p)⁻¹)

lemma harmonicSum_eq_sum_inv (p n : ℕ) : harmonicSum p n =
    ∑ j ∈ Finset.Icc 1 n, ((j : ZMod p)⁻¹) := rfl

/-- A middle pair has vanishing row sum `H_r = 0` in `ZMod p`. -/
lemma harmonicSum_middle_pair_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hrp : r < p) : harmonicSum p r = 0 := by
  have hdvd : (p : ℤ) ∣ (harmonic r).num := by
    rw [E] at hrE
    exact (Finset.mem_filter.mp hrE).2
  exact (num_dvd_iff_sum_inv_zero p r hrp).mp hdvd

/-! ## The shifted row is coprime to the gap -/

/-- A common divisor of `p - 1 - 2r` and `2r + 1` divides their sum `p`;
as the gap is `< p` and `p` is prime, the gcd is `1`. -/
lemma middle_gap_coprime_shifted_row (p r : ℕ) (hp : Nat.Prime p) (hmid : 2 * r + 1 < p) :
    Nat.Coprime (p - 1 - 2 * r) (2 * r + 1) := by
  have hgap : 0 < p - 1 - 2 * r := by omega
  have hdvd_sum : Nat.gcd (p - 1 - 2 * r) (2 * r + 1) ∣ p := by
    have h1 : Nat.gcd (p - 1 - 2 * r) (2 * r + 1) ∣ p - 1 - 2 * r := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (p - 1 - 2 * r) (2 * r + 1) ∣ 2 * r + 1 := Nat.gcd_dvd_right _ _
    have hs : Nat.gcd (p - 1 - 2 * r) (2 * r + 1) ∣ (p - 1 - 2 * r) + (2 * r + 1) :=
      Nat.dvd_add h1 h2
    have hsum : (p - 1 - 2 * r) + (2 * r + 1) = p := by omega
    simpa [hsum] using hs
  have hdvd_eq : Nat.gcd (p - 1 - 2 * r) (2 * r + 1) = 1 ∨
      Nat.gcd (p - 1 - 2 * r) (2 * r + 1) = p := by
    exact (Nat.dvd_prime hp).mp hdvd_sum
  rcases hdvd_eq with h1 | hpe
  · exact h1
  · have hle : Nat.gcd (p - 1 - 2 * r) (2 * r + 1) ≤ p - 1 - 2 * r :=
      Nat.le_of_dvd hgap (Nat.gcd_dvd_left _ _)
    rw [hpe] at hle
    omega

/-! ## The Fermat quotient equals the walk at half the gap -/

/-- For a middle pair, `q_p(2) = oddWalk p ((p - 1 - 2r) / 2)`. -/
lemma fermatQuotient_eq_oddWalk_of_middle_pair (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    (fermatQuotient p : ZMod p) = oddWalk p ((p - 1 - 2 * r) / 2) := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  rcases hodd with ⟨m, hm⟩
  have hpm : p = 2 * m + 1 := by omega
  have hmdiv : (p - 1) / 2 = m := by omega
  have h1r : 1 ≤ r := by
    rw [E] at hrE
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).1
  have hrle : r ≤ (p - 1) / 2 := by
    rw [hmdiv]
    omega
  have hwalk := (mem_E_iff_oddWalk_eq p r hp h1r hrle).mp hrE
  have ht_eq : (p - 1 - 2 * r) / 2 = m - r := by
    have h2 : 2 * (m - r) = p - 1 - 2 * r := by omega
    rw [← h2]
    exact Nat.mul_div_right (m - r) (by norm_num : 0 < 2)
  calc
    (fermatQuotient p : ZMod p) = oddWalk p ((p - 1) / 2) :=
      (oddWalk_mid_eq_fermatQuotient p hp).symm
    _ = oddWalk p ((p - 1) / 2 - r) := hwalk.symm
    _ = oddWalk p ((p - 1 - 2 * r) / 2) := by
      rw [hmdiv, ← ht_eq]

/-! ## The harmonic identity of a middle pair -/

/-- For a middle pair, `H_r = 2·H_{2r} - H_t - 2·q_p(2)` in `ZMod p`, where
`t = (p - 1 - 2r) / 2`. -/
lemma harmonicSum_middle_pair_identity (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    harmonicSum p r = 2 * harmonicSum p (2 * r)
      - harmonicSum p ((p - 1 - 2 * r) / 2) - 2 * (fermatQuotient p : ZMod p) := by
  let H : ℕ → ZMod p := fun n => harmonicSum p n
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  rcases hodd with ⟨m, hm⟩
  have hpm : p = 2 * m + 1 := by omega
  have hmdiv : (p - 1) / 2 = m := by omega
  have h1r : 1 ≤ r := by
    rw [E] at hrE
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).1
  have hrp : r < p := by omega
  have hHr0 : H r = 0 := by
    dsimp [H]
    exact harmonicSum_middle_pair_zero p r hrE hrp
  let t : ℕ := (p - 1 - 2 * r) / 2
  have ht2 : 2 * t = p - 1 - 2 * r := by
    have h2div : 2 ∣ p - 1 - 2 * r := by
      use m - r
      omega
    have hmul : 2 * ((p - 1 - 2 * r) / 2) = p - 1 - 2 * r := Nat.mul_div_cancel' h2div
    simpa [t] using hmul
  have h2r_le_pred : 2 * r ≤ p - 1 := by omega
  have hpair : H (2 * r) = H (2 * t) := by
    have h := sum_inv_Icc_sub_eq_sum_inv p (2 * r) hp h2r_le_pred
    have h' : H (2 * t) = H (2 * r) := by
      dsimp [H]
      simpa [harmonicSum, ht2] using h
    exact h'.symm
  have heven_split : ∀ n : ℕ, H (2 * n) = oddWalk p n + (2 : ZMod p)⁻¹ * H n := by
    intro n
    have hsplit := sum_Icc_one_mul_two n (fun j => ((j : ZMod p)⁻¹))
    have heven : (∑ i ∈ Finset.Icc 1 n, ((2 * i : ℕ) : ZMod p)⁻¹) =
        (2 : ZMod p)⁻¹ * (∑ i ∈ Finset.Icc 1 n, ((i : ℕ) : ZMod p)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.cast_mul, mul_inv_rev, mul_comm]
      simp
    dsimp [H, harmonicSum]
    rw [hsplit, oddWalk, heven]
  have hq_t : oddWalk p t = (fermatQuotient p : ZMod p) := by
    dsimp [t]
    exact (fermatQuotient_eq_oddWalk_of_middle_pair p r hp hrE hmid).symm
  calc
    H r = 0 := hHr0
    _ = 2 * H (2 * r) - H t - 2 * (fermatQuotient p : ZMod p) := by
      rw [hpair, heven_split t, hq_t]
      have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
        rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
        exact two_isUnit p hp
      rw [mul_add, ← mul_assoc, htwo, one_mul]
      ring

/-! ## Gap-2 and quarter middle pairs -/

/-- A gap-2 middle pair forces `q_p(2) = 1`. -/
lemma fermatQuotient_eq_one_of_middle_pair_gap_two (p r : ℕ) [Fact p.Prime]
    (hp : 3 ≤ p) (hrE : r ∈ E p) (hgap : p = 2 * r + 3) :
    (fermatQuotient p : ZMod p) = 1 := by
  have hmid : 2 * r + 1 < p := by omega
  have h := fermatQuotient_eq_oddWalk_of_middle_pair p r hp hrE hmid
  have ht : (p - 1 - 2 * r) / 2 = 1 := by
    have h2 : 2 * 1 = p - 1 - 2 * r := by omega
    rw [← h2]
  rw [h, ht]
  simp [oddWalk]

/-- A quarter middle pair (`p = 4r + 1`) forces `q_p(2) = 0`: the middle digit is
bad exactly for Wieferich primes. -/
lemma fermatQuotient_eq_zero_of_middle_pair_quarter (p r : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hrE : r ∈ E p) (hquarter : p = 4 * r + 1) :
    (fermatQuotient p : ZMod p) = 0 := by
  have hp3 : 3 ≤ p := by omega
  have hmid : 2 * r + 1 < p := by omega
  have h1r : 1 ≤ r := by
    rw [E] at hrE
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).1
  have hrp : r < p := by omega
  have hq : (fermatQuotient p : ZMod p) = oddWalk p r := by
    have h := fermatQuotient_eq_oddWalk_of_middle_pair p r hp3 hrE hmid
    have ht : (p - 1 - 2 * r) / 2 = r := by
      have h2 : 2 * r = p - 1 - 2 * r := by omega
      rw [← h2]
      exact Nat.mul_div_right r (by norm_num : 0 < 2)
    rwa [ht] at h
  have hHr0 : harmonicSum p r = 0 := harmonicSum_middle_pair_zero p r hrE hrp
  have hsplit_r : harmonicSum p (2 * r) = oddWalk p r + (2 : ZMod p)⁻¹ * harmonicSum p r := by
    have hsplit := sum_Icc_one_mul_two r (fun j => ((j : ZMod p)⁻¹))
    have heven : (∑ i ∈ Finset.Icc 1 r, ((2 * i : ℕ) : ZMod p)⁻¹) =
        (2 : ZMod p)⁻¹ * (∑ i ∈ Finset.Icc 1 r, ((i : ℕ) : ZMod p)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Nat.cast_mul, mul_inv_rev, mul_comm]
      simp
    dsimp [harmonicSum]
    rw [hsplit, oddWalk, heven]
  have hH2r : harmonicSum p (2 * r) = harmonicSum p ((p - 1) / 2) := by
    have hquarter' : (p - 1) / 2 = 2 * r := by
      have h2 : 2 * (2 * r) = p - 1 := by omega
      rw [← h2]
      exact Nat.mul_div_right (2 * r) (by norm_num : 0 < 2)
    rw [hquarter']
  have hEis' : harmonicSum p ((p - 1) / 2) = -(2 : ZMod p) * (fermatQuotient p : ZMod p) := by
    simpa [harmonicSum] using eisenstein_congruence p hp3
  have hq_neg : oddWalk p r = -(2 : ZMod p) * (fermatQuotient p : ZMod p) := by
    rw [hH2r] at hsplit_r
    rw [hEis'] at hsplit_r
    rw [hHr0] at hsplit_r
    simpa using hsplit_r.symm
  have hq_eq : (fermatQuotient p : ZMod p) = -(2 : ZMod p) * (fermatQuotient p : ZMod p) := by
    nth_rewrite 1 [hq]
    rw [hq_neg]
  have hq3 : (3 : ZMod p) * (fermatQuotient p : ZMod p) = 0 := by
    rw [show (3 : ZMod p) * (fermatQuotient p : ZMod p) =
        (fermatQuotient p : ZMod p) + 2 * (fermatQuotient p : ZMod p) by ring]
    calc
      (fermatQuotient p : ZMod p) + 2 * (fermatQuotient p : ZMod p)
          = -(2 : ZMod p) * (fermatQuotient p : ZMod p) + 2 * (fermatQuotient p : ZMod p) := by
              nth_rewrite 1 [hq_eq]
              rfl
      _ = 0 := by ring
  have h3unit : IsUnit (3 : ZMod p) := by
    rw [isUnit_iff_ne_zero]
    intro h
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  rcases mul_eq_zero.mp hq3 with h3 | hq0
  · exfalso
    exact h3unit.ne_zero h3
  · exact hq0

end

end Erdos291
