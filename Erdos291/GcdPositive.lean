import Erdos291.Characterization
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős #291 — the `gcd > 1` direction

We prove that `gcd(a_n, L_n) > 1` for infinitely many `n`, namely for `n = 2 · 3^(e+1)`.
This is the direction of #291 that is fully resolved; the `gcd = 1` direction is the
open Shiu (2016) conjecture.

The key input is the characterization `dvd_a_iff_sum_inv_eq_zero`: for `n = 2 · 3^(e+1)`
we have `log₃ n = e + 1` and the leading base-3 digit is `2`, so

    3 ∣ a n  ⟺  ∑_{j=1}^2 j⁻¹ = 0 in ZMod 3,

and `1 + 1/2 = 3/2 ≡ 0 (mod 3)`, whence `3 ∣ gcd(a_n, L_n)`.
-/

open scoped BigOperators

namespace Erdos291

open Nat

/-- `Nat.log 3 (2 · 3^e) = e`. -/
lemma log_three_two_mul_pow (e : ℕ) : Nat.log 3 (2 * 3 ^ e) = e := by
  rw [Nat.log_eq_iff]
  · constructor
    · simp
    · have h : 2 * 3 ^ e < 3 ^ e * 3 := by
        simp [mul_comm]
      simpa [pow_succ] using h
  · right
    exact ⟨by norm_num, by positivity⟩

/-- `∑_{j=1}^2 j⁻¹ = 0` in `ZMod 3`. -/
lemma sum_inv_Icc_one_two_three : (∑ j ∈ Finset.Icc (1 : ℕ) (2 : ℕ), ((j : ZMod 3)⁻¹)) = 0 := by
  native_decide

/-- `3 ∣ gcd(a_{2·3^(e+1)}, L_{2·3^(e+1)})`, so `gcd > 1` for the infinite family `2·3^(e+1)`. -/
theorem three_dvd_gcd_two_mul_pow_three (e : ℕ) :
    3 ∣ Nat.gcd (a (2 * 3 ^ (e + 1))) (L (2 * 3 ^ (e + 1))) := by
  have h3le : 3 ≤ 2 * 3 ^ (e + 1) := by
    calc
      3 ≤ 3 ^ (e + 1) := Nat.le_self_pow (Nat.succ_ne_zero e) 3
      _ ≤ 2 * 3 ^ (e + 1) := by
        simp
  have h3a : 3 ∣ a (2 * 3 ^ (e + 1)) := by
    rw [dvd_a_iff_sum_inv_eq_zero 3 (2 * 3 ^ (e + 1)) h3le]
    have hlog : Nat.log 3 (2 * 3 ^ (e + 1)) = e + 1 := log_three_two_mul_pow (e + 1)
    have hdiv : (2 * 3 ^ (e + 1)) / 3 ^ (e + 1) = 2 := by
      simp
    simpa [hlog, hdiv] using sum_inv_Icc_one_two_three
  have h3L : 3 ∣ L (2 * 3 ^ (e + 1)) :=
    dvd_L_of_mem_Icc (2 * 3 ^ (e + 1)) 3 (by
      rw [Finset.mem_Icc]
      exact ⟨by norm_num, h3le⟩)
  exact Nat.dvd_gcd h3a h3L

/-- `gcd (a n) (L n) > 1` for infinitely many `n`, witnessed by the family `n = 2 · 3^(e+1)`. -/
theorem gcd_gt_one_infinitely_often :
    Set.Infinite {n : ℕ | 1 < Nat.gcd (a n) (L n)} := by
  let f : ℕ → ℕ := fun e => 2 * 3 ^ (e + 1)
  have hf_inj : Function.Injective f := by
    intro e₁ e₂ h
    have hpow : 3 ^ (e₁ + 1) = 3 ^ (e₂ + 1) :=
      Nat.mul_left_cancel (by norm_num : 0 < 2) h
    have hsucc : e₁ + 1 = e₂ + 1 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
    omega
  have hmem : ∀ e : ℕ, f e ∈ {n : ℕ | 1 < Nat.gcd (a n) (L n)} := by
    intro e
    have h3 : 3 ∣ Nat.gcd (a (2 * 3 ^ (e + 1))) (L (2 * 3 ^ (e + 1))) :=
      three_dvd_gcd_two_mul_pow_three e
    have h3le : 3 ≤ Nat.gcd (a (2 * 3 ^ (e + 1))) (L (2 * 3 ^ (e + 1))) :=
      Nat.le_of_dvd
        (Nat.gcd_pos_of_pos_right (a (2 * 3 ^ (e + 1))) (L_pos (2 * 3 ^ (e + 1)))) h3
    exact lt_of_lt_of_le (by norm_num : 1 < 3) h3le
  exact Set.infinite_of_injective_forall_mem hf_inj hmem

end Erdos291
