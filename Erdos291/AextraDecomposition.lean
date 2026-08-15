import Erdos291.BadDensity
import Erdos291.SymmetryOrbits
import Erdos291.SecondMoment
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Erdős #291 — decomposition of `Aextra` into a main term and an exceptional term

For a fixed `D ≥ 1`, every prime `p` not dividing the fixed nonzero integer `Nall D`
contributes at most `2 / D + 2 / (p - 1)` to `Aextra`.  Summing over primes `p ≤ x`
therefore gives

`Aextra x ≤ (2 / D) * π x + 2 * Σ_{p ≤ x} 1 / (p - 1) + (exceptional sum)`.

The exceptional sum is finite and uniformly bounded by `(Nall D) / 2`, which yields the
fixed-`D` asymptotic

`Aextra x ≤ (2 / D) * π x + C * (1 + log (log x))`.

There are no unproved declarations in this file.
-/

set_option linter.style.haveILetI false

open scoped BigOperators
open Filter

namespace Erdos291

/-! ## The exact decomposition with the exceptional sum retained -/

/-- The exact bound for a fixed `D` with `Nall D` as the exceptional integer. -/
private lemma Aextra_le_two_div_D_pi_add_exceptional_Nall (D x : ℕ) (hD : 1 ≤ D) :
    Aextra x ≤
      (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ)
      + 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
          1 / ((p - 1 : ℕ) : ℝ))
      + (∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ Nall D),
          ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  let S : Finset ℕ := (Finset.Icc 2 x).filter Nat.Prime
  let exc : Finset ℕ := S.filter (fun p => p ∣ Nall D)
  let good : Finset ℕ := S.filter (fun p => ¬ p ∣ Nall D)
  let f : ℕ → ℝ := fun p => ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)
  have hDpos : 0 < D := by omega
  have hDposR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDposR
  -- Per-prime bound for the good primes.
  have hterm_good : ∀ p ∈ good, f p ≤ 2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ) := by
    intro p hp
    dsimp [good, S] at hp
    have hpS : p ∈ (Finset.Icc 2 x).filter Nat.Prime := (Finset.mem_filter.mp hp).1
    have hnot : ¬ p ∣ Nall D := (Finset.mem_filter.mp hp).2
    have hp' : Nat.Prime p := (Finset.mem_filter.mp hpS).2
    haveI : Fact p.Prime := ⟨hp'⟩
    have hT_le_E : (T p).card ≤ (E p).card := by
      simpa [T] using Finset.card_filter_le (E p) (fun r => 2 * r < p - 1)
    have hcardE := E_card_le_two_mul_div_add_two p D hDpos hnot
    have hn_pos : 0 < (p - 1 : ℕ) := by
      have hp2 : 2 ≤ p := hp'.two_le
      omega
    have hn_posR : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hn_pos
    have hn_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn_posR
    have hcardR : ((T p).card : ℝ) ≤ 2 * (((p - 1) / D + 1 : ℕ) : ℝ) := by
      exact_mod_cast (le_trans hT_le_E hcardE)
    have hdivD : (((p - 1) / D : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) / (D : ℝ) := Nat.cast_div_le
    have hnat_le : (((p - 1) / D + 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) / (D : ℝ) + 1 := by
      have h1 : (((p - 1) / D + 1 : ℕ) : ℝ) = (((p - 1) / D : ℕ) : ℝ) + 1 := by norm_num
      rw [h1]
      linarith [hdivD]
    dsimp [f]
    calc
      ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
          (2 * (((p - 1) / D + 1 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hcardR (le_of_lt hn_posR)
      _ ≤ (2 * (((p - 1 : ℕ) : ℝ) / (D : ℝ) + 1)) / ((p - 1 : ℕ) : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hn_posR)
          exact mul_le_mul_of_nonneg_left hnat_le (by norm_num)
      _ = 2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ) := by
          field_simp [hn_ne, hDne]
  -- Sum the per-prime bound over the good primes.
  have hgood_sum :
      (∑ p ∈ good, f p) ≤
        (2 / (D : ℝ)) * (good.card : ℝ) + 2 * (∑ p ∈ good, 1 / ((p - 1 : ℕ) : ℝ)) := by
    calc
      (∑ p ∈ good, f p) ≤ ∑ p ∈ good, (2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro p hp
        exact hterm_good p hp
      _ = (∑ p ∈ good, (2 / (D : ℝ))) + ∑ p ∈ good, 2 / ((p - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib]
      _ = (2 / (D : ℝ)) * (good.card : ℝ) + 2 * (∑ p ∈ good, 1 / ((p - 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_comm]
  -- The good primes are at most all primes `≤ x`.
  have hgood_card_nat : good.card ≤ Nat.primeCounting x := by
    have hsub : good ⊆ S := by
      intro p hp
      dsimp [good] at hp
      exact (Finset.mem_filter.mp hp).1
    have hS_card : S.card = Nat.primeCounting x := by
      dsimp [S]
      rw [← Nat.primesLE_eq_filter_Icc_two x, Nat.primesLE_card_eq_primeCounting]
    exact le_trans (Finset.card_le_card hsub) (le_of_eq hS_card)
  have hgood_card_R : (good.card : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
    exact_mod_cast hgood_card_nat
  have hcoef_nonneg : 0 ≤ 2 / (D : ℝ) := by
    exact div_nonneg (by norm_num) (le_of_lt hDposR)
  have hmul_good_card :
      (2 / (D : ℝ)) * (good.card : ℝ) ≤ (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ) :=
    mul_le_mul_of_nonneg_left hgood_card_R hcoef_nonneg
  -- The reciprocal sum over the good primes is bounded by the full reciprocal sum.
  have hgood_recip_le :
      (∑ p ∈ good, 1 / ((p - 1 : ℕ) : ℝ)) ≤
        (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      dsimp [good] at hp
      exact (Finset.mem_filter.mp hp).1
    · intro p _ _
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg (p - 1 : ℕ))
  -- Total contribution of the good primes.
  have hgood_total :
      (∑ p ∈ good, f p) ≤
        (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ)
          + 2 * (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) := by
    calc
      (∑ p ∈ good, f p) ≤
          (2 / (D : ℝ)) * (good.card : ℝ) + 2 * (∑ p ∈ good, 1 / ((p - 1 : ℕ) : ℝ)) :=
        hgood_sum
      _ ≤ (2 / (D : ℝ)) * (good.card : ℝ) + 2 * (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hgood_recip_le (by norm_num)) _
      _ ≤ (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ)
            + 2 * (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) := by
        exact add_le_add_left hmul_good_card _
  -- Split the total sum into exceptional and good parts.
  have hsplit :
      (∑ p ∈ exc, f p) + (∑ p ∈ good, f p) = ∑ p ∈ S, f p := by
    simpa [exc, good, S] using
      (Finset.sum_filter_add_sum_filter_not (s := S) (p := fun p => p ∣ Nall D) (f := f))
  have hsum_eq : Aextra x = (∑ p ∈ exc, f p) + (∑ p ∈ good, f p) := by
    unfold Aextra
    change (∑ p ∈ S, f p) = (∑ p ∈ exc, f p) + (∑ p ∈ good, f p)
    rw [← hsplit]
  have hexc_eq : exc = (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ Nall D) := by
    dsimp [exc, S]
    rw [Finset.filter_filter]
  rw [hsum_eq]
  rw [← hexc_eq]
  linarith [hgood_total]

/-- Lemma 9, first statement: the `Aextra` decomposition with an explicit exceptional sum. -/
theorem Aextra_le_two_div_D_pi_add_exceptional (D x : ℕ) (hD : 1 ≤ D) :
    ∃ N : ℕ, N ≠ 0 ∧
      Aextra x ≤
        (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ)
        + 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
            1 / ((p - 1 : ℕ) : ℝ))
        + (∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ N),
            ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
  refine ⟨Nall D, Nall_ne_zero D, ?_⟩
  exact Aextra_le_two_div_D_pi_add_exceptional_Nall D x hD

/-! ## The fixed-`D` asymptotic form -/

/-- Lemma 9, second statement: for fixed `D`, the main term is `(2 / D) * π x` and the
rest is `O(1 + log log x)`. -/
theorem Aextra_le_of_fixed_D (D : ℕ) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      Aextra x ≤
        (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ)
        + C * (1 + Real.log (Real.log (x : ℝ))) := by
  rcases sum_inv_pred_le_loglog with ⟨C₀, hC₀pos, hC₀⟩
  have hNne : Nall D ≠ 0 := Nall_ne_zero D
  have hNpos : 0 < Nall D := Nat.pos_of_ne_zero hNne
  -- The exceptional sum is uniformly bounded by `(Nall D) / 2`.
  have hexc_le (x : ℕ) :
      (∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ Nall D),
          ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤ (Nall D : ℝ) / 2 := by
    let s : Finset ℕ := (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ Nall D)
    change (∑ p ∈ s, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤ (Nall D : ℝ) / 2
    have hterm : ∀ p ∈ s, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 1 / 2 := by
      intro p hp
      have hp_main : Nat.Prime p ∧ p ∣ Nall D := (Finset.mem_filter.mp hp).2
      have hp' : Nat.Prime p := hp_main.1
      have hp2 : 2 ≤ p := hp'.two_le
      have hden_nat : 0 < (p - 1 : ℕ) := by omega
      have hdenR : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hden_nat
      have hT_le_E : (T p).card ≤ (E p).card := by
        simpa [T] using Finset.card_filter_le (E p) (fun r => 2 * r < p - 1)
      have hcardR : ((T p).card : ℝ) ≤ ((E p).card : ℝ) := by exact_mod_cast hT_le_E
      have hf_le_E :
          ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
            ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hcardR (le_of_lt hdenR)
      have hcR : (c p : ℝ) = ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := by
        unfold c
        push_cast
        rw [Nat.cast_sub hp'.one_le]
        norm_num
      calc
        ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
            ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := hf_le_E
        _ = (c p : ℝ) := hcR.symm
        _ ≤ 1 / 2 := c_le_one_half p hp'
    have hsum_le :
        (∑ p ∈ s, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤ ∑ p ∈ s, (1 / 2 : ℝ) := by
      exact Finset.sum_le_sum hterm
    have hcard_nat : s.card ≤ Nall D := by
      have hsub : s ⊆ Finset.Icc 1 (Nall D) := by
        intro p hp
        rw [Finset.mem_Icc]
        have hp_main : Nat.Prime p ∧ p ∣ Nall D := (Finset.mem_filter.mp hp).2
        exact ⟨Nat.Prime.one_le hp_main.1, Nat.le_of_dvd hNpos hp_main.2⟩
      have hcardIcc : (Finset.Icc 1 (Nall D)).card = Nall D := by
        rw [Nat.card_Icc]
        omega
      exact le_trans (Finset.card_le_card hsub) (le_of_eq hcardIcc)
    have hcardR : (s.card : ℝ) ≤ (Nall D : ℝ) := by exact_mod_cast hcard_nat
    calc
      (∑ p ∈ s, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) ≤ ∑ p ∈ s, (1 / 2 : ℝ) := hsum_le
      _ = (s.card : ℝ) / 2 := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul]
        ring
      _ ≤ (Nall D : ℝ) / 2 := by
        exact div_le_div_of_nonneg_right hcardR (by norm_num)
  -- Main bound with the exceptional sum replaced by its uniform bound.
  have hmain (x : ℕ) :
      Aextra x ≤
        (2 / (D : ℝ)) * (Nat.primeCounting x : ℝ)
          + 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              1 / ((p - 1 : ℕ) : ℝ))
          + (Nall D : ℝ) / 2 := by
    have h := Aextra_le_two_div_D_pi_add_exceptional_Nall D x hD
    have hexc := hexc_le x
    nlinarith
  -- Eventually `0 ≤ log (log x)`, i.e. `1 ≤ 1 + log (log x)`.
  have h_eventually_one : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ 1 + Real.log (Real.log (x : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with x hx
    have hxRpos : 0 < (x : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hx)
    have hlogx_gt_one : (1 : ℝ) < Real.log (x : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hxRpos]
      have h3xR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
      exact lt_of_lt_of_le Real.exp_one_lt_three h3xR
    have hll_nonneg : 0 ≤ Real.log (Real.log (x : ℝ)) :=
      le_of_lt (Real.log_pos hlogx_gt_one)
    linarith
  let C : ℝ := 2 * C₀ + (Nall D : ℝ) / 2 + 1
  have hCpos : 0 < C := by
    dsimp [C]
    have hNhalf_nonneg : 0 ≤ (Nall D : ℝ) / 2 := by
      exact div_nonneg (by exact_mod_cast Nat.zero_le (Nall D)) (by norm_num)
    linarith
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC₀, h_eventually_one] with x hxSum hxOne
  have hmainx := hmain x
  have hL : 0 ≤ Real.log (Real.log (x : ℝ)) := by linarith [hxOne]
  have hNhalf_nonneg : 0 ≤ (Nall D : ℝ) / 2 := by
    exact div_nonneg (by exact_mod_cast Nat.zero_le (Nall D)) (by norm_num)
  have hNL : 0 ≤ ((Nall D : ℝ) / 2) * Real.log (Real.log (x : ℝ)) :=
    mul_nonneg hNhalf_nonneg hL
  dsimp [C]
  nlinarith [hmainx, hxSum, hxOne, hNL, hC₀pos]

end Erdos291
