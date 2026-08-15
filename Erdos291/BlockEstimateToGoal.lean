import Erdos291.DyadicBlocks
import Erdos291.SymmetryOrbits
import Erdos291.ProdUnbounded
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-!
# From a uniform dyadic block bound to `Aextra ≤ log / 8` and `xP → ∞`

Assume that for all sufficiently large dyadic block parameters `R` the block
contribution `W R x` is bounded by a constant `C` with `C < log 2 / 8`.  Then
`Aextra x ≤ (1 / 8) * log x` eventually, and consequently `x * prodOneSub x`
tends to `atTop`.
-/

open scoped BigOperators
open scoped Topology
open Filter

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## A crude per-block bound by the Icc-2 Mertens sum -/

private lemma blockGoal_W_le_R_mul_sum_inv_pred (R x : ℕ) :
    W R x ≤ (R : ℝ) *
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) := by
  unfold W
  by_cases hR : R = 0
  · subst R
    have hsum0 : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        ∑ r ∈ (T p).filter (fun r => 0 ≤ r ∧ r < 2 * 0), (1 / ((p - 1 : ℕ) : ℝ))) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro r hr
      have hr0 : r < 0 := (Finset.mem_filter.mp hr).2.2
      omega
    rw [hsum0]
    norm_num
  · have hRge : 1 ≤ R := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hR)
    have hsub : ∀ p, ((T p).filter (fun r => R ≤ r ∧ r < 2 * R)) ⊆ Finset.Icc R (2 * R - 1) := by
      intro p r hr
      rw [Finset.mem_Icc]
      have hrR := (Finset.mem_filter.mp hr).2
      constructor
      · exact hrR.1
      · omega
    have hcard : ∀ p, (((T p).filter (fun r => R ≤ r ∧ r < 2 * R)).card : ℝ) ≤ (R : ℝ) := by
      intro p
      have hc : ((T p).filter (fun r => R ≤ r ∧ r < 2 * R)).card ≤ (Finset.Icc R (2 * R - 1)).card :=
        Finset.card_le_card (hsub p)
      have hcIcc : (Finset.Icc R (2 * R - 1)).card = R := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast (le_trans hc (by rw [hcIcc]))
    have hinner : ∀ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        (∑ r ∈ (T p).filter (fun r => R ≤ r ∧ r < 2 * R), (1 / ((p - 1 : ℕ) : ℝ)))
          ≤ (R : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by
      intro p hp
      let b : ℝ := 1 / ((p - 1 : ℕ) : ℝ)
      have hb : 0 ≤ b := by
        dsimp [b]
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
      calc
        (∑ r ∈ (T p).filter (fun r => R ≤ r ∧ r < 2 * R), (1 / ((p - 1 : ℕ) : ℝ)))
            = ∑ r ∈ (T p).filter (fun r => R ≤ r ∧ r < 2 * R), b := by rfl
        _ = (((T p).filter (fun r => R ≤ r ∧ r < 2 * R)).card : ℝ) * b := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (R : ℝ) * b := mul_le_mul_of_nonneg_right (hcard p) hb
        _ = (R : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by rfl
    calc
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
          ∑ r ∈ (T p).filter (fun r => R ≤ r ∧ r < 2 * R), (1 / ((p - 1 : ℕ) : ℝ)))
          ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              (R : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by
            exact Finset.sum_le_sum (by intro p hp; exact hinner p hp)
      _ = (R : ℝ) * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) := by
            rw [← Finset.mul_sum]

/-! ## Small dyadic blocks: finite geometric sum -/

private def blockGoal_k0 (R0 : ℕ) : ℕ :=
  if R0 = 0 then 0 else Nat.log 2 R0 + 1

private lemma blockGoal_R0_le_two_pow (R0 : ℕ) {k : ℕ} (hk : blockGoal_k0 R0 ≤ k) :
    R0 ≤ 2 ^ k := by
  unfold blockGoal_k0 at hk
  by_cases hR0 : R0 = 0
  · subst R0
    exact Nat.zero_le _
  · have hlog : R0 < 2 ^ (Nat.log 2 R0 + 1) := by
      have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) R0
      simpa [Nat.succ_eq_add_one] using h
    have hk' : Nat.log 2 R0 + 1 ≤ k := by
      simpa [hR0] using hk
    have hpow : 2 ^ (Nat.log 2 R0 + 1) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hk'
    exact le_trans (le_of_lt hlog) hpow

private lemma blockGoal_sum_range_two_pow (n : ℕ) :
    (∑ k ∈ Finset.range n, ((2 ^ k : ℕ) : ℝ)) = ((2 ^ n : ℕ) : ℝ) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsum := Finset.sum_range_succ (fun k : ℕ => ((2 ^ k : ℕ) : ℝ)) n
      have hpow : ((2 ^ n.succ : ℕ) : ℝ) = 2 * ((2 ^ n : ℕ) : ℝ) := by
        rw [pow_succ]
        norm_num
        ring
      calc
        (∑ k ∈ Finset.range n.succ, ((2 ^ k : ℕ) : ℝ))
            = (∑ k ∈ Finset.range n, ((2 ^ k : ℕ) : ℝ)) + ((2 ^ n : ℕ) : ℝ) := by
                  simpa [Nat.succ_eq_add_one] using hsum
        _ = (((2 ^ n : ℕ) : ℝ) - 1) + ((2 ^ n : ℕ) : ℝ) := by rw [ih]
        _ = ((2 ^ n.succ : ℕ) : ℝ) - 1 := by
                  rw [hpow]
                  ring

private lemma blockGoal_two_pow_k0_le_two_mul_R0 (R0 : ℕ) (hR0 : R0 ≠ 0) :
    (2 ^ blockGoal_k0 R0 : ℕ) ≤ 2 * R0 := by
  have hlog : 2 ^ Nat.log 2 R0 ≤ R0 := Nat.pow_log_le_self 2 hR0
  have hmul : 2 * 2 ^ Nat.log 2 R0 ≤ 2 * R0 := Nat.mul_le_mul_left 2 hlog
  have hpow : 2 * 2 ^ Nat.log 2 R0 = 2 ^ (Nat.log 2 R0 + 1) := by
    rw [pow_succ']
  have hk0 : blockGoal_k0 R0 = Nat.log 2 R0 + 1 := by
    simp [blockGoal_k0, hR0]
  rw [hk0, ← hpow]
  exact hmul

private lemma blockGoal_sum_range_k0_le_two_mul_R0 (R0 : ℕ) :
    (∑ k ∈ Finset.range (blockGoal_k0 R0), ((2 ^ k : ℕ) : ℝ)) ≤ ((2 * R0 : ℕ) : ℝ) := by
  by_cases hR0 : R0 = 0
  · subst R0
    simp [blockGoal_k0]
  · calc
      (∑ k ∈ Finset.range (blockGoal_k0 R0), ((2 ^ k : ℕ) : ℝ))
          = ((2 ^ blockGoal_k0 R0 : ℕ) : ℝ) - 1 := blockGoal_sum_range_two_pow (blockGoal_k0 R0)
      _ ≤ ((2 ^ blockGoal_k0 R0 : ℕ) : ℝ) := by linarith
      _ ≤ ((2 * R0 : ℕ) : ℝ) := by
            exact_mod_cast (blockGoal_two_pow_k0_le_two_mul_R0 R0 hR0)

/-! ## The natural logarithm of the dyadic block size -/

private lemma blockGoal_nat_log_le_log_div_log_two {x : ℕ} (hx : 1 ≤ x) :
    ((Nat.log 2 x : ℕ) : ℝ) ≤ Real.log (x : ℝ) / Real.log 2 := by
  have hxne : x ≠ 0 := by omega
  have hpow_nat : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 hxne
  have hpow : (2 : ℝ) ^ Nat.log 2 x ≤ (x : ℝ) := by
    exact_mod_cast hpow_nat
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hpow_pos : 0 < (2 : ℝ) ^ Nat.log 2 x := pow_pos (by norm_num : (0 : ℝ) < 2) _
  have hle : Real.log ((2 : ℝ) ^ Nat.log 2 x) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hpow_pos hpow
  have hle' : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log (x : ℝ) := by
    simpa [Real.log_pow] using hle
  exact (le_div_iff₀ hlog2).2 hle'

/-! ## Pointwise inequality for `Aextra` -/

private lemma blockGoal_Aextra_le_const_mul_log_add_small
    (R0 : ℕ) (C : ℝ) (hCnonneg : 0 ≤ C)
    (hblock : ∀ R : ℕ, R0 ≤ R → ∀ x : ℕ, W R x ≤ C) :
    ∀ x : ℕ, 1 ≤ x →
      Aextra x ≤ (C / Real.log 2) * Real.log (x : ℝ) + C
        + ((2 * R0 : ℕ) : ℝ) *
          (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) := by
  intro x hx
  let K := Nat.log 2 x
  let k0 := blockGoal_k0 R0
  let P : Finset ℕ := (Finset.Icc 2 x).filter Nat.Prime
  let M : ℝ := ∑ p ∈ P, (1 / ((p - 1 : ℕ) : ℝ))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, P]
    exact Finset.sum_nonneg (by
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))
  have hW_small : ∀ k, k < k0 → W (2 ^ k) x ≤ ((2 ^ k : ℕ) : ℝ) * M := by
    intro k hk
    have hW := blockGoal_W_le_R_mul_sum_inv_pred (2 ^ k) x
    simpa [P, M] using hW
  have hW_big : ∀ k, k0 ≤ k → W (2 ^ k) x ≤ C := by
    intro k hk
    exact hblock (2 ^ k) (blockGoal_R0_le_two_pow R0 hk) x
  have hterm : ∀ k ∈ Finset.range (K + 1),
      W (2 ^ k) x ≤ (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else C) := by
    intro k hk
    by_cases hklt : k < k0
    · simp only [hklt, ite_true]
      exact hW_small k hklt
    · have hkle : k0 ≤ k := Nat.le_of_not_gt hklt
      simp only [hklt, ite_false]
      exact hW_big k hkle
  have hsum_blocks :
      (∑ k ∈ Finset.range (K + 1), W (2 ^ k) x)
        ≤ ∑ k ∈ Finset.range (K + 1), (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else C) :=
    Finset.sum_le_sum hterm
  have hifsum :
      (∑ k ∈ Finset.range (K + 1), (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else C))
        = (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
          + (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), C) := by
    rw [Finset.sum_ite]
  have hsmall_sum :
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
        ≤ ((2 * R0 : ℕ) : ℝ) * M := by
    have hsub : (Finset.range (K + 1)).filter (fun k => k < k0) ⊆ Finset.range k0 := by
      intro k hk
      rw [Finset.mem_range]
      exact (Finset.mem_filter.mp hk).2
    have hsum_le_range :
        (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ))
          ≤ ∑ k ∈ Finset.range k0, ((2 ^ k : ℕ) : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro k hk hks
        exact Nat.cast_nonneg _)
    calc
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
          = (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ)) * M := by
              rw [← Finset.sum_mul]
      _ ≤ (∑ k ∈ Finset.range k0, ((2 ^ k : ℕ) : ℝ)) * M :=
              mul_le_mul_of_nonneg_right hsum_le_range hM_nonneg
      _ ≤ ((2 * R0 : ℕ) : ℝ) * M :=
              mul_le_mul_of_nonneg_right (blockGoal_sum_range_k0_le_two_mul_R0 R0) hM_nonneg
  have hbig_sum :
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), C)
        ≤ C * ((K + 1 : ℕ) : ℝ) := by
    have hsub : (Finset.range (K + 1)).filter (fun k => ¬ k < k0) ⊆ Finset.range (K + 1) := by
      intro k hk
      exact (Finset.mem_filter.mp hk).1
    have hcard : ((Finset.range (K + 1)).filter (fun k => ¬ k < k0)).card ≤ K + 1 := by
      simpa [Finset.card_range] using Finset.card_le_card hsub
    calc
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), C)
          = (((Finset.range (K + 1)).filter (fun k => ¬ k < k0)).card : ℝ) * C := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((K + 1 : ℕ) : ℝ) * C := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hCnonneg
      _ = C * ((K + 1 : ℕ) : ℝ) := by ring
  have hK_log : ((K : ℕ) : ℝ) ≤ Real.log (x : ℝ) / Real.log 2 := by
    simpa [K] using blockGoal_nat_log_le_log_div_log_two hx
  have hK_cast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC_K :
      C * ((K + 1 : ℕ) : ℝ) ≤ (C / Real.log 2) * Real.log (x : ℝ) + C := by
    have h1 : C * (K : ℝ) ≤ C * (Real.log (x : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hK_log hCnonneg
    have h2 : C * (Real.log (x : ℝ) / Real.log 2) = (C / Real.log 2) * Real.log (x : ℝ) := by
      ring
    rw [hK_cast]
    calc
      C * ((K : ℝ) + 1) = C * (K : ℝ) + C := by ring
      _ ≤ C * (Real.log (x : ℝ) / Real.log 2) + C := by linarith
      _ = (C / Real.log 2) * Real.log (x : ℝ) + C := by rw [h2]
  have hmain_sum :
      (∑ k ∈ Finset.range (K + 1), W (2 ^ k) x)
        ≤ (C / Real.log 2) * Real.log (x : ℝ) + C + ((2 * R0 : ℕ) : ℝ) * M := by
    calc
      (∑ k ∈ Finset.range (K + 1), W (2 ^ k) x)
          ≤ ∑ k ∈ Finset.range (K + 1), (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else C) := hsum_blocks
      _ = (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
          + (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), C) := hifsum
      _ ≤ ((2 * R0 : ℕ) : ℝ) * M + C * ((K + 1 : ℕ) : ℝ) := add_le_add hsmall_sum hbig_sum
      _ ≤ ((2 * R0 : ℕ) : ℝ) * M + ((C / Real.log 2) * Real.log (x : ℝ) + C) := by
              linarith [hC_K]
      _ = (C / Real.log 2) * Real.log (x : ℝ) + C + ((2 * R0 : ℕ) : ℝ) * M := by ring
  have hmain : Aextra x ≤ (C / Real.log 2) * Real.log (x : ℝ) + C + ((2 * R0 : ℕ) : ℝ) * M := by
    calc
      Aextra x = ∑ k ∈ Finset.range (Nat.log 2 x + 1), W (2 ^ k) x := by
        exact Aextra_eq_sum_dyadic_blocks x
      _ = ∑ k ∈ Finset.range (K + 1), W (2 ^ k) x := by rfl
      _ ≤ (C / Real.log 2) * Real.log (x : ℝ) + C + ((2 * R0 : ℕ) : ℝ) * M := hmain_sum
  simpa [P, M] using hmain

/-! ## Turning a quotient tending to zero into an eventual linear bound -/

private lemma blockGoal_eventually_le_mul_log_of_div_log_tendsto_zero
    {f : ℕ → ℝ} (ε : ℝ) (hε : 0 < ε)
    (hf : Tendsto (fun x : ℕ => f x / Real.log (x : ℝ)) atTop (𝓝 0))
    (hfnonneg : ∀ᶠ x : ℕ in atTop, 0 ≤ f x) :
    ∀ᶠ x : ℕ in atTop, f x ≤ ε * Real.log (x : ℝ) := by
  have hlog_pos_ev : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    exact Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
  rcases Metric.tendsto_atTop.mp hf ε hε with ⟨N, hN⟩
  filter_upwards [hlog_pos_ev, hfnonneg, eventually_ge_atTop N] with x hxpos hxnonneg hxN
  have hq_abs : |f x / Real.log (x : ℝ)| < ε := by
    have hdist := hN x hxN
    rw [Real.dist_eq] at hdist
    simpa only [sub_zero] using hdist
  have hqnonneg : 0 ≤ f x / Real.log (x : ℝ) :=
    div_nonneg hxnonneg (le_of_lt hxpos)
  have hqlt : f x / Real.log (x : ℝ) < ε := by
    simpa [abs_of_nonneg hqnonneg] using hq_abs
  exact le_of_lt ((div_lt_iff₀ hxpos).1 hqlt)

/-! ## Lemma 12A: quantitative block bound implies `Aextra ≤ log / 8` -/

theorem Aextra_eventually_le_eighth_log_of_block_bound
    (h : ∃ R₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ C < Real.log 2 / 8 ∧
      ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ C) :
    ∀ᶠ x : ℕ in atTop, Aextra x ≤ (1 / 8 : ℝ) * Real.log (x : ℝ) := by
  rcases h with ⟨R0, C, hCnonneg, hC, hblock⟩
  let α : ℝ := C / Real.log 2
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hα_lt : α < 1 / 8 := by
    dsimp [α]
    rw [div_lt_iff₀ hlog2pos]
    calc
      C < Real.log 2 / 8 := hC
      _ = (1 / 8 : ℝ) * Real.log 2 := by ring
  let η : ℝ := (1 / 8 - α) / 2
  have hηpos : 0 < η := by
    dsimp [η]
    linarith [hα_lt]
  have hηhalfpos : 0 < η / 2 := div_pos hηpos (by norm_num)
  have hαη_lt : α + η < 1 / 8 := by
    dsimp [η]
    linarith [hα_lt]
  have hCevent : ∀ᶠ x : ℕ in atTop, C ≤ (η / 2) * Real.log (x : ℝ) := by
    have hlogtend : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hCdiv : Tendsto (fun x : ℕ => C / Real.log (x : ℝ)) atTop (𝓝 0) := by
      have h : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
      exact h.div_atTop hlogtend
    exact blockGoal_eventually_le_mul_log_of_div_log_tendsto_zero (η / 2) hηhalfpos hCdiv
      (by filter_upwards [] with x; exact hCnonneg)
  let A : ℝ := (2 * R0 : ℕ)
  have hsmallevent : ∀ᶠ x : ℕ in atTop,
      A * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ (η / 2) * Real.log (x : ℝ) := by
    have hquot : Tendsto (fun x : ℕ =>
        (A * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))))
          / Real.log (x : ℝ)) atTop (𝓝 0) := by
      simpa [mul_div_assoc] using (sum_inv_pred_div_log_tendsto_zero.const_mul A)
    have hnonneg : ∀ᶠ x : ℕ in atTop,
        0 ≤ A * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) := by
      filter_upwards [] with x
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (by
        intro p hp
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)))
    exact blockGoal_eventually_le_mul_log_of_div_log_tendsto_zero (η / 2) hηhalfpos hquot hnonneg
  have hmain_event : ∀ᶠ x : ℕ in atTop,
      Aextra x ≤ (1 / 8 : ℝ) * Real.log (x : ℝ) := by
    filter_upwards [hCevent, hsmallevent, eventually_gt_atTop (1 : ℕ)] with x hCx hsmallx hxgt1
    have hx1 : 1 ≤ x := by omega
    have hlog_nonneg : 0 ≤ Real.log (x : ℝ) := by
      exact le_of_lt (Real.log_pos (by exact_mod_cast hxgt1 : (1 : ℝ) < (x : ℝ)))
    have hpoint := blockGoal_Aextra_le_const_mul_log_add_small R0 C hCnonneg hblock x hx1
    have hle : Aextra x ≤ (α + η) * Real.log (x : ℝ) := by
      calc
        Aextra x ≤ α * Real.log (x : ℝ) + C
            + (2 * R0 : ℕ) *
              (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) := by
              simpa [α, A] using hpoint
        _ ≤ α * Real.log (x : ℝ) + (η / 2) * Real.log (x : ℝ)
            + (η / 2) * Real.log (x : ℝ) := by
              linarith
        _ = (α + η) * Real.log (x : ℝ) := by ring
    have hαη_le : (α + η) * Real.log (x : ℝ) ≤ (1 / 8 : ℝ) * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_right (le_of_lt hαη_lt) hlog_nonneg
    exact le_trans hle hαη_le
  exact hmain_event

/-! ## Lemma 12A implies the product tends to infinity -/

theorem xP_tendsto_atTop_of_block_bound
    (h : ∃ R₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ C < Real.log 2 / 8 ∧
      ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ C) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  have hA : ∀ᶠ x : ℕ in atTop, Aextra x ≤ (1 / 8 : ℝ) * Real.log (x : ℝ) :=
    Aextra_eventually_le_eighth_log_of_block_bound h
  have hInv : ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ (1 / 16 : ℝ) * Real.log (x : ℝ) := by
    exact blockGoal_eventually_le_mul_log_of_div_log_tendsto_zero (1 / 16 : ℝ) (by norm_num)
      sum_inv_pred_Icc3_div_log_tendsto_zero
      (by filter_upwards [] with x
          exact Finset.sum_nonneg (by
            intro p hp
            exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)))
  have hW : ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ))
        ≤ (1 / 16 : ℝ) * Real.log (x : ℝ) := by
    exact blockGoal_eventually_le_mul_log_of_div_log_tendsto_zero (1 / 16 : ℝ) (by norm_num)
      sum_w_div_log_tendsto_zero
      (by filter_upwards [] with x; exact sum_w_nonneg x)
  have hS : ∀ᶠ x : ℕ in atTop, S x ≤ (3 / 8 : ℝ) * Real.log (x : ℝ) := by
    filter_upwards [hInv, hW, hA] with x hInvx hWx hAx
    have hS4 := S_eq_sum_inv_pred_add_sum_w_add_two_mul_Aextra x
    calc
      S x = (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
          + (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ))
          + 2 * Aextra x := hS4
      _ ≤ (1 / 16 : ℝ) * Real.log (x : ℝ) + (1 / 16 : ℝ) * Real.log (x : ℝ)
          + 2 * ((1 / 8 : ℝ) * Real.log (x : ℝ)) := by
            linarith
      _ = (3 / 8 : ℝ) * Real.log (x : ℝ) := by ring
  exact xP_tendsto_atTop_of_S_le_const_mul_log ⟨(3 / 8 : ℝ), by norm_num, hS⟩

end Erdos291
