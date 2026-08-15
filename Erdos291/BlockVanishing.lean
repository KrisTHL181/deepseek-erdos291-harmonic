import Erdos291.DyadicBlocks
import Erdos291.SymmetryOrbits
import Erdos291.ProdUnbounded
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Uniform vanishing of the dyadic blocks implies `HA_arith_weak`

Assume the dyadic block contributions `W R x` tend to zero uniformly in `x` as
`R → ∞`.  Then the small dyadic blocks (`k < k₀`) only contribute
`O_R₀(Σ 1/(p-1)) = o(log x)`, while each large block is bounded by an
arbitrarily small `ε`.  Hence `Aextra x = o(log x)`, which is equivalent to
`HA_arith_weak`, and consequently `x * prodOneSub x` tends to `atTop`.
-/

open scoped BigOperators
open scoped Topology
open Filter

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## A crude per-block bound by the Icc-2 Mertens sum -/

private lemma blockVanishing_W_le_R_mul_sum_inv_pred (R x : ℕ) :
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

/-! ## Nonnegativity of `Aextra` -/

private lemma blockVanishing_Aextra_nonneg (x : ℕ) : 0 ≤ Aextra x := by
  unfold Aextra
  exact Finset.sum_nonneg (by
    intro p hp
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-! ## Small dyadic blocks: finite geometric sum -/

private def blockVanishing_k0 (R0 : ℕ) : ℕ :=
  if R0 = 0 then 0 else Nat.log 2 R0 + 1

private lemma blockVanishing_R0_le_two_pow (R0 : ℕ) {k : ℕ} (hk : blockVanishing_k0 R0 ≤ k) :
    R0 ≤ 2 ^ k := by
  unfold blockVanishing_k0 at hk
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

private lemma blockVanishing_sum_range_two_pow (n : ℕ) :
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

private lemma blockVanishing_two_pow_k0_le_two_mul_R0 (R0 : ℕ) (hR0 : R0 ≠ 0) :
    (2 ^ blockVanishing_k0 R0 : ℕ) ≤ 2 * R0 := by
  have hlog : 2 ^ Nat.log 2 R0 ≤ R0 := Nat.pow_log_le_self 2 hR0
  have hmul : 2 * 2 ^ Nat.log 2 R0 ≤ 2 * R0 := Nat.mul_le_mul_left 2 hlog
  have hpow : 2 * 2 ^ Nat.log 2 R0 = 2 ^ (Nat.log 2 R0 + 1) := by
    rw [pow_succ']
  have hk0 : blockVanishing_k0 R0 = Nat.log 2 R0 + 1 := by
    simp [blockVanishing_k0, hR0]
  rw [hk0, ← hpow]
  exact hmul

private lemma blockVanishing_sum_range_k0_le_two_mul_R0 (R0 : ℕ) :
    (∑ k ∈ Finset.range (blockVanishing_k0 R0), ((2 ^ k : ℕ) : ℝ)) ≤ ((2 * R0 : ℕ) : ℝ) := by
  by_cases hR0 : R0 = 0
  · subst R0
    simp [blockVanishing_k0]
  · calc
      (∑ k ∈ Finset.range (blockVanishing_k0 R0), ((2 ^ k : ℕ) : ℝ))
          = ((2 ^ blockVanishing_k0 R0 : ℕ) : ℝ) - 1 := blockVanishing_sum_range_two_pow (blockVanishing_k0 R0)
      _ ≤ ((2 ^ blockVanishing_k0 R0 : ℕ) : ℝ) := by linarith
      _ ≤ ((2 * R0 : ℕ) : ℝ) := by
            exact_mod_cast (blockVanishing_two_pow_k0_le_two_mul_R0 R0 hR0)

/-! ## The natural logarithm of the dyadic block size -/

private lemma blockVanishing_nat_log_le_log_div_log_two {x : ℕ} (hx : 1 ≤ x) :
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

/-! ## Turning a quotient tending to zero into an eventual linear bound -/

private lemma blockVanishing_eventually_le_mul_log_of_div_log_tendsto_zero
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

/-! ## Pointwise inequality for `Aextra / log` -/

private lemma blockVanishing_Aextra_div_log_le
    (R₀ : ℕ) (ε' : ℝ) (hε'nonneg : 0 ≤ ε')
    (hblock : ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ ε')
    {x : ℕ} (hx2 : 2 ≤ x) :
    Aextra x / Real.log (x : ℝ)
      ≤ (((2 * R₀ : ℕ) : ℝ) *
          (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))) / Real.log (x : ℝ)
        + ε' / Real.log 2 + ε' / Real.log (x : ℝ) := by
  let K := Nat.log 2 x
  let k0 := blockVanishing_k0 R₀
  let P : Finset ℕ := (Finset.Icc 2 x).filter Nat.Prime
  let M : ℝ := ∑ p ∈ P, (1 / ((p - 1 : ℕ) : ℝ))
  have hx1 : 1 ≤ x := by omega
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx2 : (1 : ℝ) < (x : ℝ))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, P]
    exact Finset.sum_nonneg (by
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))
  have hW_small : ∀ k, k < k0 → W (2 ^ k) x ≤ ((2 ^ k : ℕ) : ℝ) * M := by
    intro k hk
    have hW := blockVanishing_W_le_R_mul_sum_inv_pred (2 ^ k) x
    simpa [P, M] using hW
  have hW_big : ∀ k, k0 ≤ k → W (2 ^ k) x ≤ ε' := by
    intro k hk
    exact hblock (2 ^ k) (blockVanishing_R0_le_two_pow R₀ hk) x
  have hterm : ∀ k ∈ Finset.range (K + 1),
      W (2 ^ k) x ≤ (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else ε') := by
    intro k hk
    by_cases hklt : k < k0
    · simp only [hklt, ite_true]
      exact hW_small k hklt
    · have hkle : k0 ≤ k := Nat.le_of_not_gt hklt
      simp only [hklt, ite_false]
      exact hW_big k hkle
  have hsum_blocks :
      (∑ k ∈ Finset.range (K + 1), W (2 ^ k) x)
        ≤ ∑ k ∈ Finset.range (K + 1), (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else ε') :=
    Finset.sum_le_sum hterm
  have hifsum :
      (∑ k ∈ Finset.range (K + 1), (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else ε'))
        = (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
          + (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), ε') := by
    rw [Finset.sum_ite]
  have hsmall_sum :
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
        ≤ ((2 * R₀ : ℕ) : ℝ) * M := by
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
      _ ≤ ((2 * R₀ : ℕ) : ℝ) * M :=
              mul_le_mul_of_nonneg_right (blockVanishing_sum_range_k0_le_two_mul_R0 R₀) hM_nonneg
  have hbig_sum :
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), ε')
        ≤ ε' * ((K + 1 : ℕ) : ℝ) := by
    have hsub : (Finset.range (K + 1)).filter (fun k => ¬ k < k0) ⊆ Finset.range (K + 1) := by
      intro k hk
      exact (Finset.mem_filter.mp hk).1
    have hcard : ((Finset.range (K + 1)).filter (fun k => ¬ k < k0)).card ≤ K + 1 := by
      simpa [Finset.card_range] using Finset.card_le_card hsub
    calc
      (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), ε')
          = (((Finset.range (K + 1)).filter (fun k => ¬ k < k0)).card : ℝ) * ε' := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((K + 1 : ℕ) : ℝ) * ε' := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε'nonneg
      _ = ε' * ((K + 1 : ℕ) : ℝ) := by ring
  have hK_log : ((K : ℕ) : ℝ) ≤ Real.log (x : ℝ) / Real.log 2 := by
    simpa [K] using blockVanishing_nat_log_le_log_div_log_two hx1
  have hK_cast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by
    rw [Nat.cast_add]
    norm_num
  have hbig_le :
      ε' * ((K + 1 : ℕ) : ℝ) ≤ ε' * (Real.log (x : ℝ) / Real.log 2 + 1) := by
    have h1 : ε' * (K : ℝ) ≤ ε' * (Real.log (x : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hK_log hε'nonneg
    rw [hK_cast]
    calc
      ε' * ((K : ℝ) + 1) = ε' * (K : ℝ) + ε' := by ring
      _ ≤ ε' * (Real.log (x : ℝ) / Real.log 2) + ε' := by linarith
      _ = ε' * (Real.log (x : ℝ) / Real.log 2 + 1) := by ring
  have hmain_sum :
      (∑ k ∈ Finset.range (K + 1), W (2 ^ k) x)
        ≤ ((2 * R₀ : ℕ) : ℝ) * M + ε' * (Real.log (x : ℝ) / Real.log 2 + 1) := by
    calc
      (∑ k ∈ Finset.range (K + 1), W (2 ^ k) x)
          ≤ ∑ k ∈ Finset.range (K + 1), (if k < k0 then ((2 ^ k : ℕ) : ℝ) * M else ε') := hsum_blocks
      _ = (∑ k ∈ (Finset.range (K + 1)).filter (fun k => k < k0), ((2 ^ k : ℕ) : ℝ) * M)
          + (∑ k ∈ (Finset.range (K + 1)).filter (fun k => ¬ k < k0), ε') := hifsum
      _ ≤ ((2 * R₀ : ℕ) : ℝ) * M + ε' * ((K + 1 : ℕ) : ℝ) := add_le_add hsmall_sum hbig_sum
      _ ≤ ((2 * R₀ : ℕ) : ℝ) * M + ε' * (Real.log (x : ℝ) / Real.log 2 + 1) := by
              linarith [hbig_le]
  have hmain : Aextra x ≤ ((2 * R₀ : ℕ) : ℝ) * M + ε' * (Real.log (x : ℝ) / Real.log 2 + 1) := by
    calc
      Aextra x = ∑ k ∈ Finset.range (Nat.log 2 x + 1), W (2 ^ k) x := by
        exact Aextra_eq_sum_dyadic_blocks x
      _ = ∑ k ∈ Finset.range (K + 1), W (2 ^ k) x := by rfl
      _ ≤ ((2 * R₀ : ℕ) : ℝ) * M + ε' * (Real.log (x : ℝ) / Real.log 2 + 1) := hmain_sum
  have hdivbound :
      Aextra x / Real.log (x : ℝ)
        ≤ ((2 * R₀ : ℕ) : ℝ) * M / Real.log (x : ℝ)
          + ε' * (Real.log (x : ℝ) / Real.log 2 + 1) / Real.log (x : ℝ) := by
    have hle := div_le_div_of_nonneg_right hmain (le_of_lt hlogpos)
    simpa [add_div] using hle
  have hlogterm :
      ε' * (Real.log (x : ℝ) / Real.log 2 + 1) / Real.log (x : ℝ)
        = ε' / Real.log 2 + ε' / Real.log (x : ℝ) := by
    field_simp [hlogpos.ne', hlog2pos.ne']
  calc
    Aextra x / Real.log (x : ℝ)
        ≤ ((2 * R₀ : ℕ) : ℝ) * M / Real.log (x : ℝ)
          + ε' * (Real.log (x : ℝ) / Real.log 2 + 1) / Real.log (x : ℝ) := hdivbound
    _ = ((2 * R₀ : ℕ) : ℝ) * M / Real.log (x : ℝ)
          + (ε' / Real.log 2 + ε' / Real.log (x : ℝ)) := by rw [hlogterm]
    _ = ((2 * R₀ : ℕ) : ℝ) * M / Real.log (x : ℝ)
          + ε' / Real.log 2 + ε' / Real.log (x : ℝ) := by ring

/-! ## The quotient `Aextra / log` tends to zero -/

private lemma blockVanishing_Aextra_div_log_tendsto_zero
    (h : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ ε) :
    Tendsto (fun x : ℕ => Aextra x / Real.log (x : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog2_lt_two : Real.log 2 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    have h3 : (2 : ℝ) + 1 < Real.exp 2 := by
      simpa using (Real.add_one_lt_exp (x := 2) (by norm_num : (2 : ℝ) ≠ 0))
    linarith
  let ε' : ℝ := δ * Real.log 2 / 4
  have hε'pos : 0 < ε' := div_pos (mul_pos hδ hlog2pos) (by norm_num : (0 : ℝ) < 4)
  have hε'nonneg : 0 ≤ ε' := le_of_lt hε'pos
  rcases h ε' hε'pos with ⟨R₀, hR₀⟩
  let A : ℝ := ((2 * R₀ : ℕ) : ℝ)
  have hsmall_ev : ∀ᶠ x : ℕ in atTop,
      A * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ ε' * Real.log (x : ℝ) := by
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
    exact blockVanishing_eventually_le_mul_log_of_div_log_tendsto_zero ε' hε'pos hquot hnonneg
  have hx2_ev : ∀ᶠ x : ℕ in atTop, 2 ≤ x := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx
    exact hx
  have hlogpos_ev : ∀ᶠ x : ℕ in atTop, 0 < Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    exact Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
  have hfinal : ∀ᶠ x : ℕ in atTop, dist (Aextra x / Real.log (x : ℝ)) 0 < δ := by
    filter_upwards [hsmall_ev, hx2_ev, hlogpos_ev] with x hsmallx hx2 hxlog
    have hqnonneg : 0 ≤ Aextra x / Real.log (x : ℝ) :=
      div_nonneg (blockVanishing_Aextra_nonneg x) (le_of_lt hxlog)
    have hpoint := blockVanishing_Aextra_div_log_le R₀ ε' hε'nonneg hR₀ hx2
    have hlog2lelog : Real.log 2 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hx2 : (2 : ℝ) ≤ (x : ℝ))
    have hsmallq :
        A * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
          ≤ ε' := by
      exact (div_le_iff₀ hxlog).2 hsmallx
    have hthird : ε' / Real.log (x : ℝ) ≤ ε' / Real.log 2 := by
      exact div_le_div_of_nonneg_left hε'nonneg hlog2pos hlog2lelog
    have hupper1 : Aextra x / Real.log (x : ℝ) ≤ ε' + ε' / Real.log 2 + ε' / Real.log 2 := by
      calc
        Aextra x / Real.log (x : ℝ)
            ≤ A * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
              + ε' / Real.log 2 + ε' / Real.log (x : ℝ) := by
                  simpa [A] using hpoint
        _ ≤ ε' + ε' / Real.log 2 + ε' / Real.log 2 := by linarith
    have hbigval : ε' / Real.log 2 + ε' / Real.log 2 = δ / 2 := by
      dsimp [ε']
      field_simp [hlog2pos.ne']
      ring
    have hupper2 : Aextra x / Real.log (x : ℝ) ≤ ε' + δ / 2 := by
      linarith
    have hε'lt : ε' < δ / 2 := by
      have h1 : δ * Real.log 2 < δ * 2 := mul_lt_mul_of_pos_left hlog2_lt_two hδ
      dsimp [ε']
      nlinarith
    have hlt : ε' + δ / 2 < δ := by
      nlinarith
    have hqlt : Aextra x / Real.log (x : ℝ) < δ := lt_of_le_of_lt hupper2 hlt
    rw [Real.dist_eq]
    rw [sub_zero]
    rw [abs_of_nonneg hqnonneg]
    exact hqlt
  exact Filter.eventually_atTop.1 hfinal

/-! ## Proposition 12B: uniform block vanishing implies `HA_arith_weak` -/

theorem HA_arith_weak_of_W_uniformly_tends_to_zero
    (h : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ ε) :
    HA_arith_weak := by
  exact HA_arith_weak_iff_Aextra_o_log.mpr (blockVanishing_Aextra_div_log_tendsto_zero h)

/-! ## Corollary: uniform block vanishing implies `x · P x → ∞` -/

theorem xP_tendsto_atTop_of_W_uniformly_tends_to_zero
    (h : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ ε) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop :=
  xP_tendsto_atTop_of_HA_arith_weak (HA_arith_weak_of_W_uniformly_tends_to_zero h)

end Erdos291
