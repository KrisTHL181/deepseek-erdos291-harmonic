import Erdos291.BlockActiveProof
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Weighted-row bound for `Wmid`

This file reduces the direct middle-block bound `HA_Wmid_constant_bound` to a
weighted row-sum hypothesis.  For each `r ∈ [R, 2R)` let

  `middleRowMass r x = Σ_{p ≤ x, 2r+1 < p ≤ r², p prime, p ∣ num H_r} 1/(p-1)`

and set `WmidWeightedRowSum R x = Σ_{r∈[R,2R)} r · middleRowMass r x`.
Since `r ≥ R` on the block, `Wmid R x ≤ WmidWeightedRowSum R x / R`
(unconditionally).  Splitting the digit sum into exceptional primes
`p ∣ Nall R` and the rest gives the unconditional estimate

  `Wmid R x ≤ 2 * middleActiveMassStrict R x + trueMiddleExceptionalMass R x`.

The remaining hypothesis `HA_WmidWeightedRowSum_log_bound` states the
logarithmic row bound `WmidWeightedRowSum R x ≤ R / (2 log(2R))` for
`R ≥ 18`.  A C scan gives `max ((Sy/R) · log(2R)) ≈ 0.4848 < 0.5` for
`R ≤ 3184`; under this hypothesis, for `R ≥ 4096`,
`1 / (2 log(2R)) ≤ 0.055489 < 0.057082`, so `HA_Wmid_constant_bound` follows
with `R₀ = 4096` and `C = 0.057082`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-- The mass of the middle row `r`: primes `p ≤ x` satisfying
`2r+1 < p ≤ r²` and dividing the numerator of the harmonic number `H_r`,
weighted by `1/(p-1)`. -/
noncomputable def middleRowMass (r x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter
      (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
    primeWeight p

/-- The `r`-weighted sum of the middle row masses over `r ∈ [R, 2R)`. -/
noncomputable def WmidWeightedRowSum (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMass r x

/-- The true middle exceptional mass: primes `p ≤ x` dividing `Nall R`,
counted with their number of middle-active digits.  (This is the exact
exceptional contribution, without the `R` amplification used in
`BlockActive.exceptionalMassAboveR`.) -/
noncomputable def trueMiddleExceptionalMass (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ Nall R),
    (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p

/-- `Wmid R x` is defeq to the sum of the row masses over the block. -/
lemma Wmid_eq_sum_middleRowMass (R x : ℕ) :
    Wmid R x = ∑ r ∈ Finset.Ico R (2 * R), middleRowMass r x := by
  rfl

/-- Each row mass is nonnegative. -/
lemma middleRowMass_nonneg (r x : ℕ) : 0 ≤ middleRowMass r x := by
  unfold middleRowMass
  exact Finset.sum_nonneg (by
    intro p hp
    dsimp [primeWeight]
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

/-- On the block `[R, 2R)` each row mass is multiplied by at least one in the
weighted row sum, so `Wmid` is at most the weighted row sum divided by `R`. -/
lemma Wmid_le_WmidWeightedRowSum_div_R (R x : ℕ) (hR : 0 < R) :
    Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := by
  classical
  have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hR
  have hRreal_ne : (R : ℝ) ≠ 0 := ne_of_gt hRreal_pos
  have h_le (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      middleRowMass r x ≤ ((r : ℝ) / (R : ℝ)) * middleRowMass r x := by
    have hrI := Finset.mem_Ico.mp hr
    have hRle : (R : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrI.1
    have hone : (1 : ℝ) ≤ (r : ℝ) / (R : ℝ) := by
      rw [le_div_iff₀ hRreal_pos]
      simpa [one_mul] using hRle
    have hm : 0 ≤ middleRowMass r x := middleRowMass_nonneg r x
    calc
      middleRowMass r x = (1 : ℝ) * middleRowMass r x := by rw [one_mul]
      _ ≤ ((r : ℝ) / (R : ℝ)) * middleRowMass r x :=
        mul_le_mul_of_nonneg_right hone hm
  have hsum : Wmid R x ≤ ∑ r ∈ Finset.Ico R (2 * R),
      ((r : ℝ) / (R : ℝ)) * middleRowMass r x := by
    rw [Wmid_eq_sum_middleRowMass]
    refine Finset.sum_le_sum ?_
    intro r hr
    exact h_le r hr
  have hsum_div : (∑ r ∈ Finset.Ico R (2 * R),
      ((r : ℝ) / (R : ℝ)) * middleRowMass r x)
      = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMass r x) / (R : ℝ) := by
    calc
      (∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) / (R : ℝ)) * middleRowMass r x)
          = ∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) * middleRowMass r x) / (R : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            ring
      _ = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMass r x) / (R : ℝ) := by
            rw [Finset.sum_div]
  calc
    Wmid R x ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ((r : ℝ) / (R : ℝ)) * middleRowMass r x := hsum
    _ = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMass r x) / (R : ℝ) := hsum_div
    _ = WmidWeightedRowSum R x / (R : ℝ) := by rfl

/-- Saturation of a single row mass at `x = 4R²`: for `r ∈ [R,2R)` every
middle prime has `p ≤ r² < 4R²`. -/
lemma middleRowMass_le_fourR2 (R x r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
    middleRowMass r x ≤ middleRowMass r (4 * R ^ 2) := by
  classical
  let y : ℕ := 4 * R ^ 2
  by_cases hxy : x ≤ y
  · unfold middleRowMass
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpIcc := Finset.mem_Icc.mp hpF.1
      have hpy : p ≤ y := le_trans hpIcc.2 hxy
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpy⟩, hpF.2⟩
    · intro p hp hpnot
      dsimp [primeWeight]
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  · have hyx : y ≤ x := by omega
    have hmain : middleRowMass r x = middleRowMass r y := by
      unfold middleRowMass
      have hfilter : (Finset.Icc 2 x).filter
          (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)
          = (Finset.Icc 2 y).filter
          (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num) := by
        ext p
        constructor
        · intro hp
          have hpF := Finset.mem_filter.mp hp
          have hpIcc := Finset.mem_Icc.mp hpF.1
          have hple : p ≤ r ^ 2 := hpF.2.2.1
          have hrI := Finset.mem_Ico.mp hr
          have hsq : r ^ 2 < 4 * R ^ 2 := by nlinarith
          have hpy : p ≤ y := by dsimp [y]; omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpy⟩, hpF.2⟩
        · intro hp
          have hpF := Finset.mem_filter.mp hp
          have hpIcc := Finset.mem_Icc.mp hpF.1
          have hpx : p ≤ x := le_trans hpIcc.2 hyx
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpx⟩, hpF.2⟩
      rw [hfilter]
    exact le_of_eq hmain

/-- The weighted row sum saturates at `x = 4R²`. -/
lemma WmidWeightedRowSum_le_fourR2 (R x : ℕ) :
    WmidWeightedRowSum R x ≤ WmidWeightedRowSum R (4 * R ^ 2) := by
  classical
  unfold WmidWeightedRowSum
  refine Finset.sum_le_sum ?_
  intro r hr
  exact mul_le_mul_of_nonneg_left (middleRowMass_le_fourR2 R x r hr) (Nat.cast_nonneg _)

/-- For a prime `p` not dividing `Nall R`, at most two middle-active digits of
`p` lie in the block `[R, 2R)`: they form a subset of `E p ∩ [R, 2R)`, whose
cardinality is at most two by `E_inter_card_le_two_of_not_dvd_Nall`. -/
lemma middleActiveDigits_card_le_two_of_not_dvd_Nall (R p : ℕ) (hp : Nat.Prime p)
    (h : ¬ p ∣ Nall R) : (middleActiveDigits R p).card ≤ 2 := by
  classical
  have hsub : middleActiveDigits R p ⊆ E p ∩ Finset.Ico R (2 * R) := by
    intro r hr
    have hrF := Finset.mem_filter.mp hr
    exact Finset.mem_inter.mpr ⟨hrF.1, Finset.mem_Ico.mpr ⟨hrF.2.1, hrF.2.2.1⟩⟩
  have hle := Finset.card_le_card hsub
  exact le_trans hle (E_inter_card_le_two_of_not_dvd_Nall p R hp h)

/-- The middle block is at most twice the strict middle-active mass plus the
true exceptional mass.  This is the same argument as
`BlockActive.Wmid_le_two_mul_activeMass_add_R_mul_exceptionalMassAboveR`, but
with the exact exceptional cardinality instead of the `R` amplification. -/
theorem Wmid_le_two_mul_middleActiveMassStrict_add_trueMiddleExceptional (R x : ℕ) :
    Wmid R x ≤ 2 * middleActiveMassStrict R x + trueMiddleExceptionalMass R x := by
  classical
  let P : Finset ℕ := (Finset.Icc 2 x).filter Nat.Prime
  have h1 : Wmid R x ≤ ∑ p ∈ P,
      (((middleActiveDigits R p).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    simpa [P] using Wmid_le_sum_middleActiveDigits_card_weight R x
  have hrewrite : (∑ p ∈ P,
        (((middleActiveDigits R p).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))
      = ∑ p ∈ P, (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [primeWeight]
    rw [mul_one_div]
  have hsplit :
      (∑ p ∈ P.filter (fun p => p ∣ Nall R),
          (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
        + (∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
          (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
        = ∑ p ∈ P, (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hexc : (∑ p ∈ P.filter (fun p => p ∣ Nall R),
        (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
      = trueMiddleExceptionalMass R x := by
    unfold trueMiddleExceptionalMass
    have hset : P.filter (fun p => p ∣ Nall R)
        = (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ∣ Nall R) := by
      ext p
      simp only [P, Finset.mem_filter, Finset.mem_Icc]
      tauto
    rw [hset]
  have hnexc_le_two_mass :
      (∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
          (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
        ≤ 2 * middleActiveMassStrict R x := by
    have hsub : P.filter (fun p => ¬ p ∣ Nall R) ⊆ P := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hle_sum :
        (∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
            (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
          ≤ ∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
            (if (middleActiveDigits R p).Nonempty then 2 * primeWeight p else 0) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpP).2
      have hnot : ¬ p ∣ Nall R := (Finset.mem_filter.mp hp).2
      have hcard : (middleActiveDigits R p).card ≤ 2 :=
        middleActiveDigits_card_le_two_of_not_dvd_Nall R p hpPrime hnot
      have hw' : 0 ≤ ((p - 1 : ℕ) : ℝ)⁻¹ :=
        inv_nonneg.mpr (Nat.cast_nonneg _)
      by_cases hnon : (middleActiveDigits R p).Nonempty
      · simp [hnon, primeWeight]
        have hcard' : (((middleActiveDigits R p).card : ℕ) : ℝ) ≤ (2 : ℝ) := by
          exact_mod_cast hcard
        simpa [primeWeight] using mul_le_mul_of_nonneg_right hcard' hw'
      · have hcard0 : (middleActiveDigits R p).card = 0 := by
          rw [Finset.card_eq_zero]
          exact Finset.not_nonempty_iff_eq_empty.mp hnon
        simp [hnon, hcard0]
    have hle_indicator :
        (∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
            (if (middleActiveDigits R p).Nonempty then 2 * primeWeight p else 0))
          ≤ ∑ p ∈ P, (if (middleActiveDigits R p).Nonempty then 2 * primeWeight p else 0) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hp hpnot
      by_cases h : (middleActiveDigits R p).Nonempty <;> simp [h]
    have hindicator :
        (∑ p ∈ P, (if (middleActiveDigits R p).Nonempty then 2 * primeWeight p else 0))
          = 2 * middleActiveMassStrict R x := by
      unfold middleActiveMassStrict
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : (middleActiveDigits R p).Nonempty <;> simp [h]
    calc
      (∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
          (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
          ≤ ∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
            (if (middleActiveDigits R p).Nonempty then 2 * primeWeight p else 0) := hle_sum
      _ ≤ ∑ p ∈ P,
            (if (middleActiveDigits R p).Nonempty then 2 * primeWeight p else 0) := hle_indicator
      _ = 2 * middleActiveMassStrict R x := hindicator
  calc
    Wmid R x ≤ ∑ p ∈ P,
        (((middleActiveDigits R p).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := h1
    _ = ∑ p ∈ P, (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p := hrewrite
    _ = (∑ p ∈ P.filter (fun p => p ∣ Nall R),
          (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p)
        + (∑ p ∈ P.filter (fun p => ¬ p ∣ Nall R),
          (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p) := by
          rw [← hsplit]
    _ ≤ trueMiddleExceptionalMass R x + 2 * middleActiveMassStrict R x := by
          exact add_le_add (le_of_eq hexc) hnexc_le_two_mass
    _ = 2 * middleActiveMassStrict R x + trueMiddleExceptionalMass R x := by ring

/-! ## The weighted row-sum log hypothesis -/

/-- The weighted row sum `Sy(R,x) = Σ_{r∈[R,2R)} r·middleRowMass r x` satisfies
the log bound `Sy ≤ R/(2 log(2R))` for all `R ≥ 18` and all `x`.  Numerically
max `(Sy/R)·log(2R) ≈ 0.4848 < 0.5` for `R ≤ 3184` (computed by C scans). -/
def HA_WmidWeightedRowSum_log_bound : Prop :=
  ∀ R : ℕ, 18 ≤ R → ∀ x : ℕ,
    WmidWeightedRowSum R x ≤ (R : ℝ) / (2 * Real.log (2 * (R : ℝ)))

/-! ## The threshold `1 / (2 log(2R)) ≤ 0.057082` for `R ≥ 4096` -/

/-- For `R ≥ 4096`, `1 / (2 log(2R)) ≤ 0.057082`.
Uses `8192 ≤ 2R`, `log 8192 = 13·log 2` and `0.6931471803 < log 2`. -/
lemma one_div_two_mul_log_two_mul_R_le_0_057082 (R : ℕ) (hR : 4096 ≤ R) :
    (1 : ℝ) / (2 * Real.log (2 * (R : ℝ))) ≤ 0.057082 := by
  have hRreal : (4096 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h2R : (8192 : ℝ) ≤ 2 * (R : ℝ) := by nlinarith
  have hlogmono : Real.log (8192 : ℝ) ≤ Real.log (2 * (R : ℝ)) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 8192) h2R
  have h8192pow : (8192 : ℝ) = (2 : ℝ) ^ 13 := by norm_num
  have hlog8192 : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
    calc
      Real.log (8192 : ℝ) = Real.log ((2 : ℝ) ^ 13) := by rw [h8192pow]
      _ = (13 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ = 13 * Real.log 2 := by norm_num
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hA : (9.0109133439 : ℝ) < Real.log (2 * (R : ℝ)) := by
    rw [hlog8192] at hlogmono
    nlinarith [hlogmono, hlog2gt]
  have hApos : 0 < Real.log (2 * (R : ℝ)) := by nlinarith [hA]
  have hden : 0 < 2 * Real.log (2 * (R : ℝ)) := by positivity
  have hnum : (1 : ℝ) ≤ 0.057082 * (2 * Real.log (2 * (R : ℝ))) := by
    have hconst : (1 : ℝ) < 0.057082 * (2 * 9.0109133439) := by norm_num
    nlinarith [hA, hconst]
  rw [div_le_iff₀ hden]
  exact hnum

/-! ## Capstone: the weighted-row log bound implies the constant middle bound -/

/-- Under the weighted row-sum log bound, `HA_Wmid_constant_bound` holds with
`R₀ = 4096` and `C = 0.057082`. -/
theorem HA_Wmid_constant_bound_of_weighted_row_log_bound
    (h : HA_WmidWeightedRowSum_log_bound) :
    HA_Wmid_constant_bound := by
  refine ⟨4096, 0.057082, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : (0.456656 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (0.456656 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have h8 : (0.057082 : ℝ) * 8 = 0.456656 := by norm_num
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hlog]
  · intro R hR x
    have hRpos : 0 < R := by omega
    have hR18 : 18 ≤ R := by omega
    have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hRpos
    have hRreal_ne : (R : ℝ) ≠ 0 := ne_of_gt hRreal_pos
    have hRreal : (4096 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hlogpos : 0 < Real.log (2 * (R : ℝ)) := by
      have h2R_gt_one : (1 : ℝ) < 2 * (R : ℝ) := by nlinarith
      exact Real.log_pos h2R_gt_one
    have hden : 0 < 2 * Real.log (2 * (R : ℝ)) := by positivity
    have hden_ne : 2 * Real.log (2 * (R : ℝ)) ≠ 0 := ne_of_gt hden
    have hWmid : Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) :=
      Wmid_le_WmidWeightedRowSum_div_R R x hRpos
    have hSy : WmidWeightedRowSum R x ≤ (R : ℝ) / (2 * Real.log (2 * (R : ℝ))) :=
      h R hR18 x
    have hdiv : WmidWeightedRowSum R x / (R : ℝ)
        ≤ ((R : ℝ) / (2 * Real.log (2 * (R : ℝ)))) / (R : ℝ) := by
      exact div_le_div_of_nonneg_right hSy (le_of_lt hRreal_pos)
    have hsimp : ((R : ℝ) / (2 * Real.log (2 * (R : ℝ)))) / (R : ℝ)
        = (1 : ℝ) / (2 * Real.log (2 * (R : ℝ))) := by
      field_simp [hRreal_ne, hden_ne]
    have hthresh : (1 : ℝ) / (2 * Real.log (2 * (R : ℝ))) ≤ 0.057082 :=
      one_div_two_mul_log_two_mul_R_le_0_057082 R hR
    calc
      Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := hWmid
      _ ≤ ((R : ℝ) / (2 * Real.log (2 * (R : ℝ)))) / (R : ℝ) := hdiv
      _ = (1 : ℝ) / (2 * Real.log (2 * (R : ℝ))) := hsimp
      _ ≤ 0.057082 := hthresh

/-! ## Final chained theorem -/

/-- Under the weighted row-sum log bound, `x · prodOneSub x` tends to `atTop`. -/
theorem xP_tendsto_atTop_of_weighted_row_log_bound
    (h : HA_WmidWeightedRowSum_log_bound) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  exact xP_tendsto_atTop_of_Wmid_constant_bound
    (HA_Wmid_constant_bound_of_weighted_row_log_bound h)

end

end Erdos291
