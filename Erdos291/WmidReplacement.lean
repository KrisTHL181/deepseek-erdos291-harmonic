import Erdos291.WmidBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Replacement hypotheses for `HA_WmidWeightedRowSum_log_bound`

The capstone in `WmidBound` only needs an eventual constant bound for `Wmid`.
This file records two alternative hypotheses that are each numerically
supported (see the C/Python scans) and each close the final goal through
`HA_Wmid_constant_bound_of_weighted_row_log_bound`-style reasoning.

1. `HA_WmidWeightedRowSum_log_bound_049`: the slightly sharper logarithmic
   bound `Sy R x ≤ 0.49·R / log(2R)` for `R ≥ 18`.  Data max of
   `(Sy/R)·log(2R)` over `R ≤ 3184` is `0.484791 < 0.49`.

2. `HA_WmidWeightedRowSum_constant_bound_005`: the constant bound
   `Sy R x ≤ 0.05·R` for `R ≥ 4096`.  Data suffix max of `Sy/R` over
   `R ≥ 4096` (checked through `R = 9998`) is `0.047450 < 0.05`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- Hypothesis: `Sy ≤ 0.49·R/log(2R)` for `R ≥ 18`. -/
def HA_WmidWeightedRowSum_log_bound_049 : Prop :=
  ∀ R : ℕ, 18 ≤ R → ∀ x : ℕ,
    WmidWeightedRowSum R x ≤ (0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))

/-- Hypothesis: `Sy ≤ 0.05·R` for `R ≥ 4096`. -/
def HA_WmidWeightedRowSum_constant_bound_005 : Prop :=
  ∀ R : ℕ, 4096 ≤ R → ∀ x : ℕ,
    WmidWeightedRowSum R x ≤ 0.05 * (R : ℝ)

/-- For `R ≥ 4096`, `0.49/log(2R) ≤ 0.057082`.
Uses `8192 = 2^13` and `0.6931471803 < log 2`. -/
lemma zeroPointFourNine_div_log_two_mul_R_le_0_057082 (R : ℕ) (hR : 4096 ≤ R) :
    (0.49 : ℝ) / Real.log (2 * (R : ℝ)) ≤ 0.057082 := by
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
  have hloglow : (9.0109133439 : ℝ) < Real.log (2 * (R : ℝ)) := by
    rw [hlog8192] at hlogmono
    nlinarith [hlogmono, hlog2gt]
  have hlogpos : 0 < Real.log (2 * (R : ℝ)) := by nlinarith [hloglow]
  have hnum : (0.49 : ℝ) ≤ 0.057082 * Real.log (2 * (R : ℝ)) := by
    have hconst : (0.49 : ℝ) < 0.057082 * 9.0109133439 := by norm_num
    nlinarith [hloglow, hconst]
  rw [div_le_iff₀ hlogpos]
  exact hnum

/-- The 0.49 log-bound implies the direct middle-block constant bound. -/
theorem HA_Wmid_constant_bound_of_weighted_row_log_bound_049
    (h : HA_WmidWeightedRowSum_log_bound_049) :
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
    have hlogne : Real.log (2 * (R : ℝ)) ≠ 0 := ne_of_gt hlogpos
    have hWmid : Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) :=
      Wmid_le_WmidWeightedRowSum_div_R R x hRpos
    have hSy : WmidWeightedRowSum R x ≤ (0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ)) :=
      h R hR18 x
    have hdiv : WmidWeightedRowSum R x / (R : ℝ)
        ≤ ((0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))) / (R : ℝ) := by
      exact div_le_div_of_nonneg_right hSy (le_of_lt hRreal_pos)
    have hsimp : ((0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))) / (R : ℝ)
        = (0.49 : ℝ) / Real.log (2 * (R : ℝ)) := by
      field_simp [hRreal_ne, hlogne]
    have hthresh : (0.49 : ℝ) / Real.log (2 * (R : ℝ)) ≤ 0.057082 :=
      zeroPointFourNine_div_log_two_mul_R_le_0_057082 R hR
    calc
      Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := hWmid
      _ ≤ ((0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))) / (R : ℝ) := hdiv
      _ = (0.49 : ℝ) / Real.log (2 * (R : ℝ)) := hsimp
      _ ≤ 0.057082 := hthresh

/-- The constant 0.05 bound implies the direct middle-block constant bound
(with the better constant `C = 0.05`). -/
theorem HA_Wmid_constant_bound_of_weighted_row_constant_bound_005
    (h : HA_WmidWeightedRowSum_constant_bound_005) :
    HA_Wmid_constant_bound := by
  refine ⟨4096, 0.05, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : (0.4 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (0.4 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have h8 : (0.05 : ℝ) * 8 = 0.4 := by norm_num
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hlog]
  · intro R hR x
    have hRpos : 0 < R := by omega
    have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hRpos
    have hWmid : Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) :=
      Wmid_le_WmidWeightedRowSum_div_R R x hRpos
    have hSy : WmidWeightedRowSum R x ≤ 0.05 * (R : ℝ) := h R hR x
    have hdiv : WmidWeightedRowSum R x / (R : ℝ) ≤ (0.05 * (R : ℝ)) / (R : ℝ) := by
      exact div_le_div_of_nonneg_right hSy (le_of_lt hRreal_pos)
    have hsimp : (0.05 * (R : ℝ)) / (R : ℝ) = 0.05 := by
      field_simp [ne_of_gt hRreal_pos]
    calc
      Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := hWmid
      _ ≤ (0.05 * (R : ℝ)) / (R : ℝ) := hdiv
      _ = 0.05 := hsimp

/-- The 0.49 log-bound closes the final goal. -/
theorem xP_tendsto_atTop_of_weighted_row_log_bound_049
    (h : HA_WmidWeightedRowSum_log_bound_049) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  exact xP_tendsto_atTop_of_Wmid_constant_bound
    (HA_Wmid_constant_bound_of_weighted_row_log_bound_049 h)

/-- The constant 0.05 bound closes the final goal. -/
theorem xP_tendsto_atTop_of_weighted_row_constant_bound_005
    (h : HA_WmidWeightedRowSum_constant_bound_005) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  exact xP_tendsto_atTop_of_Wmid_constant_bound
    (HA_Wmid_constant_bound_of_weighted_row_constant_bound_005 h)

lemma zeroPointFourNine_div_log_two_mul_R_le_0_055 (R : ℕ) (hR : 4096 ≤ R) :
    (0.49 : ℝ) / Real.log (2 * (R : ℝ)) ≤ 0.055 := by
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
  have hloglow : (9.0109133439 : ℝ) < Real.log (2 * (R : ℝ)) := by
    rw [hlog8192] at hlogmono
    nlinarith [hlogmono, hlog2gt]
  have hlogpos : 0 < Real.log (2 * (R : ℝ)) := by nlinarith [hloglow]
  have hnum : (0.49 : ℝ) ≤ 0.055 * Real.log (2 * (R : ℝ)) := by
    have hconst : (0.49 : ℝ) < 0.055 * 9.0109133439 := by norm_num
    nlinarith [hloglow, hconst]
  rw [div_le_iff₀ hlogpos]
  exact hnum

theorem HA_Wmid_constant_bound_of_weighted_row_log_bound_049_stronger
    (h : HA_WmidWeightedRowSum_log_bound_049) : HA_Wmid_constant_bound := by
  refine ⟨4096, 0.055, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : (0.44 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (0.44 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have h8 : (0.055 : ℝ) * 8 = 0.44 := by norm_num
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
    have hlogne : Real.log (2 * (R : ℝ)) ≠ 0 := ne_of_gt hlogpos
    have hWmid : Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) :=
      Wmid_le_WmidWeightedRowSum_div_R R x hRpos
    have hSy : WmidWeightedRowSum R x ≤ (0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ)) :=
      h R hR18 x
    have hdiv : WmidWeightedRowSum R x / (R : ℝ)
        ≤ ((0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))) / (R : ℝ) := by
      exact div_le_div_of_nonneg_right hSy (le_of_lt hRreal_pos)
    have hsimp : ((0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))) / (R : ℝ)
        = (0.49 : ℝ) / Real.log (2 * (R : ℝ)) := by
      field_simp [hRreal_ne, hlogne]
    have hthresh : (0.49 : ℝ) / Real.log (2 * (R : ℝ)) ≤ 0.055 :=
      zeroPointFourNine_div_log_two_mul_R_le_0_055 R hR
    calc
      Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := hWmid
      _ ≤ ((0.49 * (R : ℝ)) / Real.log (2 * (R : ℝ))) / (R : ℝ) := hdiv
      _ = (0.49 : ℝ) / Real.log (2 * (R : ℝ)) := hsimp
      _ ≤ 0.055 := hthresh

def HA_WmidWeightedRowSum_replacement : Prop :=
  HA_WmidWeightedRowSum_log_bound_049 ∧ HA_WmidWeightedRowSum_constant_bound_005

theorem HA_Wmid_constant_bound_of_replacement (h : HA_WmidWeightedRowSum_replacement) :
    HA_Wmid_constant_bound :=
  HA_Wmid_constant_bound_of_weighted_row_constant_bound_005 h.2

theorem xP_tendsto_atTop_of_replacement (h : HA_WmidWeightedRowSum_replacement) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop :=
  xP_tendsto_atTop_of_Wmid_constant_bound (HA_Wmid_constant_bound_of_replacement h)

end Erdos291
