import Erdos291.SecondMoment
import Erdos291.GcdOneWeak
import Erdos291.Reductions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Instances.Nat

/-!
# Erdős #291 — weakening the second-moment hypothesis

This file weakens the second-moment hypothesis `M x = O(log log x)` (recorded in
`SecondMoment.lean` as `HA_second_moment`) to the much weaker hypothesis `M x = o(log x)`,

  `HA_second_weak := Tendsto (fun x : ℕ => M x / log x) atTop (𝓝 0)`,

and shows that *already this weaker hypothesis implies* the weak arithmetic hypothesis
`HA_arith_weak` (`S x = o(log x)`), by-passing the strong arithmetic hypothesis
`HA_arith` (`S x = O(log log x)`) entirely.

The argument is elementary.  Writing `M x` for the second factorial moment and using the
pointwise bound `S x ≤ Σ_{p ≤ x} 1/(p - 1) + M x` (`S_le_sum_inv_pred_add_M`) together
with Mertens' bound `Σ_{p ≤ x} 1/(p - 1) = O(log log x)` (`sum_inv_pred_le_loglog`), we get
eventually

  `S x / log x ≤ C₁ · (1 + log(log x)) / log x + M x / log x`.

Both summands on the right tend to `0` (`(1 + log log x)/log x → 0` is the fact that
`log log x = o(log x)`, and `M x / log x → 0` is exactly `HA_second_weak`), so squeezing
against the nonnegative lower bound `0 ≤ S x / log x` gives `HA_arith_weak`.

We also record that `HA_second_weak` is strictly weaker than `HA_second_moment`: the
implication `HA_second_moment → HA_second_weak` is the same `log log x = o(log x)` fact.

There are no unproved declarations in this file.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-! ## The weakened second-moment hypothesis -/

/-- The weakened second-moment hypothesis: `M x = o(log x)`, i.e. `M x / log x → 0`. -/
def HA_second_weak : Prop :=
  Tendsto (fun x : ℕ => M x / Real.log (x : ℝ)) atTop (𝓝 0)

/-! ## Analytic ingredients: `(1 + log log x)/log x → 0` -/

/-- For a natural number `n`, `n · (n - 1) ≥ 0` as reals (used to see `M x ≥ 0`). -/
lemma natCast_mul_sub_one_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  by_cases hn : n = 0
  · subst n
    norm_num
  · have h1 : 1 ≤ n := by omega
    have hc1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have hdiff : 0 ≤ (n : ℝ) - 1 := by linarith
    exact mul_nonneg (Nat.cast_nonneg n) hdiff

/-- `M x` is nonnegative for every `x`. -/
lemma M_nonneg (x : ℕ) : 0 ≤ M x := by
  unfold M
  apply Finset.sum_nonneg
  intro p hp
  have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hden : 0 < ((p - 1 : ℕ) : ℝ) := by
    have : 0 < p - 1 := by omega
    exact_mod_cast this
  exact div_nonneg (natCast_mul_sub_one_nonneg (E p).card) (le_of_lt hden)

/-- `(1 + log(log x))/log x → 0` along `ℕ`: this is the statement `log(log x) = o(log x)`.
The key ingredient is `log u / u → 0` (`Real.tendsto_pow_log_div_mul_add_atTop`) composed with
`log x → ∞` (`Real.tendsto_log_atTop`), plus `1 / log x → 0`. -/
lemma one_add_loglog_div_log_tendsto_zero :
    Tendsto (fun x : ℕ => (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1
      (by norm_num : (1 : ℝ) ≠ 0))
  have hdiv : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
    hbase.comp Real.tendsto_log_atTop
  have hdiv_nat : Tendsto
      (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) :=
    hdiv.comp tendsto_natCast_atTop_atTop
  have hone_div : Tendsto (fun x : ℕ => (1 : ℝ) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    refine hlog.inv_tendsto_atTop.congr' ?_
    filter_upwards [] with x
    exact (one_div (Real.log (x : ℝ))).symm
  have hsum : Tendsto (fun x : ℕ => (1 : ℝ) / Real.log (x : ℝ) +
        Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    simpa using hone_div.add hdiv_nat
  refine hsum.congr' ?_
  filter_upwards [] with x
  exact (add_div (1 : ℝ) (Real.log (Real.log (x : ℝ))) (Real.log (x : ℝ))).symm

/-- For any constant `C`, `C · (1 + log(log x))/log x → 0` along `ℕ`. -/
lemma const_mul_one_add_loglog_div_log_tendsto_zero (C : ℝ) :
    Tendsto (fun x : ℕ => C * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ)) atTop (𝓝 0) := by
  have hmul : Tendsto
      (fun x : ℕ => C * ((1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ))) atTop (𝓝 0) := by
    simpa using one_add_loglog_div_log_tendsto_zero.const_mul C
  refine hmul.congr' ?_
  filter_upwards [] with x
  rw [mul_div_assoc]

/-! ## The weak reduction `HA_second_weak → HA_arith_weak` -/

/-- The weakened second-moment hypothesis `M x = o(log x)` implies the weak arithmetic
hypothesis `S x = o(log x)`: since `S x ≤ Σ 1/(p - 1) + M x` and `Σ 1/(p - 1) = O(log log x)`,
dividing by the (eventually positive) `log x` and squeezing against `0 ≤ S x / log x` gives
`S x / log x → 0`. -/
theorem HA_arith_weak_of_HA_second_weak (hM : HA_second_weak) : HA_arith_weak := by
  unfold HA_arith_weak
  rcases sum_inv_pred_le_loglog with ⟨C₁, _hC1pos, hC₁⟩
  have hS_nonneg : ∀ x : ℕ, 0 ≤ S x := by
    intro x
    unfold S
    exact Finset.sum_nonneg (fun p _ => c_nonneg p)
  have hlower : ∀ᶠ x : ℕ in atTop, (0 : ℝ) ≤ S x / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    exact div_nonneg (hS_nonneg x)
      (le_of_lt (Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))))
  have hupper : ∀ᶠ x : ℕ in atTop,
      S x / Real.log (x : ℝ) ≤
        C₁ * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) + M x / Real.log (x : ℝ) := by
    filter_upwards [hC₁, eventually_gt_atTop (1 : ℕ)] with x hC1x hxgt
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hxgt : (1 : ℝ) < (x : ℝ))
    have hSle : S x ≤ C₁ * (1 + Real.log (Real.log (x : ℝ))) + M x :=
      (S_le_sum_inv_pred_add_M x).trans (add_le_add hC1x (le_refl (M x)))
    have hdivle : S x / Real.log (x : ℝ) ≤
        (C₁ * (1 + Real.log (Real.log (x : ℝ))) + M x) / Real.log (x : ℝ) :=
      div_le_div_of_nonneg_right hSle (le_of_lt hlogpos)
    have hadd : (C₁ * (1 + Real.log (Real.log (x : ℝ))) + M x) / Real.log (x : ℝ) =
        C₁ * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) + M x / Real.log (x : ℝ) := by
      rw [add_div]
    calc
      S x / Real.log (x : ℝ) ≤
          (C₁ * (1 + Real.log (Real.log (x : ℝ))) + M x) / Real.log (x : ℝ) := hdivle
      _ = C₁ * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) + M x / Real.log (x : ℝ) := hadd
  have hupper_tendsto : Tendsto
      (fun x : ℕ => C₁ * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) + M x / Real.log (x : ℝ))
      atTop (𝓝 0) := by
    simpa using (const_mul_one_add_loglog_div_log_tendsto_zero C₁).add hM
  exact squeeze_zero' hlower hupper hupper_tendsto

/-! ## `HA_second_weak` is weaker than `HA_second_moment` -/

/-- The second-moment hypothesis `M x = O(log log x)` implies the weakened hypothesis
`M x = o(log x)`: since `M x ≤ C · (1 + log log x)` and `0 ≤ M x`, dividing by `log x` and
using `(1 + log log x)/log x → 0` gives `M x / log x → 0`. -/
theorem HA_second_weak_of_HA_second_moment (h : HA_second_moment) : HA_second_weak := by
  unfold HA_second_weak
  rcases h with ⟨C, _hCpos, hbound⟩
  have hlower : ∀ᶠ x : ℕ in atTop, (0 : ℝ) ≤ M x / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    exact div_nonneg (M_nonneg x)
      (le_of_lt (Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))))
  have hupper : ∀ᶠ x : ℕ in atTop,
      M x / Real.log (x : ℝ) ≤
        C * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) := by
    filter_upwards [hbound, eventually_gt_atTop (1 : ℕ)] with x hMx hxgt
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hxgt : (1 : ℝ) < (x : ℝ))
    exact div_le_div_of_nonneg_right hMx (le_of_lt hlogpos)
  exact squeeze_zero' hlower hupper (const_mul_one_add_loglog_div_log_tendsto_zero C)

end Erdos291
