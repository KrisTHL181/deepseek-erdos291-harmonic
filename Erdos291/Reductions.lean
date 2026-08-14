import Erdos291.GcdOne
import Erdos291.GcdOneWeak
import Erdos291.SecondMoment

/-!
# Erdős #291 — reduction bookkeeping between the arithmetic hypotheses

This file completes the implication diagram among the arithmetic hypotheses:

  `HA_second_moment ⟹ HA_arith ⟹ HA_arith_weak`.

The first arrow is proved in `SecondMoment.lean` (`HA_arith_of_HA_second_moment`); here we prove
the second (`HA_arith_implies_HA_arith_weak`) and then the composite
(`HA_second_moment_implies_HA_arith_weak`).

The second arrow is elementary: `HA_arith` gives `S x ≤ C · log(log x)` eventually, and since
`log(log x) = o(log x)`, dividing by the (eventually positive) `log x` and squeezing shows
`S x / log x → 0`, which is exactly `HA_arith_weak`.

There are no unproved declarations in this file.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-- `HA_arith` (the bound `S x = O(log log x)`) implies the weak arithmetic hypothesis
`HA_arith_weak` (`S x = o(log x)`): since `log(log x) / log x → 0`, the bound
`S x ≤ C · log(log x)` divided by the (eventually positive) `log x` tends to `0`. -/
theorem HA_arith_implies_HA_arith_weak (h : HA_arith) : HA_arith_weak := by
  rcases h with ⟨C, _hCpos, hbound⟩
  have hSbound : ∀ᶠ x : ℕ in atTop, S x ≤ C * Real.log (Real.log (x : ℝ)) := by
    simpa [S] using hbound
  have hS_nonneg : ∀ x : ℕ, 0 ≤ S x := by
    intro x
    unfold S
    exact Finset.sum_nonneg (fun p _ => c_nonneg p)
  -- lower bound: `0 ≤ S x / log x` eventually
  have hlower : ∀ᶠ x : ℕ in atTop, (0 : ℝ) ≤ S x / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    exact div_nonneg (hS_nonneg x)
      (le_of_lt (Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))))
  -- upper bound: `S x / log x ≤ C · log(log x) / log x` eventually
  have hupper : ∀ᶠ x : ℕ in atTop,
      S x / Real.log (x : ℝ) ≤ C * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by
    filter_upwards [hSbound, eventually_gt_atTop (1 : ℕ)] with x hx hxgt
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hxgt : (1 : ℝ) < (x : ℝ))
    exact div_le_div_of_nonneg_right hx (le_of_lt hlogpos)
  -- `C · log(log x) / log x → 0`
  have hupper_tendsto : Tendsto
      (fun x : ℕ => C * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1
        (by norm_num : (1 : ℝ) ≠ 0))
    have hdiv : Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
      hbase.comp Real.tendsto_log_atTop
    have hdiv_nat : Tendsto
        (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) :=
      hdiv.comp tendsto_natCast_atTop_atTop
    have hmul : Tendsto
        (fun x : ℕ => C * (Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ))) atTop (𝓝 0) := by
      simpa using hdiv_nat.const_mul C
    refine hmul.congr' ?_
    filter_upwards [] with x
    rw [mul_div_assoc]
  exact squeeze_zero' hlower hupper hupper_tendsto

/-- The second-moment hypothesis implies the weak arithmetic hypothesis: compose
`HA_arith_of_HA_second_moment` with `HA_arith_implies_HA_arith_weak`. -/
theorem HA_second_moment_implies_HA_arith_weak (h : HA_second_moment) : HA_arith_weak :=
  HA_arith_implies_HA_arith_weak (HA_arith_of_HA_second_moment h)

end Erdos291
