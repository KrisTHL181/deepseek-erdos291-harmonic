import Erdos291.HAProgress
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős #291 — the Mertens step: `∑_{p ≤ x} c_p → ∞`

This file completes the Mertens step that was left open in `HAProgress.lean`.  The
quantitative goal is the lower bound `∑_{p ≤ x} c_p = Ω(log log x)`; here we establish the
weaker (but unconditional and still essential) divergence statement, namely that the bad-digit
density sum grows without bound:

* `sum_inv_pred_tendsto_atTop`: `∑_{p ≤ x} 1 / (p - 1) → ∞`.
* `sum_c_tendsto_atTop`: `∑_{p ≤ x} c_p → ∞`.

The engine is Euler's theorem `not_summable_one_div_on_primes` (the sum of `1/p` over the
primes diverges), together with the monotonicity of partial sums and the pointwise bounds
`1/(p-1) ≥ 1/p` and `c_p ≥ 1/(p-1)` (the latter from Wolstenholme, `c_ge_inv_pred`).
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

noncomputable section

/-- The indicator of the primes with weight `1/n`, as a function `ℕ → ℝ`. -/
private def primeRecipIndicator : ℕ → ℝ :=
  {p | p.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)

/-- The partial sums `∑_{p < x, p prime} 1/p` tend to `+∞` (Euler). -/
lemma tendsto_sum_one_div_primesBelow_atTop :
    Tendsto (fun x : ℕ => ∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ))) atTop atTop := by
  have hnonneg : ∀ n, 0 ≤ primeRecipIndicator n := by
    intro n
    dsimp [primeRecipIndicator]
    rw [Set.indicator_apply]
    split_ifs with hn
    · exact le_of_lt (one_div_pos.mpr (by exact_mod_cast (Nat.Prime.pos hn)))
    · exact le_rfl
  have hnonsumm : ¬ Summable primeRecipIndicator := by
    simpa [primeRecipIndicator] using not_summable_one_div_on_primes
  have htend : Tendsto (fun n => ∑ i ∈ Finset.range n, primeRecipIndicator i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnonsumm
  refine htend.congr (fun n => ?_)
  calc
    (∑ i ∈ Finset.range n, primeRecipIndicator i)
        = ∑ i ∈ Finset.range n, (if i.Prime then (1 / (i : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [primeRecipIndicator]
            rw [Set.indicator_apply]
            by_cases hi : i.Prime <;> simp [hi]
    _ = ∑ i ∈ (Finset.range n).filter Nat.Prime, (1 / (i : ℝ)) := by
            exact (Finset.sum_filter Nat.Prime (fun i => (1 / (i : ℝ)))).symm
    _ = ∑ p ∈ Nat.primesBelow n, (1 / (p : ℝ)) := by
            rw [← Nat.primesBelow_eq_filter_range n]

/-- `∑_{p < x, prime} 1/p ≤ 1/2 + ∑_{3 ≤ p ≤ x, prime} 1/p`: the only prime below `3` is `2`. -/
lemma sum_one_div_primesBelow_le (x : ℕ) :
    (∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ))) ≤
      (1 / 2 : ℝ) + ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / (p : ℝ)) := by
  have hsub : Nat.primesBelow x ⊆ insert 2 ((Finset.Icc 3 x).filter Nat.Prime) := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hlt : p < x := Nat.lt_of_mem_primesBelow hp
    by_cases hp2 : p = 2
    · simp [hp2]
    · rw [Finset.mem_insert]
      right
      rw [Finset.mem_filter, Finset.mem_Icc]
      have hple2 : 2 ≤ p := hprime.two_le
      exact ⟨⟨by omega, by omega⟩, hprime⟩
  have hsumle : (∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ))) ≤
      ∑ p ∈ insert 2 ((Finset.Icc 3 x).filter Nat.Prime), (1 / (p : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p _ _
    exact div_nonneg zero_le_one (Nat.cast_nonneg p)
  have hnot2 : 2 ∉ (Finset.Icc 3 x).filter Nat.Prime := by
    intro h
    have hIcc : 2 ∈ Finset.Icc 3 x := (Finset.mem_filter.mp h).1
    have : 3 ≤ 2 := (Finset.mem_Icc.mp hIcc).1
    omega
  calc
    (∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ))) ≤
        ∑ p ∈ insert 2 ((Finset.Icc 3 x).filter Nat.Prime), (1 / (p : ℝ)) := hsumle
    _ = (1 / 2 : ℝ) + ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / (p : ℝ)) := by
        rw [Finset.sum_insert hnot2]
        norm_num

/-- `∑_{3 ≤ p ≤ x, prime} 1/p → ∞`. -/
lemma tendsto_sum_one_div_Icc_atTop :
    Tendsto (fun x : ℕ => ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / (p : ℝ))) atTop atTop := by
  have hshift : Tendsto
      (fun x => (∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ))) + (-(1 / 2 : ℝ))) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-(1 / 2 : ℝ)) tendsto_sum_one_div_primesBelow_atTop
  refine tendsto_atTop_mono (fun x => ?_) hshift
  have hle := sum_one_div_primesBelow_le x
  linarith

/-- For `3 ≤ p`, `1/p ≤ 1/(p-1)`. -/
lemma one_div_pred_ge_one_div (p : ℕ) (hp : 3 ≤ p) :
    (1 / (p : ℝ)) ≤ (1 / ((p - 1 : ℕ) : ℝ)) := by
  have hp1pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    have : 0 < p - 1 := by omega
    exact_mod_cast this
  have hppos : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hle : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.sub_le p 1)
  exact (one_div_le_one_div hppos hp1pos).2 hle

/-- `∑ 1/p ≤ ∑ 1/(p-1)` over the primes `3 ≤ p ≤ x`. -/
lemma sum_one_div_le_sum_inv_pred (x : ℕ) :
    (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / (p : ℝ))) ≤
      ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)) := by
  apply Finset.sum_le_sum
  intro p hp
  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact one_div_pred_ge_one_div p hp3

/-- `∑_{p ≤ x} 1/(p-1) → ∞`. -/
theorem sum_inv_pred_tendsto_atTop :
    Tendsto (fun x : ℕ => ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime,
      (1 / ((p - 1 : ℕ) : ℝ))) atTop atTop := by
  refine tendsto_atTop_mono (fun x => sum_one_div_le_sum_inv_pred x) tendsto_sum_one_div_Icc_atTop

/-- For `3 ≤ p`, `1/(p-1) ≤ c p` (the real-cast form of `c_ge_inv_pred`). -/
lemma c_ge_inv_pred_real (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (1 / ((p - 1 : ℕ) : ℝ)) ≤ (c p : ℝ) := by
  have hq := c_ge_inv_pred (p := p) hp
  have hr : (((p - 1 : ℕ) : ℚ)⁻¹ : ℝ) ≤ (c p : ℝ) := by
    exact_mod_cast hq
  simpa [one_div] using hr

/-- `∑ 1/(p-1) ≤ ∑ c p` over the primes `3 ≤ p ≤ x` (real form). -/
lemma sum_inv_pred_le_sum_c (x : ℕ) :
    (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) ≤
      ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (c p : ℝ) := by
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact @c_ge_inv_pred_real p ⟨hpPrime⟩ hp3

/-- `∑_{p ≤ x} c_p → ∞`. -/
theorem sum_c_tendsto_atTop :
    Tendsto (fun x : ℕ => ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (c p : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun x => sum_inv_pred_le_sum_c x) sum_inv_pred_tendsto_atTop

end

end Erdos291
