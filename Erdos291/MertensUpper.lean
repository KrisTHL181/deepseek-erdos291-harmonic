import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Erdős #291 — Mertens' upper bound: `∑_{p ≤ x} 1/p = O(log log x)`

This file proves the *upper* half of the Mertens estimate, complementing the divergence
(`not_summable_one_div_on_primes`) used in `Erdos291.Mertens`.  The theorem is that the sum
of `1/p` over the primes `p < x` is `O(log log x)` with an explicit constant.

The argument is the classical Chebyshev + Abel-summation route:

1. **Chebyshev** `π(x) = O(x / log x)` (here `Chebyshev.pi_le_log4_mul_div`, which gives the
   explicit bound `π x ≤ log 4 · x / log √x + √x`); we absorb the `√x` term to obtain
   `π n ≤ primeCountingConst · n / log n` for `n ≥ 2`.

2. **Abel partial summation** expresses `∑_{p ≤ x} 1/p` as
   `π x / x + ∑_{n < x} π n / (n (n + 1))`.

3. **The log-log step**: `∑_{n ≤ x} 1 / (n log n) ≤ 1/(2 log 2) + log (log x) - log (log 2)`,
   obtained from the antitone sum-integral comparison and the fundamental theorem of calculus
   applied to `log ∘ log` (whose derivative is `1 / (x log x)`).
-/

open Filter
open scoped BigOperators Topology Nat.Prime

namespace Erdos291

noncomputable section

/-- An explicit constant so that `π n ≤ primeCountingConst * n / log n` for every `n ≥ 2`. -/
def primeCountingConst : ℝ := 2 * Real.log 4 + 2

/-- The Chebyshev upper bound `π n ≤ C n / log n` for `n ≥ 2`, with the explicit constant
`primeCountingConst = 2 log 4 + 2`. -/
lemma primeCounting_le_const_div_log (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ primeCountingConst * (n : ℝ) / Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
  have h := Chebyshev.pi_le_log4_mul_div hn1
  have h' : (Nat.primeCounting n : ℝ) ≤
      Real.log 4 * (n : ℝ) / Real.log (Real.sqrt (n : ℝ)) + Real.sqrt (n : ℝ) := by
    simpa using h
  have hsqrt : Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) / 2 :=
    Real.log_sqrt hn0
  have hlog_le_sqrt : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hs := Real.log_le_self (by positivity : (0 : ℝ) ≤ Real.sqrt (n : ℝ))
    rw [Real.log_sqrt hn0] at hs
    nlinarith
  have hmul : Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ 2 * (n : ℝ) := by
    calc
      Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          ≤ Real.sqrt (n : ℝ) * (2 * Real.sqrt (n : ℝ)) := by
            gcongr
      _ = 2 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = 2 * (n : ℝ) := by rw [Real.sq_sqrt hn0]
  have hsq : Real.sqrt (n : ℝ) ≤ 2 * (n : ℝ) / Real.log (n : ℝ) := by
    rw [le_div_iff₀ hlogpos]
    exact hmul
  calc
    (Nat.primeCounting n : ℝ)
        ≤ Real.log 4 * (n : ℝ) / Real.log (Real.sqrt (n : ℝ)) + Real.sqrt (n : ℝ) := h'
    _ = Real.log 4 * (n : ℝ) / (Real.log (n : ℝ) / 2) + Real.sqrt (n : ℝ) := by
          rw [hsqrt]
    _ = (2 * Real.log 4) * (n : ℝ) / Real.log (n : ℝ) + Real.sqrt (n : ℝ) := by
          field_simp [hlogpos.ne']
    _ ≤ (2 * Real.log 4) * (n : ℝ) / Real.log (n : ℝ) + 2 * (n : ℝ) / Real.log (n : ℝ) := by
          gcongr
    _ = primeCountingConst * (n : ℝ) / Real.log (n : ℝ) := by
          simp [primeCountingConst]
          ring

/-- The number of primes `< n` expressed as a sum of indicators over `range n`. -/
lemma sum_range_prime_indicator (n : ℕ) :
    (∑ i ∈ Finset.range n, (if i.Prime then (1 : ℝ) else 0)) =
      (Nat.count Nat.Prime n : ℝ) := by
  rw [← Finset.sum_filter (s := Finset.range n) (p := Nat.Prime) (f := fun _ => (1 : ℝ))]
  simp [Nat.count_eq_card_filter_range]

/-- `¬ p.Prime` for `p ≤ 1`. -/
lemma not_prime_of_le_one {n : ℕ} (hn : n ≤ 1) : ¬ n.Prime := by
  intro hp
  have := Nat.Prime.two_le hp
  omega

/-- `∑_{p ≤ x} 1/p = ∑_{i ∈ Ioc 1 x} [i prime] / i`. -/
lemma sum_primesLE_eq_indicator (x : ℕ) :
    (∑ p ∈ Nat.primesLE x, (1 / (p : ℝ))) =
      ∑ i ∈ Finset.Ioc 1 x, (if i.Prime then (1 / (i : ℝ)) else 0) := by
  rw [Nat.primesLE_eq_filter_Ioc_one]
  rw [Finset.sum_filter]

/-- Abel partial summation: `∑_{p ≤ x} 1/p = π x / x + ∑_{n < x} π n / (n (n+1))`. -/
lemma sum_one_div_primesLE_eq (x : ℕ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE x, (1 / (p : ℝ))) =
      (Nat.primeCounting x : ℝ) / (x : ℝ) +
        ∑ i ∈ Finset.Ioc 1 (x - 1), (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ)) := by
  rw [sum_primesLE_eq_indicator x]
  let f : ℕ → ℝ := fun i => 1 / (i : ℝ)
  let g : ℕ → ℝ := fun i => if i.Prime then 1 else 0
  have hGx : (∑ i ∈ Finset.range (x + 1), g i) = (Nat.primeCounting x : ℝ) := by
    dsimp [g]; rw [sum_range_prime_indicator]; rfl
  have hG2 : (∑ i ∈ Finset.range 2, g i) = 0 := by
    dsimp [g]; rw [Finset.sum_range_succ]; simp [not_prime_of_le_one]
  have hGi : ∀ i, (∑ j ∈ Finset.range (i + 1), g j) = (Nat.primeCounting i : ℝ) := by
    intro i; dsimp [g]; rw [sum_range_prime_indicator]; rfl
  have habel := Finset.sum_Ioc_by_parts f g (by omega : 1 < x)
  rw [hGx, hG2] at habel
  simp only [hGi, smul_eq_mul] at habel
  calc
    (∑ i ∈ Finset.Ioc 1 x, (if i.Prime then (1 / (i : ℝ)) else 0))
        = ∑ i ∈ Finset.Ioc 1 x, f i * g i := by
            apply Finset.sum_congr rfl; intro i _; simp [f, g]
    _ = f x * (Nat.primeCounting x : ℝ) -
          ∑ i ∈ Finset.Ioc 1 (x - 1), (f (i + 1) - f i) * (Nat.primeCounting i : ℝ) := by
            rw [habel]; simp
    _ = (Nat.primeCounting x : ℝ) / (x : ℝ) +
          ∑ i ∈ Finset.Ioc 1 (x - 1), (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ)) := by
            dsimp [f]
            rw [show (1 / (x : ℝ)) * (Nat.primeCounting x : ℝ) = (Nat.primeCounting x : ℝ) / (x : ℝ) by ring]
            rw [sub_eq_add_neg]
            rw [← Finset.sum_neg_distrib]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            have hi2 : 2 ≤ i := by have hi' := Finset.mem_Ioc.mp hi; omega
            have hi_ne : (i : ℝ) ≠ 0 := by positivity
            rw [show ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 by norm_num]
            field_simp [hi_ne]
            ring

/-- `1 / (t log t)` is antitone on `[2, ∞)`. -/
lemma antitone_one_div_mul_log :
    AntitoneOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Ici 2) := by
  intro a ha b hb hab
  have ha2 : (2 : ℝ) ≤ a := ha
  have hapos : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ha2
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hb
  have hlog_nonneg_a : 0 ≤ Real.log a := le_of_lt (Real.log_pos (by linarith : (1 : ℝ) < a))
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log hapos hab
  have hle : a * Real.log a ≤ b * Real.log b := by
    have h1 := mul_le_mul_of_nonneg_right hab hlog_nonneg_a
    have h2 := mul_le_mul_of_nonneg_left hlog (le_of_lt hbpos)
    nlinarith
  have hpos : 0 < a * Real.log a := mul_pos hapos (Real.log_pos (by linarith : (1 : ℝ) < a))
  exact one_div_le_one_div_of_le hpos hle

/-- `∫_2^N dt/(t log t) = log(log N) - log(log 2)` for `N ≥ 2`. -/
lemma integral_one_div_mul_log (N : ℕ) (hN : 2 ≤ N) :
    ∫ t in (2 : ℝ)..(N : ℝ), (1 / (t * Real.log t)) =
      Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
  have hmain : (∫ t in (2 : ℝ)..(N : ℝ), (t⁻¹ / Real.log t)) =
      Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
    refine intervalIntegral.integral_deriv_eq_sub' (fun x : ℝ => Real.log (Real.log x))
      (f' := fun x => x⁻¹ / Real.log x) ?_ ?_ ?_
    · exact Real.deriv_log_log
    · intro x hx
      have hx2 : (2 : ℝ) ≤ x := by
        have hx' : x ∈ Set.Icc (2 : ℝ) (N : ℝ) := by
          simpa [Set.uIcc_of_le (by exact_mod_cast hN : (2 : ℝ) ≤ N)] using hx
        exact hx'.1
      apply Real.differentiableAt_log_log <;> linarith
    · rw [Set.uIcc_of_le (by exact_mod_cast hN : (2 : ℝ) ≤ N)]
      refine ContinuousOn.div (continuousOn_inv₀.mono ?_) (Real.continuousOn_log.mono ?_) ?_
      · intro x hx
        exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
      · intro x hx
        exact (show (0 : ℝ) < x by linarith [hx.1]).ne'
      · intro x hx
        exact (Real.log_pos (by linarith [hx.1] : (1 : ℝ) < x)).ne'
  convert hmain using 1
  apply intervalIntegral.integral_congr
  intro t _
  change (1 / (t * Real.log t)) = t⁻¹ / Real.log t
  rw [one_div, mul_inv_rev, div_eq_mul_inv, mul_comm]

/-- `∑_{n = 2}^N 1/(n log n) ≤ 1/(2 log 2) + log(log N) - log(log 2)` for `N ≥ 2`. -/
lemma sum_inv_mul_log_le (N : ℕ) (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (1 / ((n : ℝ) * Real.log (n : ℝ))))
      ≤ 1 / (2 * Real.log 2) + Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.Icc 2 (N : ℝ)) :=
    antitone_one_div_mul_log.mono (Set.Icc_subset_Ici_self)
  have hcomp : (∑ i ∈ Finset.Ico 2 N, (1 / (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ))))
      ≤ ∫ t in (2 : ℝ)..(N : ℝ), (1 / (t * Real.log t)) :=
    AntitoneOn.sum_le_integral_Ico (by exact hN : (2 : ℕ) ≤ N) hanti
  have hsum : (∑ n ∈ Finset.Icc 2 N, (1 / ((n : ℝ) * Real.log (n : ℝ))))
      = 1 / (2 * Real.log 2) + ∑ i ∈ Finset.Ico 2 N,
          (1 / (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ))) := by
    rw [show Finset.Icc 2 N = insert 2 (Finset.Ioc 2 N) by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_insert]; omega]
    rw [Finset.sum_insert]
    · rw [show (↑(2 : ℕ) : ℝ) = (2 : ℝ) by norm_num]
      congr 1
      rw [show Finset.Ioc 2 N = Finset.Ico 3 (N + 1) by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega]
      rw [← Finset.sum_Ico_add (f := fun n : ℕ => 1 / ((n : ℝ) * Real.log (n : ℝ))) 2 N 1]
      apply Finset.sum_congr rfl
      intro i _
      simp [Nat.cast_add, Nat.cast_one, add_comm]
    · rw [Finset.mem_Ioc]; omega
  rw [hsum]
  have hint : (∑ i ∈ Finset.Ico 2 N, (1 / (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ))))
      ≤ Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
    calc
      (∑ i ∈ Finset.Ico 2 N, (1 / (((i + 1 : ℕ) : ℝ) * Real.log ((i + 1 : ℕ) : ℝ))))
          ≤ ∫ t in (2 : ℝ)..(N : ℝ), (1 / (t * Real.log t)) := hcomp
      _ = Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := integral_one_div_mul_log N hN
  linarith [hint]

/-- Mertens' upper bound with an explicit constant: `∑_{p < x} 1/p ≤ C (1 + log log x)`. -/
theorem sum_one_div_primes_le_loglog :
    ∃ C : ℝ, ∀ x : ℕ, 3 ≤ x →
      (∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ))) ≤ C * (1 + Real.log (Real.log (x : ℝ))) := by
  refine ⟨primeCountingConst * (4 / Real.log 2), ?_⟩
  intro x hx
  have hx2 : 2 ≤ x := by omega
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 3) hx)
  have hxpos : 0 < (x : ℝ) := by positivity
  have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hloglogx_nonneg : 0 ≤ Real.log (Real.log (x : ℝ)) := by
    have h3e : (3 : ℝ) > Real.exp 1 := by
      have h := Real.exp_lt_two_add_div_two_sub (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
      norm_num at h
      exact h
    have hlogx_gt_one : (1 : ℝ) < Real.log (x : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < x)]
      exact lt_of_lt_of_le h3e (by exact_mod_cast hx : (3 : ℝ) ≤ x)
    exact le_of_lt (Real.log_pos hlogx_gt_one)
  -- Abel partial summation
  have habel := sum_one_div_primesLE_eq x hx2
  let C0 := primeCountingConst
  have hC0pos : 0 ≤ C0 := by
    dsimp [C0, primeCountingConst]
    positivity
  -- π x / x ≤ C0 / log x
  have hbound1 : (Nat.primeCounting x : ℝ) / (x : ℝ) ≤ C0 / Real.log (x : ℝ) := by
    have hpi := primeCounting_le_const_div_log x hx2
    have : primeCountingConst * (x : ℝ) / Real.log (x : ℝ) / (x : ℝ) = primeCountingConst / Real.log (x : ℝ) := by
      field_simp [hxpos.ne', hlogxpos.ne']
    rw [← this]
    exact div_le_div_of_nonneg_right hpi (le_of_lt hxpos)
  -- bound the Abel sum
  have hbound2 : (∑ i ∈ Finset.Ioc 1 (x - 1), (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ)))
      ≤ C0 * (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
    have hterm : ∀ i ∈ Finset.Ioc 1 (x - 1),
        (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ))
          ≤ C0 * (1 / ((i : ℝ) * Real.log (i : ℝ))) := by
      intro i hi
      have hi2 : 2 ≤ i := by
        have hi' := Finset.mem_Ioc.mp hi
        omega
      have hpi := primeCounting_le_const_div_log i hi2
      have hipos : 0 < (i : ℝ) := by positivity
      have hi1pos : 0 < (i : ℝ) + 1 := by positivity
      have hilogpos : 0 < Real.log (i : ℝ) := Real.log_pos (by exact_mod_cast hi2)
      calc
        (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ))
            ≤ (primeCountingConst * (i : ℝ) / Real.log (i : ℝ)) / ((i : ℝ) * (i + 1 : ℝ)) := by
                gcongr
        _ = primeCountingConst / (((i : ℝ) + 1) * Real.log (i : ℝ)) := by
                field_simp [hipos.ne', hi1pos.ne', hilogpos.ne']
        _ ≤ C0 * (1 / ((i : ℝ) * Real.log (i : ℝ))) := by
                dsimp [C0]
                have hle : ((i : ℝ) + 1) * Real.log (i : ℝ) ≥ (i : ℝ) * Real.log (i : ℝ) := by
                  nlinarith [hilogpos]
                rw [div_eq_mul_one_div]
                gcongr
    have hsum_bound : (∑ i ∈ Finset.Ioc 1 (x - 1), (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ)))
        ≤ ∑ i ∈ Finset.Ioc 1 (x - 1), C0 * (1 / ((i : ℝ) * Real.log (i : ℝ))) := by
      exact Finset.sum_le_sum (fun i hi => hterm i hi)
    have hreindex : (∑ i ∈ Finset.Ioc 1 (x - 1), C0 * (1 / ((i : ℝ) * Real.log (i : ℝ))))
        = C0 * (∑ n ∈ Finset.Icc 2 (x - 1), (1 / ((n : ℝ) * Real.log (n : ℝ)))) := by
      rw [Finset.mul_sum]
      rw [show Finset.Ioc 1 (x - 1) = Finset.Icc 2 (x - 1) by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
    have hsumlog := sum_inv_mul_log_le (x - 1) (by omega : 2 ≤ x - 1)
    have hlogxm1_le_logx : Real.log (Real.log ((x - 1 : ℕ) : ℝ)) ≤ Real.log (Real.log (x : ℝ)) := by
      have hxm1_pos : 0 < (x - 1 : ℕ) := by omega
      have hxm1_le : (x - 1 : ℕ) ≤ x := Nat.sub_le x 1
      have h1 : Real.log ((x - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) :=
        Real.log_le_log (by exact_mod_cast hxm1_pos) (by exact_mod_cast hxm1_le)
      have h2 : 0 < Real.log ((x - 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < x - 1))
      exact Real.log_le_log h2 h1
    calc
      (∑ i ∈ Finset.Ioc 1 (x - 1), (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ)))
          ≤ ∑ i ∈ Finset.Ioc 1 (x - 1), C0 * (1 / ((i : ℝ) * Real.log (i : ℝ))) := hsum_bound
      _ = C0 * (∑ n ∈ Finset.Icc 2 (x - 1), (1 / ((n : ℝ) * Real.log (n : ℝ)))) := hreindex
      _ ≤ C0 * (1 / (2 * Real.log 2) + Real.log (Real.log ((x - 1 : ℕ) : ℝ)) - Real.log (Real.log 2)) := by
            exact mul_le_mul_of_nonneg_left hsumlog hC0pos
      _ ≤ C0 * (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
            gcongr
  -- final assembly
  have hC0_div : C0 / Real.log (x : ℝ) ≤ C0 / Real.log 2 := by
    have hlog2_le_logx : Real.log 2 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hx2 : (2 : ℝ) ≤ x)
    have h1 : (Real.log (x : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ := by
      rw [inv_le_inv₀ hlogxpos hlog2pos]
      exact hlog2_le_logx
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left h1 hC0pos
  have htotal : (∑ p ∈ Nat.primesLE x, (1 / (p : ℝ))) ≤
      C0 * (1 / Real.log 2 + 1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∑ p ∈ Nat.primesLE x, (1 / (p : ℝ)))
          = (Nat.primeCounting x : ℝ) / (x : ℝ) +
              ∑ i ∈ Finset.Ioc 1 (x - 1), (Nat.primeCounting i : ℝ) / ((i : ℝ) * (i + 1 : ℝ)) := habel
      _ ≤ C0 / Real.log (x : ℝ) + C0 * (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
            gcongr
      _ ≤ C0 / Real.log 2 + C0 * (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
            exact add_le_add hC0_div le_rfl
      _ = C0 * (1 / Real.log 2 + 1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
            ring
  -- now show this is ≤ C0 * (4/log2) * (1 + log log x)
  have hfinal :
      C0 * (1 / Real.log 2 + 1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2))
        ≤ C0 * (4 / Real.log 2) * (1 + Real.log (Real.log (x : ℝ))) := by
    have hA : (1 / Real.log 2 + 1 / (2 * Real.log 2) - Real.log (Real.log 2)) ≤ 4 / Real.log 2 := by
      have hneg : -Real.log (Real.log 2) ≤ 1 / Real.log 2 := by
        have hle := Real.log_le_self (by positivity : (0 : ℝ) ≤ (1 / Real.log 2))
        simpa [one_div, Real.log_inv (Real.log 2)] using hle
      have hhalf : 1 / (2 * Real.log 2) ≤ 1 / Real.log 2 :=
        one_div_le_one_div_of_le hlog2pos (by nlinarith [hlog2pos])
      calc
        (1 / Real.log 2 + 1 / (2 * Real.log 2) - Real.log (Real.log 2))
            = 1 / (2 * Real.log 2) + (1 / Real.log 2 + (-Real.log (Real.log 2))) := by ring
        _ ≤ 1 / Real.log 2 + (1 / Real.log 2 + 1 / Real.log 2) := by
              nlinarith [hneg, hhalf]
        _ ≤ 4 / Real.log 2 := by
              have hApos : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
              rw [show (1 / Real.log 2 + (1 / Real.log 2 + 1 / Real.log 2)) = 3 * (1 / Real.log 2) by ring]
              rw [show 4 / Real.log 2 = 4 * (1 / Real.log 2) by ring]
              exact mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) hApos
    calc
      C0 * (1 / Real.log 2 + 1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2))
          = C0 * ((1 / Real.log 2 + 1 / (2 * Real.log 2) - Real.log (Real.log 2)) + Real.log (Real.log (x : ℝ))) := by
                ring
      _ ≤ C0 * (4 / Real.log 2 + (4 / Real.log 2) * Real.log (Real.log (x : ℝ))) := by
            gcongr
            · have hle1 : (1 : ℝ) ≤ 4 / Real.log 2 := by
                rw [le_div_iff₀ hlog2pos]
                linarith [Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)]
              nlinarith [hle1, hloglogx_nonneg]
      _ = C0 * (4 / Real.log 2) * (1 + Real.log (Real.log (x : ℝ))) := by
            ring
  -- combine and relate primesBelow to primesLE
  calc
    (∑ p ∈ Nat.primesBelow x, (1 / (p : ℝ)))
        ≤ ∑ p ∈ Nat.primesLE x, (1 / (p : ℝ)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro p hp
            rw [Nat.mem_primesLE]
            rw [Nat.mem_primesBelow] at hp
            exact ⟨le_of_lt hp.1, hp.2⟩
          · intro p _ _
            exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ p)
    _ ≤ C0 * (1 / Real.log 2 + 1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := htotal
    _ ≤ primeCountingConst * (4 / Real.log 2) * (1 + Real.log (Real.log (x : ℝ))) := by
          simpa [C0] using hfinal

end

end Erdos291
