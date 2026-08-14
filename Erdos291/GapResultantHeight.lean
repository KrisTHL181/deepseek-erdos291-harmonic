import Erdos291.GapResultant
import Erdos291.GapCoprime
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Erdős #291 — the resultant has summable exceptional-prime mass

For a fixed pair of distances `d ≠ e`, `GapResultant` shows that any prime `p` realizing a
triple bad-position pattern `r, r + d, r + e ∈ E p` divides the fixed nonzero integer
`resultant (Qd d) (Qd e)`, and `GapCoprime` shows that this integer is nonzero.  This file
upgrades the resulting *qualitative* finiteness statement to a *quantitative* one: the
reciprocal mass of the prime divisors of `resultant (Qd d) (Qd e)` that exceed a threshold `Y`
is `≤ log N / (Y · log Y)`, uniformly in `Y ≥ 2`.

The engine is the elementary prime-divisor-mass lemma `sum_inv_prime_divisors_gt_le`: for any
nonzero `N : ℕ`, the primes `p > Y` dividing `N` have `∏ p ∣ N`, hence `Y^(S.card) ≤ N`, giving
`S.card ≤ log N / log Y`, and since each such prime is `≥ Y` their reciprocal mass is at most
`S.card / Y ≤ log N / (Y log Y)`.  The instantiation `exceptional_prime_mass_le` applies this
with `N = Int.natAbs (resultant (Qd d) (Qd e))`, using `resultant_Qd_ne_zero` for the nonvanishing.
-/

open scoped BigOperators

namespace Erdos291

/-! ## The prime-divisor-mass lemma -/

/-- **Prime-divisor mass.** For a nonzero natural number `N` and a threshold `Y ≥ 2`, the sum of
the reciprocals of the prime divisors of `N` that are strictly greater than `Y` is at most
`log N / (Y · log Y)`.

The proof: let `S` be the set of such primes.  Their product divides `N` (distinct primes, each
dividing `N`), so `∏_{p∈S} p ≤ N`; each `p ∈ S` is `> Y`, hence `Y ≤ p`, giving
`Y^(S.card) ≤ ∏_{p∈S} p ≤ N`.  Taking logs, `S.card ≤ log N / log Y`.  Finally each summand
`1/p` is `≤ 1/Y`, so the whole sum is `≤ S.card / Y ≤ log N / (Y log Y)`. -/
theorem sum_inv_prime_divisors_gt_le (N Y : ℕ) (hN : N ≠ 0) (hY : 2 ≤ Y) :
    (∑ p ∈ (Finset.Icc (Y + 1) N).filter (fun p => Nat.Prime p ∧ p ∣ N), (1 / (p : ℝ))) ≤
      Real.log (N : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) := by
  set S : Finset ℕ := (Finset.Icc (Y + 1) N).filter (fun p => Nat.Prime p ∧ p ∣ N)
  -- The product of the primes in `S` divides `N`.
  have hprod_dvd : (∏ p ∈ S, p) ∣ N := by
    refine Finset.prod_primes_dvd N ?_ ?_
    · intro a ha
      exact ((Finset.mem_filter.mp ha).2).1.prime
    · intro a ha
      exact ((Finset.mem_filter.mp ha).2).2
  have hprod_le : (∏ p ∈ S, p) ≤ N := Nat.le_of_dvd hN.bot_lt hprod_dvd
  -- Each prime in `S` is at least `Y`.
  have hY_le_p : ∀ p ∈ S, Y ≤ p := by
    intro p hp
    have hpIcc : p ∈ Finset.Icc (Y + 1) N := (Finset.mem_filter.mp hp).1
    have hYp : Y + 1 ≤ p := (Finset.mem_Icc.mp hpIcc).1
    omega
  -- Hence `Y ^ S.card ≤ ∏ p ≤ N`.
  have hYpow_le_prod : Y ^ S.card ≤ ∏ p ∈ S, p := by
    calc
      Y ^ S.card = ∏ p ∈ S, (Y : ℕ) := (Finset.prod_const (Y : ℕ)).symm
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' (fun p hp => hY_le_p p hp)
  have hYpow_le_N : Y ^ S.card ≤ N := hYpow_le_prod.trans hprod_le
  -- Positivity facts on the real side.
  have hY_pos : 0 < (Y : ℝ) := by exact_mod_cast (show 0 < Y by omega)
  have hlogY_pos : 0 < Real.log (Y : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < Y by omega))
  -- Taking logs: `S.card · log Y ≤ log N`.
  have hYpow_real_le : (Y : ℝ) ^ S.card ≤ (N : ℝ) := by
    rw [← Nat.cast_pow Y S.card]
    exact_mod_cast hYpow_le_N
  have hlog_le : Real.log ((Y : ℝ) ^ S.card) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (pow_pos hY_pos S.card) hYpow_real_le
  have hlog_mul : (S.card : ℝ) * Real.log (Y : ℝ) ≤ Real.log (N : ℝ) := by
    simpa using hlog_le
  -- The sum is bounded by `S.card / Y`.
  have hsum_le : (∑ p ∈ S, (1 / (p : ℝ))) ≤ (S.card : ℝ) / (Y : ℝ) := by
    calc
      (∑ p ∈ S, (1 / (p : ℝ))) ≤ ∑ p ∈ S, (1 / (Y : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        exact one_div_le_one_div_of_le hY_pos (by exact_mod_cast (hY_le_p p hp))
      _ = (S.card : ℝ) / (Y : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  -- And `S.card / Y ≤ log N / (Y · log Y)` from the log bound.
  have hfinal : (S.card : ℝ) / (Y : ℝ) ≤ Real.log (N : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) := by
    rw [div_le_div_iff₀ hY_pos (mul_pos hY_pos hlogY_pos)]
    calc
      (S.card : ℝ) * ((Y : ℝ) * Real.log (Y : ℝ))
          = ((S.card : ℝ) * Real.log (Y : ℝ)) * (Y : ℝ) := by ring
      _ ≤ Real.log (N : ℝ) * (Y : ℝ) :=
          mul_le_mul_of_nonneg_right hlog_mul (le_of_lt hY_pos)
  exact hsum_le.trans hfinal

/-! ## Instantiation to the resultant `Res(Q_d, Q_e)` -/

/-- **Exceptional-prime mass for a gap pair.** For distances `d ≠ e` (both `≥ 1`) and a threshold
`Y ≥ 2`, the reciprocal mass of the prime divisors of `resultant (Qd d) (Qd e)` exceeding `Y` is
bounded by `log |resultant (Qd d) (Qd e)| / (Y · log Y)`.  This is the quantitative upgrade of the
finiteness statement: the large prime divisors of the resultant contribute only a small amount of
reciprocal mass, uniformly in `Y`. -/
theorem exceptional_prime_mass_le (d e Y : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) (hde : d ≠ e)
    (hY : 2 ≤ Y) :
    (∑ p ∈ (Finset.Icc (Y + 1) (Int.natAbs (Polynomial.resultant (Qd d) (Qd e)))).filter
        (fun p => Nat.Prime p ∧ p ∣ Int.natAbs (Polynomial.resultant (Qd d) (Qd e))),
      (1 / (p : ℝ))) ≤
      Real.log ((Int.natAbs (Polynomial.resultant (Qd d) (Qd e))) : ℝ) /
        ((Y : ℝ) * Real.log (Y : ℝ)) := by
  have hres : Polynomial.resultant (Qd d) (Qd e) ≠ 0 :=
    resultant_Qd_ne_zero d e hd he hde
  have hN : (Polynomial.resultant (Qd d) (Qd e)).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr hres
  simpa using sum_inv_prime_divisors_gt_le
    (Polynomial.resultant (Qd d) (Qd e)).natAbs Y hN hY

end Erdos291
