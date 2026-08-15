import Erdos291.BadSet
import Erdos291.DoubleCount
import Erdos291.MertensUpper
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Squarefree

/-!
# Erdős #291 — removing the `p > r²` bulk of the weighted double sum

This file proves the *unconditional* estimate that the tail

$$\sum_{r \le x} \sum_{\substack{p\ \text{prime}\\ r^2 < p \le x\\ p \mid \operatorname{num}(H_r)}} \frac{1}{p-1}$$

is `O(log log x)`.  Unlike the arithmetic hypothesis `HA_arith` (which is still open),
this bound needs no input on the distribution of the bad-digit sets `E p`: the only facts
used are the size of the numerator `num (H_r)`, the trivial bound `a r ≤ r · L r`, and the
Chebyshev estimate `log (L r) = O(r)` (which *is* in Mathlib).  The key idea is a count:
the distinct primes `p > r²` dividing `num (H_r)` have product `≥ (r²)^#P_r` and `≤ r · L r`,
so `#P_r ≤ C r / log r`, and summing `#P_r / r²` over `r` gives the `log log` bound via
`MertensUpper.sum_inv_mul_log_le`.

The route is:

1. `(harmonic r).num ≤ a r` via `harmonic_eq_a_div_L` and `num_div_eq_div_gcd`.
2. `a r ≤ r · L r` (each summand `L r / k ≤ L r`, and there are `r` of them).
3. `log (L r) ≤ (log 4 + 4) · r` from `Chebyshev.psi_eq_log_lcmUpto` and
   `Chebyshev.psi_le_const_mul_self`.
4. The counting lemma `#P_r ≤ (Cψ + 1) · r / (2 log r)`.
5. Per-`r`: `∑_{p > r²} 1/(p-1) ≤ #P_r / r² ≤ (Cψ+1) / (2 r log r)`.
6. Sum over `r` using `MertensUpper.sum_inv_mul_log_le`.

There are no unproved declarations in this file.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

noncomputable section

/-- The Chebyshev constant in `log (L r) ≤ Cψ · r`. -/
def Cpsi : ℝ := Real.log 4 + 4

/-- The constant in front of `1 / (r log r)` in the per-`r` tail bound. -/
def Ctail : ℝ := (Cpsi + 1) / 2

/-- The final constant in the `O(log log x)` bound. -/
def Cfinal : ℝ := Ctail * (1 + 1 / (2 * Real.log 2) - Real.log (Real.log 2))

/-- The natural-valued numerator `num (H_r)`, used so that `primeFactors` applies. -/
def numNat (r : ℕ) : ℕ := ((harmonic r).num).natAbs

/-- The primes `p > r²` dividing `num (H_r)`. -/
def primeTail (r : ℕ) : Finset ℕ :=
  (numNat r).primeFactors.filter fun p => r ^ 2 < p

/-! ## Step 1 & 2: `num (H_r) ≤ r · L r` -/

/-- `num (H_r) ≤ a r` (as a natural, via `natAbs`). -/
lemma numNat_le_a (r : ℕ) : numNat r ≤ a r := by
  dsimp [numNat]
  have hnum : (harmonic r).num = ((a r / Nat.gcd (a r) (L r) : ℕ) : ℤ) := by
    rw [harmonic_eq_a_div_L r]
    exact num_div_eq_div_gcd (a r) (L r) (L_ne_zero r)
  calc
    ((harmonic r).num).natAbs = a r / Nat.gcd (a r) (L r) := by
      rw [hnum, Int.natAbs_natCast]
    _ ≤ a r := Nat.div_le_self (a r) (Nat.gcd (a r) (L r))

/-- `a r ≤ r · L r`. -/
lemma a_le_mul_L (r : ℕ) : a r ≤ r * L r := by
  unfold a
  calc
    (∑ k ∈ Finset.Icc 1 r, L r / k)
        ≤ ∑ k ∈ Finset.Icc 1 r, L r := by
            refine Finset.sum_le_sum ?_
            intro k _
            exact Nat.div_le_self (L r) k
    _ = r * L r := by
            have hcard : (Finset.Icc 1 r).card = r := by rw [Nat.card_Icc]; omega
            rw [Finset.sum_const, Nat.nsmul_eq_mul, hcard]

/-- `num (H_r) ≤ r · L r`. -/
lemma numNat_le_mul_L (r : ℕ) : numNat r ≤ r * L r :=
  (numNat_le_a r).trans (a_le_mul_L r)

/-! ## Step 0: `0 < harmonic r` and positivity of the numerator -/

/-- `0 < harmonic r` for `1 ≤ r`. -/
lemma harmonic_pos (r : ℕ) (hr : 1 ≤ r) : 0 < harmonic r := by
  rw [harmonic]
  refine Finset.sum_pos ?_ ?_
  · intro i _
    have hio : (0 : ℚ) < ((i + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < i + 1)
    exact inv_pos.mpr hio
  · exact ⟨0, by rw [Finset.mem_range]; omega⟩

/-- `0 < numNat r` for `1 ≤ r`. -/
lemma numNat_pos (r : ℕ) (hr : 1 ≤ r) : 0 < numNat r := by
  dsimp [numNat]
  have hharm : 0 < harmonic r := harmonic_pos r hr
  have hnum : 0 < (harmonic r).num := Rat.num_pos.2 hharm
  exact Int.natAbs_pos.mpr (ne_of_gt hnum)

/-! ## Step 3: `log (L r) ≤ Cψ · r` (Chebyshev) -/

/-- `log (L r) ≤ Cψ · r`, from Chebyshev's `ψ n ≤ (log 4 + 4) · n`. -/
lemma log_L_le (r : ℕ) : Real.log (L r) ≤ Cpsi * (r : ℝ) := by
  have h1 : Chebyshev.psi (r : ℝ) = Real.log (L r) := by
    rw [L]
    simpa using (Chebyshev.psi_eq_log_lcmUpto r)
  rw [← h1]
  have h2 := Chebyshev.psi_le_const_mul_self (show (0 : ℝ) ≤ (r : ℝ) by positivity)
  simpa [Cpsi] using h2

/-! ## Step 4: the counting lemma `#P_r ≤ (Cψ + 1) · r / (2 log r)` -/

/-- For `2 ≤ r`, the number of primes `p > r²` dividing `num (H_r)` is `≤ (Cψ+1)·r/(2 log r)`. -/
lemma primeTail_card_le (r : ℕ) (hr : 2 ≤ r) :
    ((primeTail r).card : ℝ) ≤ (Cpsi + 1) * (r : ℝ) / (2 * Real.log (r : ℝ)) := by
  let n := numNat r
  let s := primeTail r
  have hn_pos : 0 < n := by dsimp [n]; exact numNat_pos r (by omega : 1 ≤ r)
  have hsub : s ⊆ n.primeFactors := by
    dsimp [s, primeTail]
    exact Finset.filter_subset (fun p => r ^ 2 < p) (numNat r).primeFactors
  have hprod_dvd : (∏ p ∈ s, p) ∣ n := by
    have hsub' : (∏ p ∈ s, p) ∣ (∏ p ∈ (numNat r).primeFactors, p) :=
      Finset.prod_dvd_prod_of_subset s (numNat r).primeFactors (fun p => p) hsub
    exact dvd_trans hsub' (Nat.prod_primeFactors_dvd (numNat r))
  have hpow_le_prod : (r ^ 2) ^ s.card ≤ ∏ p ∈ s, p := by
    calc
      (r ^ 2) ^ s.card = ∏ p ∈ s, (r ^ 2) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, p := by
            refine Finset.prod_le_prod' ?_
            intro p hp
            have hp' := Finset.mem_filter.mp hp
            exact le_of_lt hp'.2
  have hrpow_le_n : r ^ (2 * s.card) ≤ n := by
    calc
      r ^ (2 * s.card) = (r ^ 2) ^ s.card := by rw [pow_mul]
      _ ≤ ∏ p ∈ s, p := hpow_le_prod
      _ ≤ n := Nat.le_of_dvd hn_pos hprod_dvd
  have hnum_le : n ≤ r * L r := by dsimp [n]; exact numNat_le_mul_L r
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlogrpos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hlog_pow_le : Real.log ((r ^ (2 * s.card) : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (pow_pos (by omega : 0 < r) (2 * s.card))
    · exact_mod_cast hrpow_le_n
  have hlog_n_le : Real.log (n : ℝ) ≤ Real.log ((r * L r : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hn_pos
    · exact_mod_cast hnum_le
  have hlog_mul : Real.log ((r * L r : ℕ) : ℝ) = Real.log (r : ℝ) + Real.log (L r : ℝ) := by
    rw [Nat.cast_mul]
    rw [Real.log_mul]
    · exact ne_of_gt hrpos
    · exact_mod_cast (L_ne_zero r)
  have hlog_pow : Real.log ((r : ℝ) ^ (2 * s.card)) ≤ (Cpsi + 1) * (r : ℝ) := by
    calc
      Real.log ((r : ℝ) ^ (2 * s.card)) = Real.log ((r ^ (2 * s.card) : ℕ) : ℝ) := by rw [← Nat.cast_pow]
      _ ≤ Real.log (n : ℝ) := hlog_pow_le
      _ ≤ Real.log ((r * L r : ℕ) : ℝ) := hlog_n_le
      _ = Real.log (r : ℝ) + Real.log (L r : ℝ) := hlog_mul
      _ ≤ Real.log (r : ℝ) + Cpsi * (r : ℝ) := by nlinarith [log_L_le r]
      _ ≤ (Cpsi + 1) * (r : ℝ) := by
            have hlog_le_r : Real.log (r : ℝ) ≤ (r : ℝ) := Real.log_le_self (le_of_lt hrpos)
            nlinarith
  have hlogpow : Real.log ((r : ℝ) ^ (2 * s.card)) = ((2 * s.card : ℕ) : ℝ) * Real.log (r : ℝ) := by
    rw [Real.log_pow]
  have hchain : ((2 * s.card : ℕ) : ℝ) * Real.log (r : ℝ) ≤ (Cpsi + 1) * (r : ℝ) := by
    rw [← hlogpow]
    exact hlog_pow
  have h2logpos : 0 < 2 * Real.log (r : ℝ) := by positivity
  have hmain : (s.card : ℝ) ≤ (Cpsi + 1) * (r : ℝ) / (2 * Real.log (r : ℝ)) := by
    rw [le_div_iff₀ h2logpos]
    calc
      (s.card : ℝ) * (2 * Real.log (r : ℝ))
          = 2 * (s.card : ℝ) * Real.log (r : ℝ) := by ring
      _ = ((2 * s.card : ℕ) : ℝ) * Real.log (r : ℝ) := by
            rw [Nat.cast_mul]
            ring
      _ ≤ (Cpsi + 1) * (r : ℝ) := hchain
  simpa [s] using hmain

/-! ## Step 5: the per-`r` tail bound -/

/-- `1/(p-1) ≤ 1/r²` when `p > r²`. -/
lemma one_div_sub_one_le (r p : ℕ) (hr : 2 ≤ r) (hp : r ^ 2 < p) :
    (1 / ((p - 1 : ℕ) : ℝ)) ≤ (1 / ((r : ℝ) ^ 2)) := by
  have hle_nat : r ^ 2 ≤ p - 1 := by omega
  have hr2pos : 0 < (r : ℝ) ^ 2 := by positivity
  have hle : (r : ℝ) ^ 2 ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
  exact one_div_le_one_div_of_le hr2pos hle

/-- The `Ico (r²+1) (x+1)` slice is a subset of `primeTail r`. -/
lemma slice_subset_primeTail (r x : ℕ) (hr : 2 ≤ r) :
    (Finset.Ico (r ^ 2 + 1) (x + 1)).filter (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)
      ⊆ primeTail r := by
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases hp with ⟨hpIco, hcond⟩
  rcases hcond with ⟨hpPrime, hdvd⟩
  dsimp [primeTail]
  rw [Finset.mem_filter]
  constructor
  · rw [Nat.mem_primeFactors]
    refine ⟨hpPrime, ?_, ?_⟩
    · dsimp [numNat]
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvd)
    · dsimp [numNat]
      exact ne_of_gt (numNat_pos r (by omega : 1 ≤ r))
  · have hpIco' : r ^ 2 + 1 ≤ p ∧ p < x + 1 := Finset.mem_Ico.mp hpIco
    omega

/-- For `2 ≤ r`, the inner `∑_{p > r², p ∣ num H_r} 1/(p-1)` is `≤ Ctail / (r log r)`. -/
lemma inner_sum_le (r x : ℕ) (hr : 2 ≤ r) :
    (∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
      (1 / ((p - 1 : ℕ) : ℝ)))
      ≤ Ctail * (1 / ((r : ℝ) * Real.log (r : ℝ))) := by
  let s := primeTail r
  have hsub : (∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
      (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num), (1 / ((p - 1 : ℕ) : ℝ)))
      ≤ ∑ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ)) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact slice_subset_primeTail r x hr
    · intro p _ _
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  have hcard_sum : (∑ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ))) ≤ (s.card : ℝ) * (1 / ((r : ℝ) ^ 2)) := by
    calc
      (∑ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ)))
          ≤ ∑ p ∈ s, (1 / ((r : ℝ) ^ 2)) := by
              refine Finset.sum_le_sum ?_
              intro p hp
              have hp' := Finset.mem_filter.mp hp
              exact one_div_sub_one_le r p hr hp'.2
      _ = (s.card : ℝ) * (1 / ((r : ℝ) ^ 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) ≤ (Cpsi + 1) * (r : ℝ) / (2 * Real.log (r : ℝ)) := by
    simpa [s] using primeTail_card_le r hr
  calc
    (∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num), (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ ∑ p ∈ s, (1 / ((p - 1 : ℕ) : ℝ)) := hsub
    _ ≤ (s.card : ℝ) * (1 / ((r : ℝ) ^ 2)) := hcard_sum
    _ ≤ ((Cpsi + 1) * (r : ℝ) / (2 * Real.log (r : ℝ))) * (1 / ((r : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_right hcard
            (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (r : ℝ)))
    _ = Ctail * (1 / ((r : ℝ) * Real.log (r : ℝ))) := by
          dsimp [Ctail]
          have hlogpos : Real.log (r : ℝ) ≠ 0 :=
            ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < r)))
          have hrpos : (r : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (by omega : 0 < r))
          field_simp [hlogpos, hrpos, pow_ne_zero 2 hrpos]

/-! ## Positivity of the constants -/

/-- `0 < Ctail`. -/
lemma Ctail_pos : 0 < Ctail := by
  dsimp [Ctail, Cpsi]
  positivity

/-! ## The dyadic-block tail and its uniform decay in `R` -/

/-- The `p > r²` tail of the weighted bad-digit double sum, restricted to the
dyadic block `R ≤ r < 2R`:
`Wtail R x = ∑_{R ≤ r < 2R} ∑_{r² < p ≤ x, p ∣ num H_r} 1/(p-1)`. -/
def Wtail (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R),
    ∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
        (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
      (1 / ((p - 1 : ℕ) : ℝ))

/-- The dyadic block tail is at most `Ctail / log R`, uniformly in `x`. -/
lemma Wtail_le (R x : ℕ) (hR : 2 ≤ R) :
    Wtail R x ≤ Ctail / Real.log (R : ℝ) := by
  unfold Wtail
  have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRlog_pos : 0 < Real.log (R : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < R) : (1 : ℝ) < (R : ℝ))
  have hRprod_pos : 0 < (R : ℝ) * Real.log (R : ℝ) := mul_pos hRreal_pos hRlog_pos
  calc
    (∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
            (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
          (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ ∑ r ∈ Finset.Ico R (2 * R),
            Ctail * (1 / ((r : ℝ) * Real.log (r : ℝ))) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hr2 : 2 ≤ r := by
            have hi := Finset.mem_Ico.mp hr
            omega
          exact inner_sum_le r x hr2
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
            Ctail * (1 / ((R : ℝ) * Real.log (R : ℝ))) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hi := Finset.mem_Ico.mp hr
          have hRr : R ≤ r := hi.1
          have hlog_mono : Real.log (R : ℝ) ≤ Real.log (r : ℝ) := by
            exact Real.log_le_log hRreal_pos (by exact_mod_cast hRr : (R : ℝ) ≤ (r : ℝ))
          have hcast_mono : (R : ℝ) ≤ (r : ℝ) := by exact_mod_cast hRr
          have hprod_mono : (R : ℝ) * Real.log (R : ℝ) ≤ (r : ℝ) * Real.log (r : ℝ) := by
            exact mul_le_mul hcast_mono hlog_mono (le_of_lt hRlog_pos) (Nat.cast_nonneg r)
          have hinv : 1 / ((r : ℝ) * Real.log (r : ℝ)) ≤
              1 / ((R : ℝ) * Real.log (R : ℝ)) := by
            exact one_div_le_one_div_of_le hRprod_pos hprod_mono
          exact mul_le_mul_of_nonneg_left hinv (le_of_lt Ctail_pos)
    _ = (Finset.Ico R (2 * R)).card • (Ctail * (1 / ((R : ℝ) * Real.log (R : ℝ)))) := by
          rw [Finset.sum_const]
    _ = (R : ℝ) * (Ctail * (1 / ((R : ℝ) * Real.log (R : ℝ)))) := by
          rw [nsmul_eq_mul]
          have hcard : (Finset.Ico R (2 * R)).card = R := by
            simp
            omega
          rw [hcard]
    _ = Ctail / Real.log (R : ℝ) := by
          have hRne : (R : ℝ) ≠ 0 := ne_of_gt hRreal_pos
          have hlogne : Real.log (R : ℝ) ≠ 0 := ne_of_gt hRlog_pos
          field_simp [hRne, hlogne]

/-- `Ctail / log R → 0` as `R → ∞` along the naturals. -/
lemma Ctail_div_log_tendsto_zero :
    Tendsto (fun R : ℕ => Ctail / Real.log (R : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hlog.const_div_atTop Ctail

/-- **The uniform tail decay.** For every `ε > 0` there is `R₀` such that for all
`R ≥ R₀` and all `x`, the dyadic-block tail satisfies `Wtail R x ≤ ε`. -/
theorem Wtail_uniformly_tends_to_zero :
    ∀ ε > 0, ∃ R₀, ∀ R ≥ R₀, ∀ x, Wtail R x ≤ ε := by
  intro ε hε
  have hbound : ∀ᶠ R : ℕ in atTop, Ctail / Real.log (R : ℝ) < ε := by
    exact (tendsto_order.1 Ctail_div_log_tendsto_zero).2 ε hε
  rcases Filter.eventually_atTop.1 hbound with ⟨N, hN⟩
  refine ⟨max N 2, ?_⟩
  intro R hR x
  have hR2 : 2 ≤ R := le_trans (le_max_right N 2) hR
  have hNR : N ≤ R := le_trans (le_max_left N 2) hR
  have hlt : Ctail / Real.log (R : ℝ) < ε := hN R hNR
  exact (Wtail_le R x hR2).trans hlt.le

/-- `log 2 ≤ 1`. -/
lemma log_two_le_one : Real.log 2 ≤ 1 := by
  calc
    Real.log 2 ≤ Real.log (Real.exp 1) := by
      have h2le : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        norm_num at h
        exact h
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2le
    _ = 1 := Real.log_exp 1

/-- `0 < Cfinal`. -/
lemma Cfinal_pos : 0 < Cfinal := by
  dsimp [Cfinal, Ctail, Cpsi]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hloglog2_le_zero : Real.log (Real.log 2) ≤ 0 := by
    calc
      Real.log (Real.log 2) ≤ Real.log 1 := Real.log_le_log hlog2 log_two_le_one
      _ = 0 := Real.log_one
  have h1 : 0 < (Real.log 4 + 4 + 1) / 2 := by positivity
  have h2 : 0 < 1 + 1 / (2 * Real.log 2) - Real.log (Real.log 2) := by
    have h21 : 0 < 1 / (2 * Real.log 2) := by positivity
    nlinarith
  exact mul_pos h1 h2

/-! ## The main theorem -/

/-- The `p > r²` tail of the weighted bad-digit double sum is `O(log log x)` unconditionally. -/
theorem tail_sum_p_gt_r_sq_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (∑ r ∈ Finset.Icc 2 x,
        ∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
            (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
          (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ C * (1 + Real.log (Real.log (x : ℝ))) := by
  refine ⟨Cfinal, Cfinal_pos, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with x hx
  have hx2 : 2 ≤ x := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hloglog2_le_zero : Real.log (Real.log 2) ≤ 0 := by
    calc
      Real.log (Real.log 2) ≤ Real.log 1 := Real.log_le_log hlog2 log_two_le_one
      _ = 0 := Real.log_one
  have ht_nonneg : 0 ≤ Real.log (Real.log (x : ℝ)) := by
    have h3e : (3 : ℝ) > Real.exp 1 := by
      have h := Real.exp_lt_two_add_div_two_sub (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
      norm_num at h
      exact h
    have hlogx_gt_one : (1 : ℝ) < Real.log (x : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < (x : ℝ))]
      exact lt_of_lt_of_le h3e (by exact_mod_cast hx : (3 : ℝ) ≤ (x : ℝ))
    exact le_of_lt (Real.log_pos hlogx_gt_one)
  have hA_nonneg : 0 ≤ (1 / (2 * Real.log 2) - Real.log (Real.log 2)) := by
    have h21 : 0 < 1 / (2 * Real.log 2) := by positivity
    nlinarith
  have hAt : 0 ≤ (1 / (2 * Real.log 2) - Real.log (Real.log 2)) * Real.log (Real.log (x : ℝ)) :=
    mul_nonneg hA_nonneg ht_nonneg
  have hA_le : (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2))
      ≤ (1 + 1 / (2 * Real.log 2) - Real.log (Real.log 2)) * (1 + Real.log (Real.log (x : ℝ))) := by
    nlinarith
  calc
    (∑ r ∈ Finset.Icc 2 x,
        ∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
            (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
          (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ ∑ r ∈ Finset.Icc 2 x, Ctail * (1 / ((r : ℝ) * Real.log (r : ℝ))) := by
            refine Finset.sum_le_sum ?_
            intro r hr
            exact inner_sum_le r x (Finset.mem_Icc.mp hr).1
    _ = Ctail * ∑ r ∈ Finset.Icc 2 x, (1 / ((r : ℝ) * Real.log (r : ℝ))) := by
            rw [Finset.mul_sum]
    _ ≤ Ctail * (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) := by
            exact mul_le_mul_of_nonneg_left (sum_inv_mul_log_le x hx2) (le_of_lt Ctail_pos)
    _ ≤ Cfinal * (1 + Real.log (Real.log (x : ℝ))) := by
            calc
              Ctail * (1 / (2 * Real.log 2) + Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2))
                  ≤ Ctail * ((1 + 1 / (2 * Real.log 2) - Real.log (Real.log 2))
                      * (1 + Real.log (Real.log (x : ℝ)))) := by
                      exact mul_le_mul_of_nonneg_left hA_le (le_of_lt Ctail_pos)
              _ = Cfinal * (1 + Real.log (Real.log (x : ℝ))) := by
                      dsimp [Cfinal]
                      ring

end

end Erdos291
