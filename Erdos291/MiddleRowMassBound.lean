import Erdos291.WmidBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# An explicit product bound for the middle row mass and `Sy`

The row route in `BlockMidRow` bounds the number of row primes inside one
dyadic prime block `[P,2P)`.  Here we apply the same numerator-height idea to
the full middle prime set of a row,

  `middlePrimes r x = {p ≤ x | 2r+1 < p ≤ r², p prime, p ∣ num H_r}`.

Since every such `p` is at least `2r+2`, the product of the distinct middle
primes of `r` is at least `(2r+2)^card`, and it divides `numNat r ≤ r·L r`.
Hence `card ≤ log(r·L r)/log(2r+2) ≤ middleRowConstant·r/log(2r+2)`, and because
each summand `1/(p-1)` is at most `1/(2r+1)` we obtain the row-mass bound

  `middleRowMass r x ≤ middleRowConstant·r / ((2r+1)·log(2r+2))`.

Summing `r·middleRowMass` over the window `[R,2R)` gives the unconditional
weighted-row bound

  `WmidWeightedRowSum R x ≤ middleRowConstant·R² / log(2R+2)`,

and therefore `Wmid R x ≤ middleRowConstant·R / log(2R+2)`.  This improves the
previous unconditional dyadic row bound `dyadicConstant·R/log R` by a factor
asymptotically `dyadicConstant/middleRowConstant = 8`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-- The row constant `Cψ + 1`, where `Cψ = log 4 + 4` is the Chebyshev constant
from `BulkRemoval`.  This duplicates `BlockMidRow.middleRowConstant` so that this file
does not need to import `BlockMidRow` (which is not part of the root import graph). -/
noncomputable def middleRowConstant : ℝ := Cpsi + 1

/-- The dyadic constant corresponding to `BlockMidRow.dyadicConstant` (which is
`8 * rowConstant`); redefined here to avoid importing `BlockMidRow`. -/
noncomputable def middleDyadicConstant : ℝ := 8 * middleRowConstant

/-- `0 ≤ middleRowConstant`. -/
lemma middleRowConstant_nonneg : 0 ≤ middleRowConstant := by
  dsimp [middleRowConstant, Cpsi]
  positivity

/-- `log (r·L r) ≤ middleRowConstant · r`, the same Chebyshev estimate as in
`BlockMidRow.log_mul_L_le_middleRowConstant`. -/
lemma log_mul_L_le_middleRowConstant (r : ℕ) (hr : 1 ≤ r) :
    Real.log ((r * L r : ℕ) : ℝ) ≤ middleRowConstant * (r : ℝ) := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlogr_le : Real.log (r : ℝ) ≤ (r : ℝ) := Real.log_le_self (le_of_lt hrpos)
  have hlog_mul : Real.log ((r * L r : ℕ) : ℝ) =
      Real.log (r : ℝ) + Real.log (L r : ℝ) := by
    rw [Nat.cast_mul]
    exact Real.log_mul (ne_of_gt hrpos) (by exact_mod_cast (L_ne_zero r) : (L r : ℝ) ≠ 0)
  calc
    Real.log ((r * L r : ℕ) : ℝ)
        = Real.log (r : ℝ) + Real.log (L r : ℝ) := hlog_mul
    _ ≤ (r : ℝ) + Cpsi * (r : ℝ) := by nlinarith [hlogr_le, log_L_le r]
    _ = middleRowConstant * (r : ℝ) := by
          dsimp [middleRowConstant]
          ring

/-- The full set of middle primes of a row `r`: primes `p ≤ x` satisfying
`2r+1 < p ≤ r²` and dividing the numerator of the harmonic number `H_r`. -/
def middlePrimes (r x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter
    (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)

/-- `middleRowMass` is the sum of the prime weights over `middlePrimes`. -/
lemma middleRowMass_eq_sum_middlePrimes (r x : ℕ) :
    middleRowMass r x = ∑ p ∈ middlePrimes r x, primeWeight p := by
  rfl

/-- Membership in `middlePrimes` gives the middle prime conditions. -/
lemma mem_middlePrimes_iff {r x p : ℕ} :
    p ∈ middlePrimes r x ↔
      p ∈ Finset.Icc 2 x ∧ 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧
        (p : ℤ) ∣ (harmonic r).num := by
  rw [middlePrimes, Finset.mem_filter]

/-- Every middle prime is prime. -/
lemma prime_of_mem_middlePrimes {r x p : ℕ} (hp : p ∈ middlePrimes r x) : Nat.Prime p :=
  (mem_middlePrimes_iff.mp hp).2.2.2.1

/-- Every middle prime divides the numerator of `H_r`. -/
lemma int_dvd_num_of_mem_middlePrimes {r x p : ℕ} (hp : p ∈ middlePrimes r x) :
    (p : ℤ) ∣ (harmonic r).num :=
  (mem_middlePrimes_iff.mp hp).2.2.2.2

/-- Every middle prime is at least `2r+2`. -/
lemma two_mul_r_add_two_le_of_mem_middlePrimes {r x p : ℕ} (hp : p ∈ middlePrimes r x) :
    2 * r + 2 ≤ p := by
  have h := (mem_middlePrimes_iff.mp hp).2.1
  omega

/-- `middlePrimes r x` is contained in the prime factors of `numNat r`. -/
lemma middlePrimes_subset_primeFactors {r x : ℕ} (hr : 1 ≤ r) :
    middlePrimes r x ⊆ (numNat r).primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors]
  refine ⟨prime_of_mem_middlePrimes hp, ?_, ?_⟩
  · dsimp [numNat]
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (int_dvd_num_of_mem_middlePrimes hp))
  · dsimp [numNat]
    exact ne_of_gt (numNat_pos r hr)

/-- The product of the distinct middle primes of `r` divides `numNat r`. -/
lemma prod_middlePrimes_dvd_numNat (r x : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ middlePrimes r x, p) ∣ numNat r := by
  classical
  have hsub := middlePrimes_subset_primeFactors (r := r) (x := x) hr
  have hsub' : (∏ p ∈ middlePrimes r x, p) ∣
      (∏ p ∈ (numNat r).primeFactors, p) :=
    Finset.prod_dvd_prod_of_subset (middlePrimes r x) (numNat r).primeFactors (fun p => p) hsub
  exact dvd_trans hsub' (Nat.prod_primeFactors_dvd (numNat r))

/-- The product of the distinct middle primes of `r` is at most `numNat r`. -/
lemma prod_middlePrimes_le_numNat (r x : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ middlePrimes r x, p) ≤ numNat r :=
  Nat.le_of_dvd (numNat_pos r hr) (prod_middlePrimes_dvd_numNat r x hr)

/-- Each middle prime is at least `2r+2`, so `(2r+2)^card ≤ ∏ p`. -/
lemma pow_card_le_prod_middlePrimes (r x : ℕ) :
    (2 * r + 2) ^ (middlePrimes r x).card ≤ ∏ p ∈ middlePrimes r x, p := by
  classical
  calc
    (2 * r + 2) ^ (middlePrimes r x).card = ∏ p ∈ middlePrimes r x, (2 * r + 2) := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ middlePrimes r x, p := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      exact two_mul_r_add_two_le_of_mem_middlePrimes hp

/-- The key product chain `(2r+2)^card ≤ numNat r`. -/
lemma pow_card_le_numNat_middle (r x : ℕ) (hr : 1 ≤ r) :
    (2 * r + 2) ^ (middlePrimes r x).card ≤ numNat r :=
  (pow_card_le_prod_middlePrimes r x).trans (prod_middlePrimes_le_numNat r x hr)

/-- The product chain ending at `r * L r`. -/
lemma pow_card_le_mul_L_middle (r x : ℕ) (hr : 1 ≤ r) :
    (2 * r + 2) ^ (middlePrimes r x).card ≤ r * L r :=
  (pow_card_le_numNat_middle r x hr).trans (numNat_le_mul_L r)

/-- The log-count estimate for the full middle prime set. -/
lemma middlePrimes_card_le_log_mul (r x : ℕ) (hr : 1 ≤ r) :
    ((middlePrimes r x).card : ℝ) ≤
      Real.log ((r * L r : ℕ) : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ) := by
  classical
  let s := middlePrimes r x
  have hbase : 1 < (2 * r + 2 : ℕ) := by omega
  have hbaseR : 1 < ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast hbase
  have hlogbasepos : 0 < Real.log ((2 * r + 2 : ℕ) : ℝ) := Real.log_pos hbaseR
  have hn_pos : 0 < numNat r := numNat_pos r hr
  have hpow_le : (2 * r + 2) ^ s.card ≤ numNat r := by
    dsimp [s]
    exact pow_card_le_numNat_middle r x hr
  have hlog_pow_le : Real.log (((2 * r + 2) ^ s.card : ℕ) : ℝ) ≤
      Real.log ((numNat r : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (pow_pos (by omega : 0 < 2 * r + 2) s.card)
    · exact_mod_cast hpow_le
  have hlog_pow_eq : Real.log (((2 * r + 2) ^ s.card : ℕ) : ℝ) =
      (s.card : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact Real.log_pow ((2 * r + 2 : ℕ) : ℝ) s.card
  have hcard_log : (s.card : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ) ≤
      Real.log ((numNat r : ℕ) : ℝ) := by
    rwa [hlog_pow_eq] at hlog_pow_le
  have hnum_le : numNat r ≤ r * L r := numNat_le_mul_L r
  have hlog_num_le : Real.log ((numNat r : ℕ) : ℝ) ≤ Real.log ((r * L r : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hn_pos
    · exact_mod_cast hnum_le
  have hcard_log_le := hcard_log.trans hlog_num_le
  have hmain : (s.card : ℝ) ≤ Real.log ((r * L r : ℕ) : ℝ) /
      Real.log ((2 * r + 2 : ℕ) : ℝ) := by
    exact (le_div_iff₀ hlogbasepos).2 hcard_log_le
  simpa [s] using hmain

/-- The clean log-count estimate for the full middle prime set. -/
lemma middlePrimes_card_le (r x : ℕ) (hr : 1 ≤ r) :
    ((middlePrimes r x).card : ℝ) ≤
      middleRowConstant * (r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ) := by
  have hbaseR : 1 < ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * r + 2)
  have hlogbasepos : 0 < Real.log ((2 * r + 2 : ℕ) : ℝ) := Real.log_pos hbaseR
  have hlog := middlePrimes_card_le_log_mul r x hr
  calc
    ((middlePrimes r x).card : ℝ)
        ≤ Real.log ((r * L r : ℕ) : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ) := hlog
    _ ≤ (middleRowConstant * (r : ℝ)) / Real.log ((2 * r + 2 : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right (log_mul_L_le_middleRowConstant r hr)
            (le_of_lt hlogbasepos)

/-- The middle row mass is at most the cardinality divided by `2r+1`. -/
lemma middleRowMass_le_card_div_two_mul_r_add_one (r x : ℕ) (hr : 1 ≤ r) :
    middleRowMass r x ≤ ((middlePrimes r x).card : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by
  classical
  rw [middleRowMass_eq_sum_middlePrimes]
  calc
    (∑ p ∈ middlePrimes r x, primeWeight p) ≤
        ∑ p ∈ middlePrimes r x, (1 / ((2 * r + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          have h := two_mul_r_add_two_le_of_mem_middlePrimes hp
          have hden : (2 * r + 1 : ℕ) ≤ p - 1 := by
            omega
          have hpos : 0 < ((2 * r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * r + 1)
          have hleR : ((2 * r + 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hden
          dsimp [primeWeight]
          exact one_div_le_one_div_of_le hpos hleR
    _ = ((middlePrimes r x).card : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- The explicit row-mass bound from the numerator height. -/
lemma middleRowMass_le_middleRowConstant_mul (r x : ℕ) (hr : 1 ≤ r) :
    middleRowMass r x ≤
      middleRowConstant * (r : ℝ) / (((2 * r + 1 : ℕ) : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
  have hcard := middlePrimes_card_le r x hr
  have hmass := middleRowMass_le_card_div_two_mul_r_add_one r x hr
  have hden1 : 0 < ((2 * r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * r + 1)
  have hbaseR : 1 < ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * r + 2)
  have hlogbasepos : 0 < Real.log ((2 * r + 2 : ℕ) : ℝ) := Real.log_pos hbaseR
  have hcarddiv : ((middlePrimes r x).card : ℝ) / ((2 * r + 1 : ℕ) : ℝ) ≤
      (middleRowConstant * (r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) / ((2 * r + 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
  have hrewrite : (middleRowConstant * (r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) /
      ((2 * r + 1 : ℕ) : ℝ) =
      middleRowConstant * (r : ℝ) / (((2 * r + 1 : ℕ) : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
    field_simp [ne_of_gt hden1, ne_of_gt hlogbasepos]
  calc
    middleRowMass r x ≤ ((middlePrimes r x).card : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := hmass
    _ ≤ (middleRowConstant * (r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) / ((2 * r + 1 : ℕ) : ℝ) := hcarddiv
    _ = middleRowConstant * (r : ℝ) / (((2 * r + 1 : ℕ) : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ)) := hrewrite

/-- `r²/(2r+1) ≤ r/2` for positive `r`, used to simplify the weighted sum. -/
lemma r_sq_div_two_mul_r_add_one_le (r : ℕ) (hr : 1 ≤ r) :
    ((r : ℝ) ^ 2) / ((2 * r + 1 : ℕ) : ℝ) ≤ (r : ℝ) / 2 := by
  have hpos : 0 < ((2 * r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * r + 1)
  have hrpos : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  rw [div_le_iff₀ hpos]
  have hineq : (2 : ℝ) * (r : ℝ) ^ 2 ≤ (r : ℝ) * ((2 * r + 1 : ℕ) : ℝ) := by
    have hnat : 2 * r ≤ 2 * r + 1 := by omega
    have hnatR : (2 : ℝ) * (r : ℝ) ≤ ((2 * r + 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have h1 : (2 : ℝ) * (r : ℝ) ^ 2 = (r : ℝ) * ((2 : ℝ) * (r : ℝ)) := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left hnatR hrpos
  nlinarith

/-- The weighted row sum is at most `(middleRowConstant/2)·Σ r/log(2r+2)`. -/
lemma WmidWeightedRowSum_le_middleRowConstant_half_sum (R x : ℕ) (hR : 2 ≤ R) :
    WmidWeightedRowSum R x ≤
      (middleRowConstant / 2) * ∑ r ∈ Finset.Ico R (2 * R),
        ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
  classical
  unfold WmidWeightedRowSum
  calc
    (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMass r x)
        ≤ ∑ r ∈ Finset.Ico R (2 * R),
            (r : ℝ) * (middleRowConstant * (r : ℝ) /
              (((2 * r + 1 : ℕ) : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ))) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hr1 : 1 ≤ r := by
            have hi := Finset.mem_Ico.mp hr
            omega
          exact mul_le_mul_of_nonneg_left (middleRowMass_le_middleRowConstant_mul r x hr1)
            (Nat.cast_nonneg r)
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
          (middleRowConstant / 2) * ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hr1 : 1 ≤ r := by
            have hi := Finset.mem_Ico.mp hr
            omega
          have hbaseR : 1 < ((2 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * r + 2)
          have hlogpos : 0 < Real.log ((2 * r + 2 : ℕ) : ℝ) := Real.log_pos hbaseR
          have hden1 : 0 < ((2 * r + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * r + 1)
          have hineq : ((r : ℝ) ^ 2) / ((2 * r + 1 : ℕ) : ℝ) ≤ (r : ℝ) / 2 :=
            r_sq_div_two_mul_r_add_one_le r hr1
          calc
            (r : ℝ) * (middleRowConstant * (r : ℝ) /
                (((2 * r + 1 : ℕ) : ℝ) * Real.log ((2 * r + 2 : ℕ) : ℝ)))
                = middleRowConstant * ((((r : ℝ) ^ 2) / ((2 * r + 1 : ℕ) : ℝ)) /
                    Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
                  field_simp [ne_of_gt hden1, ne_of_gt hlogpos]
            _ ≤ middleRowConstant * (((r : ℝ) / 2) / Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
                  exact mul_le_mul_of_nonneg_left
                    (div_le_div_of_nonneg_right hineq (le_of_lt hlogpos)) middleRowConstant_nonneg
            _ = (middleRowConstant / 2) * ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
                  ring
    _ = (middleRowConstant / 2) * ∑ r ∈ Finset.Ico R (2 * R),
          ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]

/-- The sum of `r/log(2r+2)` over the window is at most `2R²/log(2R+2)`. -/
lemma sum_r_div_log_le_two_mul_R_sq_div_log (R : ℕ) (hR : 2 ≤ R) :
    (∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ))) ≤
      2 * (R : ℝ) ^ 2 / Real.log ((2 * R + 2 : ℕ) : ℝ) := by
  classical
  have hbaseR : 1 < ((2 * R + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 2 * R + 2)
  have hlogRpos : 0 < Real.log ((2 * R + 2 : ℕ) : ℝ) := Real.log_pos hbaseR
  calc
    (∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)))
        ≤ ∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) / Real.log ((2 * R + 2 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hi := Finset.mem_Ico.mp hr
          have hlogmono : Real.log ((2 * R + 2 : ℕ) : ℝ) ≤ Real.log ((2 * r + 2 : ℕ) : ℝ) := by
            apply Real.log_le_log
            · exact_mod_cast (by omega : 0 < 2 * R + 2)
            · exact_mod_cast (by omega : 2 * R + 2 ≤ 2 * r + 2)
          exact div_le_div_of_nonneg_left (a := (r : ℝ)) (b := Real.log ((2 * r + 2 : ℕ) : ℝ))
            (c := Real.log ((2 * R + 2 : ℕ) : ℝ))
            (Nat.cast_nonneg r) hlogRpos hlogmono
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R), ((2 * (R : ℝ)) / Real.log ((2 * R + 2 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hi := Finset.mem_Ico.mp hr
          have hrle : (r : ℝ) ≤ 2 * (R : ℝ) := by
            have hrnat : r ≤ 2 * R := by omega
            exact_mod_cast hrnat
          exact div_le_div_of_nonneg_right hrle (le_of_lt hlogRpos)
    _ = (Finset.Ico R (2 * R)).card • ((2 * (R : ℝ)) / Real.log ((2 * R + 2 : ℕ) : ℝ)) := by
          rw [Finset.sum_const]
    _ = (R : ℝ) * ((2 * (R : ℝ)) / Real.log ((2 * R + 2 : ℕ) : ℝ)) := by
          rw [nsmul_eq_mul]
          have hcard : (Finset.Ico R (2 * R)).card = R := by
            simp
            omega
          rw [hcard]
    _ = 2 * (R : ℝ) ^ 2 / Real.log ((2 * R + 2 : ℕ) : ℝ) := by
          field_simp [ne_of_gt hlogRpos]

/-- The unconditional weighted-row bound `Sy ≤ middleRowConstant·R²/log(2R+2)`. -/
theorem WmidWeightedRowSum_le_middleRowConstant_R_sq_div_log (R x : ℕ) (hR : 2 ≤ R) :
    WmidWeightedRowSum R x ≤
      middleRowConstant * (R : ℝ) ^ 2 / Real.log ((2 * R + 2 : ℕ) : ℝ) := by
  have hsum := WmidWeightedRowSum_le_middleRowConstant_half_sum R x hR
  have htail := sum_r_div_log_le_two_mul_R_sq_div_log R hR
  have hnonneg : 0 ≤ (middleRowConstant / 2 : ℝ) := div_nonneg middleRowConstant_nonneg (by norm_num)
  calc
    WmidWeightedRowSum R x ≤
        (middleRowConstant / 2) * ∑ r ∈ Finset.Ico R (2 * R),
          ((r : ℝ) / Real.log ((2 * r + 2 : ℕ) : ℝ)) := hsum
    _ ≤ (middleRowConstant / 2) * (2 * (R : ℝ) ^ 2 / Real.log ((2 * R + 2 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left htail hnonneg
    _ = middleRowConstant * (R : ℝ) ^ 2 / Real.log ((2 * R + 2 : ℕ) : ℝ) := by
          field_simp [ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * R + 2) : 1 < ((2 * R + 2 : ℕ) : ℝ)))]

/-- The unconditional middle-block bound `Wmid ≤ middleRowConstant·R/log(2R+2)`.
This improves the previous `dyadicConstant·R/log R` row-route bound by an
asymptotic factor `8`. -/
theorem Wmid_le_middleRowConstant_mul_R_div_log (R x : ℕ) (hR : 2 ≤ R) :
    Wmid R x ≤ middleRowConstant * (R : ℝ) / Real.log ((2 * R + 2 : ℕ) : ℝ) := by
  have hRpos : 0 < R := by omega
  have hSy := WmidWeightedRowSum_le_middleRowConstant_R_sq_div_log R x hR
  have hW := Wmid_le_WmidWeightedRowSum_div_R R x hRpos
  have hRrealpos : 0 < (R : ℝ) := by exact_mod_cast hRpos
  have hlogpos : 0 < Real.log ((2 * R + 2 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * R + 2)
  calc
    Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := hW
    _ ≤ (middleRowConstant * (R : ℝ) ^ 2 / Real.log ((2 * R + 2 : ℕ) : ℝ)) / (R : ℝ) :=
          div_le_div_of_nonneg_right hSy (le_of_lt hRrealpos)
    _ = middleRowConstant * (R : ℝ) / Real.log ((2 * R + 2 : ℕ) : ℝ) := by
          field_simp [ne_of_gt hRrealpos, ne_of_gt hlogpos]

/-- The new row-route bound is at most the redefined dyadic-constant bound
(definitionally the same constant as `BlockMidRow.dyadicConstant`). -/
lemma middleRowConstant_mul_R_div_log_le_middleDyadicConstant_mul_R_div_log (R : ℕ) (hR : 2 ≤ R) :
    middleRowConstant * (R : ℝ) / Real.log ((2 * R + 2 : ℕ) : ℝ) ≤
      middleDyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRgt1 : 1 < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hRgt1
  have hlog2Rpos : 0 < Real.log ((2 * R + 2 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < 2 * R + 2)
  have hmono : Real.log (R : ℝ) ≤ Real.log ((2 * R + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < R)
    · exact_mod_cast (by omega : R ≤ 2 * R + 2)
  have hnonneg : 0 ≤ middleRowConstant * (R : ℝ) := mul_nonneg middleRowConstant_nonneg (le_of_lt hRpos)
  have hd : middleRowConstant ≤ middleDyadicConstant := by
    dsimp [middleDyadicConstant]
    nlinarith [middleRowConstant_nonneg]
  have h1 : middleRowConstant * (R : ℝ) / Real.log ((2 * R + 2 : ℕ) : ℝ) ≤
      middleRowConstant * (R : ℝ) / Real.log (R : ℝ) := by
    exact div_le_div_of_nonneg_left (a := middleRowConstant * (R : ℝ))
      (b := Real.log ((2 * R + 2 : ℕ) : ℝ)) (c := Real.log (R : ℝ))
      hnonneg hlogRpos hmono
  have h2 : middleRowConstant * (R : ℝ) / Real.log (R : ℝ) ≤
      middleDyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hd (le_of_lt hRpos))
      (le_of_lt hlogRpos)
  exact h1.trans h2

end

end Erdos291
