import Erdos291.BlockMidDyadic
import Erdos291.BulkRemoval
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Row estimate for the middle block: fixed `r`, numerator-height rows

This file develops the "row route" for `Wmid`.  For each fixed `r` the primes
contributing to the middle block form

  `rowPrimes r P x = {p ∈ [P, 2P) | p ≤ x, 2r+1 < p, p ≤ r², p prime, p ∣ num H_r}`.

Since every such `p` is `> 2r+1`, in particular `p > r`, so `p` does not divide
`L r` and the divisibility `(p : ℤ) ∣ (harmonic r).num` transfers to the natural
numerator `numNat r`.  Hence the distinct primes in `rowPrimes r P x` have product
dividing `numNat r`, and because they all lie in `[P, 2P)` we obtain the key
log-count estimate

  `#rowPrimes r P x ≤ log (r * L r) / log P ≤ rowConstant * r / log P`

(with `rowConstant = Cψ + 1`, where `Cψ` is the Chebyshev constant from
`BulkRemoval`).  This gives the block bound

  `WmidBlock R P x ≤ blockConstant * R² / (P * log P)`.

Dyadically summing over `P = 2^k` then yields the honest finite bound

  `Wmid R x ≤ dyadicConstant * R / log R`.

This bound is **not** infinitesimal: `dyadicConstant * R / log R → ∞`.
Consequently the pure row route, using only `p > r` and the numerator height
`numNat r ≤ r * L r`, does **not** close the uniform vanishing of `Wmid`.
The file records this as a theorem (`dyadicBound_tendsto_atTop` and
`dyadicBound_not_tendsto_zero`), and also provides the conditional capstone
`W_uniformly_tends_to_zero_of_HA_row_dyadic` so that a future sharper row bound
can be plugged in.

There are no `sorry`/`admit`/`axiom` declarations.  The only hypotheses are the
explicit Prop constants `HA_row_dyadic` used in the conditional capstone.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-- The clean row constant `Cψ + 1`, where `Cψ` is the Chebyshev constant from
`BulkRemoval`. -/
noncomputable def rowConstant : ℝ := Cpsi + 1

/-- The block constant `4 * rowConstant`, from `1/(P-1) ≤ 2/P` and
`∑_{r∈[R,2R)} r ≤ 2R²`. -/
noncomputable def blockConstant : ℝ := 4 * rowConstant

/-- The dyadic-sum constant `2 * blockConstant`, from the geometric-harmonic
bound `∑_{k≥K} 1/(2^k log(2^k)) ≤ 2/(2^K log(2^K))`. -/
noncomputable def dyadicConstant : ℝ := 2 * blockConstant

/-- `0 < rowConstant`. -/
lemma rowConstant_pos : 0 < rowConstant := by
  dsimp [rowConstant, Cpsi]
  positivity

/-- `0 ≤ rowConstant`. -/
lemma rowConstant_nonneg : 0 ≤ rowConstant := le_of_lt rowConstant_pos

/-- `0 < blockConstant`. -/
lemma blockConstant_pos : 0 < blockConstant := by
  dsimp [blockConstant]
  exact mul_pos (by norm_num : 0 < (4 : ℝ)) rowConstant_pos

/-- `0 ≤ blockConstant`. -/
lemma blockConstant_nonneg : 0 ≤ blockConstant := le_of_lt blockConstant_pos

/-- `0 < dyadicConstant`. -/
lemma dyadicConstant_pos : 0 < dyadicConstant := by
  dsimp [dyadicConstant]
  exact mul_pos (by norm_num : 0 < (2 : ℝ)) blockConstant_pos

/-! ## The row prime set -/

/-- The middle prime condition attached to a fixed `r`. -/
private abbrev rowPrimeCond (r p : ℕ) : Prop :=
  2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num

/-- The primes `p ∈ [P, 2P)` that contribute to `WmidBlock` for a fixed `r`:
`p ≤ x`, `2r+1 < p ≤ r²`, `p` prime, and `p` divides the numerator of `H_r`. -/
def rowPrimes (r P x : ℕ) : Finset ℕ :=
  (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ rowPrimeCond r p)

/-- Membership in `rowPrimes`. -/
lemma mem_rowPrimes_iff {r P x p : ℕ} :
    p ∈ rowPrimes r P x ↔
      p ∈ Finset.Ico P (2 * P) ∧ p ≤ x ∧ rowPrimeCond r p := by
  rw [rowPrimes, Finset.mem_filter]

/-- Every `p ∈ rowPrimes r P x` lies in the block `[P, 2P)`. -/
lemma mem_Ico_of_mem_rowPrimes {r P x p : ℕ} (hp : p ∈ rowPrimes r P x) :
    p ∈ Finset.Ico P (2 * P) :=
  (mem_rowPrimes_iff.mp hp).1

/-- Every `p ∈ rowPrimes r P x` satisfies `2r+1 < p`. -/
lemma two_mul_r_add_one_lt_of_mem_rowPrimes {r P x p : ℕ}
    (hp : p ∈ rowPrimes r P x) : 2 * r + 1 < p :=
  (mem_rowPrimes_iff.mp hp).2.2.1

/-- Every `p ∈ rowPrimes r P x` satisfies `p ≤ r²`. -/
lemma le_r_sq_of_mem_rowPrimes {r P x p : ℕ}
    (hp : p ∈ rowPrimes r P x) : p ≤ r ^ 2 :=
  (mem_rowPrimes_iff.mp hp).2.2.2.1

/-- Every `p ∈ rowPrimes r P x` is prime. -/
lemma prime_of_mem_rowPrimes {r P x p : ℕ}
    (hp : p ∈ rowPrimes r P x) : Nat.Prime p :=
  (mem_rowPrimes_iff.mp hp).2.2.2.2.1

/-- Every `p ∈ rowPrimes r P x` divides the numerator of `H_r` (over `ℤ`). -/
lemma int_dvd_num_of_mem_rowPrimes {r P x p : ℕ}
    (hp : p ∈ rowPrimes r P x) : (p : ℤ) ∣ (harmonic r).num :=
  (mem_rowPrimes_iff.mp hp).2.2.2.2.2

/-- Every `p ∈ rowPrimes r P x` is larger than `r`. -/
lemma r_lt_of_mem_rowPrimes {r P x p : ℕ}
    (hp : p ∈ rowPrimes r P x) : r < p := by
  have h := two_mul_r_add_one_lt_of_mem_rowPrimes hp
  omega

/-- `rowPrimes` is empty when the block starts below `2`. -/
lemma rowPrimes_eq_empty_of_P_le_one {r P x : ℕ} (hP : P ≤ 1) :
    rowPrimes r P x = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    have hpIco := mem_Ico_of_mem_rowPrimes hp
    have hpPrime := prime_of_mem_rowPrimes hp
    have hlo : P ≤ p := (Finset.mem_Ico.mp hpIco).1
    have hhi : p < 2 * P := (Finset.mem_Ico.mp hpIco).2
    have hp2 : 2 ≤ p := hpPrime.two_le
    omega
  · intro hp
    simp at hp

/-- `rowPrimes` is empty when `r ≤ 1`. -/
lemma rowPrimes_eq_empty_of_r_le_one {r P x : ℕ} (hr : r ≤ 1) :
    rowPrimes r P x = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    have h2rp := two_mul_r_add_one_lt_of_mem_rowPrimes hp
    have hle := le_r_sq_of_mem_rowPrimes hp
    interval_cases r <;> norm_num at h2rp hle ⊢ <;> omega
  · intro hp
    simp at hp

/-- The row primes are prime divisors of the natural numerator `numNat r`. -/
lemma rowPrimes_subset_primeFactors {r P x : ℕ} (hr : 1 ≤ r) :
    rowPrimes r P x ⊆ (numNat r).primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors]
  have hpPrime := prime_of_mem_rowPrimes hp
  have hdvdZ := int_dvd_num_of_mem_rowPrimes hp
  refine ⟨hpPrime, ?_, ?_⟩
  · dsimp [numNat]
    exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdvdZ)
  · dsimp [numNat]
    exact ne_of_gt (numNat_pos r hr)

/-- The product of the distinct row primes divides `numNat r`. -/
lemma prod_rowPrimes_dvd_numNat (r P x : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ rowPrimes r P x, p) ∣ numNat r := by
  classical
  have hsub := rowPrimes_subset_primeFactors (r := r) (P := P) (x := x) hr
  have hsub' : (∏ p ∈ rowPrimes r P x, p) ∣
      (∏ p ∈ (numNat r).primeFactors, p) :=
    Finset.prod_dvd_prod_of_subset (rowPrimes r P x) (numNat r).primeFactors (fun p => p) hsub
  exact dvd_trans hsub' (Nat.prod_primeFactors_dvd (numNat r))

/-- The product of the distinct row primes is at most `numNat r`. -/
lemma prod_rowPrimes_le_numNat (r P x : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ rowPrimes r P x, p) ≤ numNat r :=
  Nat.le_of_dvd (numNat_pos r hr) (prod_rowPrimes_dvd_numNat r P x hr)

/-- Each row prime is at least `P`, so `P ^ #rowPrimes ≤ ∏ p`. -/
lemma pow_card_le_prod_rowPrimes (r P x : ℕ) :
    P ^ (rowPrimes r P x).card ≤ ∏ p ∈ rowPrimes r P x, p := by
  classical
  calc
    P ^ (rowPrimes r P x).card = ∏ p ∈ rowPrimes r P x, P := by
      rw [Finset.prod_const]
    _ ≤ ∏ p ∈ rowPrimes r P x, p := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      exact (Finset.mem_Ico.mp (mem_Ico_of_mem_rowPrimes hp)).1

/-- The key product chain `P ^ #rowPrimes ≤ numNat r`. -/
lemma pow_card_le_numNat (r P x : ℕ) (hr : 1 ≤ r) :
    P ^ (rowPrimes r P x).card ≤ numNat r :=
  (pow_card_le_prod_rowPrimes r P x).trans (prod_rowPrimes_le_numNat r P x hr)

/-- The product chain ending at `r * L r`. -/
lemma pow_card_le_mul_L (r P x : ℕ) (hr : 1 ≤ r) :
    P ^ (rowPrimes r P x).card ≤ r * L r :=
  (pow_card_le_numNat r P x hr).trans (numNat_le_mul_L r)

/-! ## The log-count lemma -/

/-- `log (r * L r) ≤ rowConstant * r`. -/
lemma log_mul_L_le_rowConstant (r : ℕ) (hr : 1 ≤ r) :
    Real.log ((r * L r : ℕ) : ℝ) ≤ rowConstant * (r : ℝ) := by
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
    _ = rowConstant * (r : ℝ) := by
          dsimp [rowConstant]
          ring

/-- The log-count estimate: `#rowPrimes ≤ log (r * L r) / log P`. -/
lemma rowPrimes_card_le_log_mul (r P x : ℕ) (hP : 2 ≤ P) (hr : 1 ≤ r) :
    ((rowPrimes r P x).card : ℝ) ≤
      Real.log ((r * L r : ℕ) : ℝ) / Real.log (P : ℝ) := by
  classical
  let s := rowPrimes r P x
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hPgt1 : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogPpos : 0 < Real.log (P : ℝ) := Real.log_pos hPgt1
  have hn_pos : 0 < numNat r := numNat_pos r hr
  have hpow_le : P ^ s.card ≤ numNat r := by
    dsimp [s]
    exact pow_card_le_numNat r P x hr
  have hlog_pow_le : Real.log ((P ^ s.card : ℕ) : ℝ) ≤ Real.log ((numNat r : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (pow_pos (by omega : 0 < P) s.card)
    · exact_mod_cast hpow_le
  have hlog_pow_eq : Real.log ((P ^ s.card : ℕ) : ℝ) =
      (s.card : ℝ) * Real.log (P : ℝ) := by
    rw [Nat.cast_pow]
    exact Real.log_pow (P : ℝ) s.card
  have hcard_log : (s.card : ℝ) * Real.log (P : ℝ) ≤ Real.log ((numNat r : ℕ) : ℝ) := by
    rwa [hlog_pow_eq] at hlog_pow_le
  have hnum_le : numNat r ≤ r * L r := numNat_le_mul_L r
  have hlog_num_le : Real.log ((numNat r : ℕ) : ℝ) ≤ Real.log ((r * L r : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hn_pos
    · exact_mod_cast hnum_le
  have hcard_log_le := hcard_log.trans hlog_num_le
  have hmain : (s.card : ℝ) ≤ Real.log ((r * L r : ℕ) : ℝ) / Real.log (P : ℝ) := by
    exact (le_div_iff₀ hlogPpos).2 hcard_log_le
  simpa [s] using hmain

/-- The clean log-count estimate, for `2 ≤ P` and `2 ≤ r`. -/
lemma rowPrimes_card_le (r P x : ℕ) (hP : 2 ≤ P) (hr : 2 ≤ r) :
    ((rowPrimes r P x).card : ℝ) ≤ rowConstant * (r : ℝ) / Real.log (P : ℝ) := by
  have hPgt1 : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogPpos : 0 < Real.log (P : ℝ) := Real.log_pos hPgt1
  have hlog := rowPrimes_card_le_log_mul r P x hP (by omega : 1 ≤ r)
  calc
    ((rowPrimes r P x).card : ℝ)
        ≤ Real.log ((r * L r : ℕ) : ℝ) / Real.log (P : ℝ) := hlog
    _ ≤ (rowConstant * (r : ℝ)) / Real.log (P : ℝ) := by
          exact div_le_div_of_nonneg_right (log_mul_L_le_rowConstant r (by omega))
            (le_of_lt hlogPpos)

/-- A total version of the log-count estimate with harmless constants. -/
lemma rowPrimes_card_le_total (r P x : ℕ) :
    ((rowPrimes r P x).card : ℝ) ≤
      (rowConstant + 1) * ((r : ℝ) + 1) / Real.log 2 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  by_cases hP : 2 ≤ P
  · by_cases hr : 2 ≤ r
    · have hcard := rowPrimes_card_le r P x hP hr
      have hPgt1 : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
      have hlogPpos : 0 < Real.log (P : ℝ) := Real.log_pos hPgt1
      have hlog2_le_logP : Real.log 2 ≤ Real.log (P : ℝ) := by
        exact Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (by exact_mod_cast hP : (2 : ℝ) ≤ (P : ℝ))
      have hnum : rowConstant * (r : ℝ) ≤ (rowConstant + 1) * ((r : ℝ) + 1) := by
        nlinarith [rowConstant_nonneg, (Nat.cast_nonneg r : 0 ≤ (r : ℝ))]
      have hnum_nonneg : 0 ≤ (rowConstant + 1) * ((r : ℝ) + 1) := by
        exact mul_nonneg (add_nonneg rowConstant_nonneg zero_le_one)
          (add_nonneg (Nat.cast_nonneg r) zero_le_one)
      have h1 : rowConstant * (r : ℝ) / Real.log (P : ℝ) ≤
          (rowConstant + 1) * ((r : ℝ) + 1) / Real.log (P : ℝ) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hlogPpos)
      have h2 : (rowConstant + 1) * ((r : ℝ) + 1) / Real.log (P : ℝ) ≤
          (rowConstant + 1) * ((r : ℝ) + 1) / Real.log 2 := by
        exact div_le_div_of_nonneg_left (a := (rowConstant + 1) * ((r : ℝ) + 1))
          (b := Real.log (P : ℝ)) (c := Real.log 2)
          hnum_nonneg hlog2pos hlog2_le_logP
      exact (hcard.trans h1).trans h2
    · have he : rowPrimes r P x = ∅ := rowPrimes_eq_empty_of_r_le_one (by omega)
      simp [he]
      exact div_nonneg
        (mul_nonneg (add_nonneg rowConstant_nonneg zero_le_one)
          (add_nonneg (Nat.cast_nonneg r) zero_le_one)) (le_of_lt hlog2pos)
  · have he : rowPrimes r P x = ∅ := rowPrimes_eq_empty_of_P_le_one (by omega)
    simp [he]
    exact div_nonneg
      (mul_nonneg (add_nonneg rowConstant_nonneg zero_le_one)
        (add_nonneg (Nat.cast_nonneg r) zero_le_one)) (le_of_lt hlog2pos)

/-! ## Per-block row bound -/

/-- `WmidBlock` is exactly the sum over the row-prime set. -/
lemma WmidBlock_eq_sum_rowPrimes (R P x : ℕ) :
    WmidBlock R P x =
      ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ rowPrimes r P x, (1 / ((p - 1 : ℕ) : ℝ)) := by
  unfold WmidBlock rowPrimes
  rfl

/-- For `p ≥ P` and `2 ≤ P`, the weight `1/(p-1)` is at most `1/(P-1)`. -/
lemma one_div_sub_one_le_of_ge (p P : ℕ) (hP : P ≤ p) (hP2 : 2 ≤ P) :
    (1 / ((p - 1 : ℕ) : ℝ)) ≤ (1 / ((P - 1 : ℕ) : ℝ)) := by
  have hle : P - 1 ≤ p - 1 := Nat.sub_le_sub_right hP 1
  have hPpos : 0 < ((P - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P - 1)
  have hleR : ((P - 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hle
  exact one_div_le_one_div_of_le hPpos hleR

/-- The weight bound for a member of `rowPrimes`. -/
lemma one_div_sub_one_le_of_mem_rowPrimes {r P x p : ℕ}
    (hp : p ∈ rowPrimes r P x) (hP : 2 ≤ P) :
    (1 / ((p - 1 : ℕ) : ℝ)) ≤ (1 / ((P - 1 : ℕ) : ℝ)) := by
  have hpIco := mem_Ico_of_mem_rowPrimes hp
  exact one_div_sub_one_le_of_ge p P (Finset.mem_Ico.mp hpIco).1 hP

/-- The inner `p`-sum for a fixed `r` is at most `#rowPrimes / (P - 1)`. -/
lemma inner_row_sum_le (r P x : ℕ) (hP : 2 ≤ P) :
    (∑ p ∈ rowPrimes r P x, (1 / ((p - 1 : ℕ) : ℝ))) ≤
      ((rowPrimes r P x).card : ℝ) / ((P - 1 : ℕ) : ℝ) := by
  classical
  calc
    (∑ p ∈ rowPrimes r P x, (1 / ((p - 1 : ℕ) : ℝ))) ≤
        ∑ p ∈ rowPrimes r P x, (1 / ((P - 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          exact one_div_sub_one_le_of_mem_rowPrimes hp hP
    _ = ((rowPrimes r P x).card : ℝ) * (1 / ((P - 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((rowPrimes r P x).card : ℝ) / ((P - 1 : ℕ) : ℝ) := by
          rw [mul_one_div]

/-- `WmidBlock` is at most the row-count sum. -/
lemma WmidBlock_le_row_sum (R P x : ℕ) (hP : 2 ≤ P) :
    WmidBlock R P x ≤
      ∑ r ∈ Finset.Ico R (2 * R),
        ((rowPrimes r P x).card : ℝ) / ((P - 1 : ℕ) : ℝ) := by
  rw [WmidBlock_eq_sum_rowPrimes]
  refine Finset.sum_le_sum ?_
  intro r hr
  exact inner_row_sum_le r P x hP

/-- `1/(P-1) ≤ 2/P` for `2 ≤ P`. -/
lemma one_div_sub_one_le_two_div (P : ℕ) (hP : 2 ≤ P) :
    (1 / ((P - 1 : ℕ) : ℝ)) ≤ 2 / (P : ℝ) := by
  have hPsub_pos : 0 < ((P - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P - 1)
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  rw [div_le_div_iff₀ hPsub_pos hPpos]
  have h : (P : ℝ) ≤ 2 * ((P - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : P ≤ 2 * (P - 1))
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- The row-count term `#rowPrimes / (P - 1)` is at most
`2 * rowConstant * r / (P * log P)`. -/
lemma rowPrimes_card_div_sub_one_le (r P x : ℕ) (hP : 2 ≤ P) (hr : 2 ≤ r) :
    ((rowPrimes r P x).card : ℝ) / ((P - 1 : ℕ) : ℝ) ≤
      2 * rowConstant * (r : ℝ) / ((P : ℝ) * Real.log (P : ℝ)) := by
  have hcard := rowPrimes_card_le r P x hP hr
  have hsub := one_div_sub_one_le_two_div P hP
  have hPgt1 : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hlogPpos : 0 < Real.log (P : ℝ) := Real.log_pos hPgt1
  have hnonneg : 0 ≤ rowConstant * (r : ℝ) / Real.log (P : ℝ) := by
    exact div_nonneg (mul_nonneg rowConstant_nonneg (Nat.cast_nonneg r))
      (le_of_lt hlogPpos)
  have hsub_inv : ((P - 1 : ℕ) : ℝ)⁻¹ ≤ 2 / (P : ℝ) := by
    simpa [div_eq_mul_inv] using hsub
  have h1 : ((rowPrimes r P x).card : ℝ) / ((P - 1 : ℕ) : ℝ) ≤
      (rowConstant * (r : ℝ) / Real.log (P : ℝ)) / ((P - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
  have h2 : (rowConstant * (r : ℝ) / Real.log (P : ℝ)) / ((P - 1 : ℕ) : ℝ) ≤
      (rowConstant * (r : ℝ) / Real.log (P : ℝ)) * (2 / (P : ℝ)) := by
    calc
      (rowConstant * (r : ℝ) / Real.log (P : ℝ)) / ((P - 1 : ℕ) : ℝ)
          = (rowConstant * (r : ℝ) / Real.log (P : ℝ)) * ((P - 1 : ℕ) : ℝ)⁻¹ := by
              rw [div_eq_mul_inv]
      _ ≤ (rowConstant * (r : ℝ) / Real.log (P : ℝ)) * (2 / (P : ℝ)) :=
              mul_le_mul_of_nonneg_left hsub_inv hnonneg
  have h3 : (rowConstant * (r : ℝ) / Real.log (P : ℝ)) * (2 / (P : ℝ)) =
      2 * rowConstant * (r : ℝ) / ((P : ℝ) * Real.log (P : ℝ)) := by
    field_simp [ne_of_gt hPpos, ne_of_gt hlogPpos]
  exact (h1.trans h2).trans_eq h3

/-- The sum of `r` over the dyadic `r`-block `[R, 2R)` is at most `2R²`. -/
lemma sum_r_le_two_mul_R_sq (R : ℕ) :
    (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ)) ≤ 2 * (R : ℝ) ^ 2 := by
  classical
  calc
    (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ)) ≤
        ∑ r ∈ Finset.Ico R (2 * R), (2 : ℝ) * (R : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hi := Finset.mem_Ico.mp hr
          have hle : r ≤ 2 * R := by omega
          exact_mod_cast hle
    _ = (Finset.Ico R (2 * R)).card • ((2 : ℝ) * (R : ℝ)) := by
          rw [Finset.sum_const]
    _ = (R : ℝ) * (2 * (R : ℝ)) := by
          rw [nsmul_eq_mul]
          have hcard : (Finset.Ico R (2 * R)).card = R := by
            simp
            omega
          rw [hcard]
    _ = 2 * (R : ℝ) ^ 2 := by ring

/-- The per-block row bound with explicit constant. -/
lemma WmidBlock_le_constant (R P x : ℕ) (hR : 2 ≤ R) (hP : 2 ≤ P) :
    WmidBlock R P x ≤ blockConstant * (R : ℝ) ^ 2 / ((P : ℝ) * Real.log (P : ℝ)) := by
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hPgt1 : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogPpos : 0 < Real.log (P : ℝ) := Real.log_pos hPgt1
  have hprodpos : 0 < (P : ℝ) * Real.log (P : ℝ) := mul_pos hPpos hlogPpos
  have hcoef_nonneg : 0 ≤ 2 * rowConstant / ((P : ℝ) * Real.log (P : ℝ)) := by
    exact div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) rowConstant_nonneg)
      (le_of_lt hprodpos)
  calc
    WmidBlock R P x ≤
        ∑ r ∈ Finset.Ico R (2 * R),
          ((rowPrimes r P x).card : ℝ) / ((P - 1 : ℕ) : ℝ) :=
          WmidBlock_le_row_sum R P x hP
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
          2 * rowConstant * (r : ℝ) / ((P : ℝ) * Real.log (P : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hi := Finset.mem_Ico.mp hr
          exact rowPrimes_card_div_sub_one_le r P x hP (by omega : 2 ≤ r)
    _ = ∑ r ∈ Finset.Ico R (2 * R),
          (2 * rowConstant / ((P : ℝ) * Real.log (P : ℝ))) * (r : ℝ) := by
          apply Finset.sum_congr rfl
          intro r hr
          field_simp [ne_of_gt hPpos, ne_of_gt hlogPpos]
    _ = (2 * rowConstant / ((P : ℝ) * Real.log (P : ℝ))) *
          ∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) := by
          rw [← Finset.mul_sum]
    _ ≤ (2 * rowConstant / ((P : ℝ) * Real.log (P : ℝ))) * (2 * (R : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left (sum_r_le_two_mul_R_sq R) hcoef_nonneg
    _ = blockConstant * (R : ℝ) ^ 2 / ((P : ℝ) * Real.log (P : ℝ)) := by
          dsimp [blockConstant]
          field_simp [ne_of_gt hPpos, ne_of_gt hlogPpos]
          ring

/-! ## Dyadic summation -/

/-- `WmidBlock R 1 x = 0`: the block `[1, 2)` contains no primes. -/
lemma WmidBlock_eq_zero_of_P_le_one (R P x : ℕ) (hP : P ≤ 1) :
    WmidBlock R P x = 0 := by
  rw [WmidBlock_eq_sum_rowPrimes]
  apply Finset.sum_eq_zero
  intro r hr
  rw [rowPrimes_eq_empty_of_P_le_one (r := r) (P := P) (x := x) hP]
  simp

/-- If `k ≤ Nat.log 2 R`, the dyadic block `P = 2^k` is below the middle range,
so it contributes zero. -/
lemma WmidBlock_eq_zero_of_k_le_log (R x k : ℕ) (hR : 2 ≤ R)
    (hk : k ≤ Nat.log 2 R) :
    WmidBlock R (2 ^ k) x = 0 := by
  apply WmidBlock_eq_zero_of_not_mid_range
  left
  have hRne : R ≠ 0 := by omega
  have hpow : 2 ^ k ≤ R := Nat.pow_le_of_le_log hRne hk
  omega

/-- For `1 ≤ k`, `2 ≤ 2^k`. -/
lemma two_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  have hpow : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
  simpa using hpow

/-- The dyadic-block version of the row bound. -/
lemma WmidBlock_le_dyadicTerm (R x k : ℕ) (hR : 2 ≤ R) (hk : 1 ≤ k) :
    WmidBlock R (2 ^ k) x ≤
      blockConstant * (R : ℝ) ^ 2 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)) := by
  have hP : 2 ≤ 2 ^ k := two_le_two_pow hk
  have hmain := WmidBlock_le_constant R (2 ^ k) x hR hP
  simpa [Nat.cast_pow] using hmain

/-- The geometric-harmonic dyadic sum bound: for `0 < K`,
`∑_{k=K}^N 1/(2^k log(2^k)) ≤ 2/(2^K log(2^K))`. -/
lemma sum_inv_two_pow_log_le (K N : ℕ) (hK : 0 < K) :
    (∑ k ∈ Finset.Icc K N,
        (1 : ℝ) / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))) ≤
      2 / ((2 : ℝ) ^ K * Real.log ((2 : ℝ) ^ K)) := by
  classical
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hKpow_pos : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num : (0 : ℝ) < 2) K
  have hKne : K ≠ 0 := by omega
  have hKpow_gt1 : 1 < (2 : ℝ) ^ K :=
    one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hKne
  have hlogKpos : 0 < Real.log ((2 : ℝ) ^ K) := Real.log_pos hKpow_gt1
  have hsub : Finset.Icc K N ⊆ Finset.Ico K (N + 1) := by
    intro k hk
    rw [Finset.mem_Ico]
    have hk' := Finset.mem_Icc.mp hk
    omega
  have hsum_sub : (∑ k ∈ Finset.Icc K N, (1 : ℝ) / (2 : ℝ) ^ k) ≤
      ∑ k ∈ Finset.Ico K (N + 1), (1 : ℝ) / (2 : ℝ) ^ k :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro k hk hknot
      positivity)
  have hgeom := geom_sum_Ico_le_of_lt_one (m := K) (n := N + 1) (x := (1 / 2 : ℝ))
    (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)
  have hgeom' : (∑ k ∈ Finset.Ico K (N + 1), (1 : ℝ) / (2 : ℝ) ^ k) ≤
      2 / (2 : ℝ) ^ K := by
    calc
      (∑ k ∈ Finset.Ico K (N + 1), (1 : ℝ) / (2 : ℝ) ^ k) =
          ∑ k ∈ Finset.Ico K (N + 1), (1 / 2 : ℝ) ^ k := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← one_div_pow]
      _ ≤ (1 / 2 : ℝ) ^ K / (1 - 1 / 2) := hgeom
      _ = 2 / (2 : ℝ) ^ K := by
            rw [one_div_pow]
            norm_num
            ring
  have hsum_geom : (∑ k ∈ Finset.Icc K N, (1 : ℝ) / (2 : ℝ) ^ k) ≤ 2 / (2 : ℝ) ^ K :=
    hsum_sub.trans hgeom'
  calc
    (∑ k ∈ Finset.Icc K N,
        (1 : ℝ) / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))) ≤
        ∑ k ∈ Finset.Icc K N,
          (1 : ℝ) / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ K)) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hkK : K ≤ k := (Finset.mem_Icc.mp hk).1
          have hkpos : 0 < k := lt_of_lt_of_le hK hkK
          have hkne : k ≠ 0 := by omega
          have hpowk_pos : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num : (0 : ℝ) < 2) k
          have hpowk_gt1 : 1 < (2 : ℝ) ^ k :=
            one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hkne
          have hlogkpos : 0 < Real.log ((2 : ℝ) ^ k) := Real.log_pos hpowk_gt1
          have hlog_le : Real.log ((2 : ℝ) ^ K) ≤ Real.log ((2 : ℝ) ^ k) := by
            exact Real.log_le_log hKpow_pos
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) hkK)
          have hden : (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ K) ≤
              (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left hlog_le (le_of_lt hpowk_pos)
          exact one_div_le_one_div_of_le
            (mul_pos hpowk_pos hlogKpos) hden
    _ = ∑ k ∈ Finset.Icc K N,
          (1 / Real.log ((2 : ℝ) ^ K)) * (1 / (2 : ℝ) ^ k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hpowk_ne : (2 : ℝ) ^ k ≠ 0 :=
            ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) k)
          field_simp [hpowk_ne, ne_of_gt hlogKpos]
    _ = (1 / Real.log ((2 : ℝ) ^ K)) *
          ∑ k ∈ Finset.Icc K N, (1 / (2 : ℝ) ^ k) := by
          rw [Finset.mul_sum]
    _ ≤ (1 / Real.log ((2 : ℝ) ^ K)) * (2 / (2 : ℝ) ^ K) := by
          exact mul_le_mul_of_nonneg_left hsum_geom
            (le_of_lt (one_div_pos.mpr hlogKpos))
    _ = 2 / ((2 : ℝ) ^ K * Real.log ((2 : ℝ) ^ K)) := by
          field_simp [ne_of_gt hKpow_pos, ne_of_gt hlogKpos]

/-- The dyadic sum of the row bound is `≤ dyadicConstant * R / log R`. -/
lemma sum_dyadic_terms_le (R : ℕ) (hR : 2 ≤ R) :
    (∑ k ∈ Finset.Icc (Nat.log 2 R + 1) (Nat.log 2 (4 * R ^ 2)),
        blockConstant * (R : ℝ) ^ 2 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))) ≤
      dyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
  let K := Nat.log 2 R + 1
  let N := Nat.log 2 (4 * R ^ 2)
  have hKpos : 0 < K := by dsimp [K]; omega
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRgt1 : (1 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hRgt1
  have hR_lt_two_pow_K : R < 2 ^ K := by
    dsimp [K]
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) R)
  have hR_le_two_pow_K : (R : ℝ) ≤ (2 : ℝ) ^ K := by
    exact_mod_cast (le_of_lt hR_lt_two_pow_K)
  have hKpow_pos : 0 < (2 : ℝ) ^ K := pow_pos (by norm_num : (0 : ℝ) < 2) K
  have hKne : K ≠ 0 := by dsimp [K]; omega
  have hKpow_gt1 : 1 < (2 : ℝ) ^ K :=
    one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hKne
  have hlogKpos : 0 < Real.log ((2 : ℝ) ^ K) := Real.log_pos hKpow_gt1
  have hlogR_le_logK : Real.log (R : ℝ) ≤ Real.log ((2 : ℝ) ^ K) :=
    Real.log_le_log hRpos hR_le_two_pow_K
  have hRden_le : (R : ℝ) * Real.log (R : ℝ) ≤
      (2 : ℝ) ^ K * Real.log ((2 : ℝ) ^ K) :=
    mul_le_mul hR_le_two_pow_K hlogR_le_logK (le_of_lt hlogRpos) (le_of_lt hKpow_pos)
  have hsum_inv := sum_inv_two_pow_log_le K N hKpos
  calc
    (∑ k ∈ Finset.Icc K N,
        blockConstant * (R : ℝ) ^ 2 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))) =
        (blockConstant * (R : ℝ) ^ 2) *
          ∑ k ∈ Finset.Icc K N,
            (1 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [div_eq_mul_inv, one_div]
    _ ≤ (blockConstant * (R : ℝ) ^ 2) *
          (2 / ((2 : ℝ) ^ K * Real.log ((2 : ℝ) ^ K))) := by
          exact mul_le_mul_of_nonneg_left hsum_inv
            (mul_nonneg blockConstant_nonneg (sq_nonneg (R : ℝ)))
    _ ≤ (blockConstant * (R : ℝ) ^ 2) *
          (2 / ((R : ℝ) * Real.log (R : ℝ))) := by
          have h2inv : 2 / ((2 : ℝ) ^ K * Real.log ((2 : ℝ) ^ K)) ≤
              2 / ((R : ℝ) * Real.log (R : ℝ)) :=
            div_le_div_of_nonneg_left (a := 2)
              (b := (2 : ℝ) ^ K * Real.log ((2 : ℝ) ^ K))
              (c := (R : ℝ) * Real.log (R : ℝ))
              (by norm_num : 0 ≤ (2 : ℝ))
              (mul_pos hRpos hlogRpos) hRden_le
          exact mul_le_mul_of_nonneg_left h2inv
            (mul_nonneg blockConstant_nonneg (sq_nonneg (R : ℝ)))
    _ = dyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
          dsimp [dyadicConstant]
          field_simp [ne_of_gt hRpos, ne_of_gt hlogRpos]

/-- The unconditional dyadic row bound for `Wmid`. -/
theorem Wmid_le_dyadic_constant (R x : ℕ) (hR : 2 ≤ R) :
    Wmid R x ≤ dyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
  let K := Nat.log 2 R + 1
  let N := Nat.log 2 (4 * R ^ 2)
  let f : ℕ → ℝ := fun k =>
    if k ≤ Nat.log 2 R then 0
    else blockConstant * (R : ℝ) ^ 2 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k))
  have hf_zero : ∀ k, k ≤ Nat.log 2 R → f k = 0 := by
    intro k hk
    dsimp [f]
    rw [ite_eq_left hk]
  have hf_pos : ∀ k, ¬ k ≤ Nat.log 2 R → f k =
      blockConstant * (R : ℝ) ^ 2 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)) := by
    intro k hk
    dsimp [f]
    rw [ite_eq_right hk]
  have hIcc_sub : Finset.Icc K N ⊆ Finset.range (Nat.log 2 (4 * R ^ 2) + 1) := by
    intro k hk
    rw [Finset.mem_range]
    have hk' := Finset.mem_Icc.mp hk
    dsimp [N] at hk'
    omega
  have hsum_f_eq : (∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1), f k) =
      ∑ k ∈ Finset.Icc K N, f k := by
    refine (Finset.sum_subset hIcc_sub ?_).symm
    intro k hkrange hknot
    have hk_le : k ≤ Nat.log 2 R := by
      have hkN : k ≤ N := by
        rw [Finset.mem_range] at hkrange
        omega
      have hkIcc : ¬ (K ≤ k ∧ k ≤ N) := by
        intro h
        exact hknot (Finset.mem_Icc.mpr h)
      dsimp [K] at hkIcc
      omega
    exact hf_zero k hk_le
  calc
    Wmid R x = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        WmidBlock R (2 ^ k) x := Wmid_eq_sum_dyadic R x
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1), f k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          by_cases hk_le : k ≤ Nat.log 2 R
          · have hzero : WmidBlock R (2 ^ k) x = 0 :=
              WmidBlock_eq_zero_of_k_le_log R x k hR hk_le
            rw [hf_zero k hk_le]
            exact le_of_eq hzero
          · have hk_ge : Nat.log 2 R < k := Nat.lt_of_not_ge hk_le
            have hk1 : 1 ≤ k := by omega
            have hblock := WmidBlock_le_dyadicTerm R x k hR hk1
            rw [hf_pos k (by omega)]
            exact hblock
    _ = ∑ k ∈ Finset.Icc K N, f k := hsum_f_eq
    _ ≤ ∑ k ∈ Finset.Icc K N,
        blockConstant * (R : ℝ) ^ 2 / ((2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k)) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hk' := Finset.mem_Icc.mp hk
          have hk_not_le : ¬ k ≤ Nat.log 2 R := by
            dsimp [K] at hk'
            omega
          exact le_of_eq (hf_pos k hk_not_le)
    _ ≤ dyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
          dsimp [K, N]
          exact sum_dyadic_terms_le R hR

/-! ## The row bound does not tend to zero -/

/-- A simple lower bound `(1/2)√R ≤ R / log R` for `R ≥ 2`. -/
lemma sqrt_half_le_div_log (R : ℕ) (hR : 2 ≤ R) :
    (1 / 2 : ℝ) * Real.sqrt (R : ℝ) ≤ (R : ℝ) / Real.log (R : ℝ) := by
  have hRpos : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRgt1 : 1 < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlogpos : 0 < Real.log (R : ℝ) := Real.log_pos hRgt1
  have hsqrt_pos : 0 < Real.sqrt (R : ℝ) := Real.sqrt_pos.mpr hRpos
  have hlog_sqrt_le : Real.log (Real.sqrt (R : ℝ)) ≤ Real.sqrt (R : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hsqrt_pos
  have hlog_le_two_sqrt : Real.log (R : ℝ) ≤ 2 * Real.sqrt (R : ℝ) := by
    have hlog_sqrt_eq : Real.log (Real.sqrt (R : ℝ)) = Real.log (R : ℝ) / 2 :=
      Real.log_sqrt (le_of_lt hRpos)
    have h1 : Real.log (R : ℝ) / 2 ≤ Real.sqrt (R : ℝ) := by
      calc
        Real.log (R : ℝ) / 2 = Real.log (Real.sqrt (R : ℝ)) := by rw [hlog_sqrt_eq]
        _ ≤ Real.sqrt (R : ℝ) - 1 := hlog_sqrt_le
        _ ≤ Real.sqrt (R : ℝ) := by linarith
    linarith
  have hmul : (1 / 2 : ℝ) * Real.sqrt (R : ℝ) * Real.log (R : ℝ) ≤ (R : ℝ) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (R : ℝ) := le_of_lt hsqrt_pos
    calc
      (1 / 2 : ℝ) * Real.sqrt (R : ℝ) * Real.log (R : ℝ) ≤
          (1 / 2 : ℝ) * Real.sqrt (R : ℝ) * (2 * Real.sqrt (R : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hlog_le_two_sqrt
              (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (R : ℝ))
      _ = (Real.sqrt (R : ℝ)) ^ 2 := by ring
      _ = R := Real.sq_sqrt (le_of_lt hRpos)
  exact (le_div_iff₀ hlogpos).2 (by simpa [mul_assoc] using hmul)

/-- `R / log R` tends to `atTop` along the naturals. -/
lemma R_div_log_tendsto_atTop :
    Tendsto (fun R : ℕ => (R : ℝ) / Real.log (R : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' (l := atTop)
    (f₁ := fun R : ℕ => (1 / 2 : ℝ) * Real.sqrt (R : ℝ))
    (f₂ := fun R : ℕ => (R : ℝ) / Real.log (R : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with R hR
    exact sqrt_half_le_div_log R hR
  · have hsqrt : Tendsto (fun R : ℕ => Real.sqrt (R : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    exact (tendsto_const_mul_atTop_of_pos (by norm_num : 0 < (1 / 2 : ℝ))).2 hsqrt

/-- The dyadic row bound tends to `atTop` (not to zero). -/
lemma dyadicBound_tendsto_atTop :
    Tendsto (fun R : ℕ => dyadicConstant * (R : ℝ) / Real.log (R : ℝ)) atTop atTop := by
  have hdyad_pos : 0 < dyadicConstant := dyadicConstant_pos
  have hmain := R_div_log_tendsto_atTop
  have hcongr : (fun R : ℕ => dyadicConstant * (R : ℝ) / Real.log (R : ℝ)) =
      fun R : ℕ => dyadicConstant * ((R : ℝ) / Real.log (R : ℝ)) := by
    funext R
    ring
  rw [hcongr]
  exact (tendsto_const_mul_atTop_of_pos hdyad_pos).2 hmain

/-- Consequently the bound `dyadicConstant * R / log R` does **not** tend to zero. -/
lemma dyadicBound_not_tendsto_zero :
    ¬ Tendsto (fun R : ℕ => dyadicConstant * (R : ℝ) / Real.log (R : ℝ)) atTop (𝓝 0) := by
  intro h
  have htop := dyadicBound_tendsto_atTop
  have hge : ∀ᶠ R : ℕ in atTop,
      (1 : ℝ) ≤ dyadicConstant * (R : ℝ) / Real.log (R : ℝ) := by
    exact (Filter.tendsto_atTop.mp htop) 1
  have hlt : ∀ᶠ R : ℕ in atTop,
      dyadicConstant * (R : ℝ) / Real.log (R : ℝ) < 1 := by
    exact h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hboth : ∀ᶠ R : ℕ in atTop,
      (1 : ℝ) ≤ dyadicConstant * (R : ℝ) / Real.log (R : ℝ) ∧
        dyadicConstant * (R : ℝ) / Real.log (R : ℝ) < 1 :=
    hge.and hlt
  have hfalse : ∀ᶠ R : ℕ in atTop, False := hboth.mono (by
    intro R hR
    linarith)
  have hbot : atTop = ⊥ := Filter.eventually_false_iff_eq_bot.mp hfalse
  exact Filter.atTop_neBot.ne hbot

/-! ## Conditional capstone -/

/-- The remaining open target, packaged as an explicit Prop hypothesis: the
middle block `Wmid` vanishes uniformly in `x` as `R → ∞`. -/
def HA_row_dyadic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ ε

/-- If a future sharper row bound proves `HA_row_dyadic`, then `Wmid` vanishes
uniformly. -/
theorem Wmid_uniformly_tends_to_zero_of_row_bound (hrow : HA_row_dyadic) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ ε :=
  hrow

/-- And then the full dyadic block sum `W` vanishes uniformly. -/
theorem W_uniformly_tends_to_zero_of_HA_row_dyadic (hrow : HA_row_dyadic) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ ε :=
  W_uniformly_tends_to_zero_of_Wmid_uniformly_tends_to_zero
    (Wmid_uniformly_tends_to_zero_of_row_bound hrow)

end

end Erdos291
