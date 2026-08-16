import Erdos291.MiddleRowMassBound
import Erdos291.MertensUpper
import Erdos291.SecondMomentPrimeMass
import Erdos291.MidBlockRestrictions

/-!
# Erdős #291 — the LOW / MID / HIGH regime decomposition of `Wmid`

This file splits the middle-block mass `Wmid` according to the size of the
prime `p` relative to the dyadic block parameter `R`:

* **LOW** `p ≤ 4R`: controlled unconditionally by the prime-counting bound
  `π(4R) ≤ lowPrimeCountConstant · R / log(2R)` plus the hard
  `WmidWeightedRowSumLowCardGe3` term (the contribution of primes with at
  least three middle-active digits).  The LOW digit ratio satisfies
  `r / (p-1) < 1/2`, so primes with at most two digits contribute at most `1`.
* **MID** `4R < p ≤ R²`: this is the hard regime, where the 3-separation
  theorems in `MidBlockRestrictions.lean` are designed to be applied.  It is
  not bounded unconditionally in this file.
* **HIGH** `R² < p`: controlled unconditionally by the numerator-height bound
  `middlePrimesHigh_card_le` (from `MiddleRowMassBound`) and the trivial weight
  bound `1/(p-1) ≤ 2/R²`.

The unconditional constants are

  `lowPrimeCountConstant = 4 * primeCountingConst ≈ 19.090354888959`
  `highRegimeConstant = 4 * middleRowConstant ≈ 25.545177444480`

(using `primeCountingConst = 2 log 4 + 2` and `middleRowConstant = log 4 + 5`).

The two remaining hypotheses are

* `HA_Wmid_low_high_bound`: `WmidLow R x + WmidHigh R x ≤ 0.027` for
  `R ≥ 18`.  Evidence: exact C computation gives the maximum
  `0.023679098679` at `R = 18` over `R = 18..1999`.
* `HA_Wmid_mid_constant_bound`: `WmidMid R x ≤ 0.045` for `R ≥ 18`.
  Evidence: exact C computation gives the maximum `0.043368692020` at
  `R = 242` over `R = 18..1999`.

The capstone combines these with the unconditional LOW/HIGH bounds:

  `HA_Wmid_constant_bound` holds with `R₀ = 18`, `C = 0.072`; indeed
  `0.072 · 8 = 0.576 < 0.6931471803 < log 2`.

The MID 3-separation theorems live in `MidBlockRestrictions.lean`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-! ## Regime decompositions of the row mass -/

/-- The LOW row mass: middle primes `p ≤ 4R`. -/
noncomputable def middleRowMassLow (R r x : ℕ) : ℝ :=
  ∑ p ∈ (middlePrimes r x).filter (fun p => p ≤ 4 * R), primeWeight p

/-- The MID row mass: middle primes `4R < p ≤ R²`. -/
noncomputable def middleRowMassMid (R r x : ℕ) : ℝ :=
  ∑ p ∈ (middlePrimes r x).filter (fun p => 4 * R < p ∧ p ≤ R ^ 2), primeWeight p

/-- The HIGH row mass: middle primes `R² < p`. -/
noncomputable def middleRowMassHigh (R r x : ℕ) : ℝ :=
  ∑ p ∈ (middlePrimes r x).filter (fun p => R ^ 2 < p), primeWeight p

/-- The LOW block mass. -/
noncomputable def WmidLow (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), middleRowMassLow R r x

/-- The MID block mass. -/
noncomputable def WmidMid (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), middleRowMassMid R r x

/-- The HIGH block mass. -/
noncomputable def WmidHigh (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), middleRowMassHigh R r x

/-- The LOW weighted row sum. -/
noncomputable def WmidWeightedRowSumLow (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassLow R r x

/-- The MID weighted row sum. -/
noncomputable def WmidWeightedRowSumMid (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassMid R r x

/-- The HIGH weighted row sum. -/
noncomputable def WmidWeightedRowSumHigh (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassHigh R r x

/-- The part of the LOW weighted row sum coming from primes with at least
three middle-active digits in `[R, 2R)`.  For such primes `p > 2R` (any
middle-active digit `r` satisfies `2r + 1 < p` and `r ≥ R`), so the condition
`2 * R < p` is redundant but useful for later MID restrictions. -/
noncomputable def WmidWeightedRowSumLowCardGe3 (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter
      (fun p => 2 * R < p ∧ p ≤ 4 * R ∧ Nat.Prime p ∧ 3 ≤ (middleActiveDigits R p).card),
    ∑ r ∈ middleActiveDigits R p, (r : ℝ) * primeWeight p

/-- The HIGH middle primes of a row, saturated at `x = 4R²`. -/
noncomputable def middlePrimesHigh (R r : ℕ) : Finset ℕ :=
  (middlePrimes r (4 * R ^ 2)).filter (fun p => R ^ 2 < p)

/-- The LOW prime-counting constant `4 * primeCountingConst`. -/
noncomputable def lowPrimeCountConstant : ℝ := 4 * primeCountingConst

/-- The HIGH regime constant `4 * middleRowConstant`. -/
noncomputable def highRegimeConstant : ℝ := 4 * middleRowConstant

/-! ## Nonnegativity of the regime row masses -/

lemma middleRowMassLow_nonneg (R r x : ℕ) : 0 ≤ middleRowMassLow R r x := by
  unfold middleRowMassLow
  exact Finset.sum_nonneg (by
    intro p hp
    dsimp [primeWeight]
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

lemma middleRowMassMid_nonneg (R r x : ℕ) : 0 ≤ middleRowMassMid R r x := by
  unfold middleRowMassMid
  exact Finset.sum_nonneg (by
    intro p hp
    dsimp [primeWeight]
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

lemma middleRowMassHigh_nonneg (R r x : ℕ) : 0 ≤ middleRowMassHigh R r x := by
  unfold middleRowMassHigh
  exact Finset.sum_nonneg (by
    intro p hp
    dsimp [primeWeight]
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

/-! ## Decompositions -/

/-- The row mass splits into LOW + MID + HIGH. -/
lemma middleRowMass_eq_low_add_mid_add_high (R r x : ℕ) (hR : 4 ≤ R) :
    middleRowMass r x = middleRowMassLow R r x + middleRowMassMid R r x + middleRowMassHigh R r x := by
  classical
  unfold middleRowMassLow middleRowMassMid middleRowMassHigh
  rw [middleRowMass_eq_sum_middlePrimes]
  let s : Finset ℕ := middlePrimes r x
  have hsplit1 := Finset.sum_filter_add_sum_filter_not (s := s)
    (p := fun p => p ≤ 4 * R) (f := primeWeight)
  have hnot : s.filter (fun p => ¬ p ≤ 4 * R) = s.filter (fun p => 4 * R < p) := by
    ext p
    simp only [Finset.mem_filter]
    constructor <;> intro hp <;> exact ⟨hp.1, by omega⟩
  have hsplit1' : (∑ p ∈ s.filter (fun p => p ≤ 4 * R), primeWeight p)
      + (∑ p ∈ s.filter (fun p => 4 * R < p), primeWeight p)
      = ∑ p ∈ s, primeWeight p := by
    simpa [hnot] using hsplit1
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    (s := s.filter (fun p => 4 * R < p))
    (p := fun p => p ≤ R ^ 2) (f := primeWeight)
  have hmid_eq : (s.filter (fun p => 4 * R < p)).filter (fun p => p ≤ R ^ 2)
      = s.filter (fun p => 4 * R < p ∧ p ≤ R ^ 2) := by
    rw [Finset.filter_filter]
  have hhigh_eq : (s.filter (fun p => 4 * R < p)).filter (fun p => ¬ p ≤ R ^ 2)
      = s.filter (fun p => R ^ 2 < p) := by
    rw [Finset.filter_filter]
    ext p
    simp only [Finset.mem_filter]
    constructor
    · intro hp
      exact ⟨hp.1, not_le.mp hp.2.2⟩
    · intro hp
      have h4R_le_R2 : 4 * R ≤ R ^ 2 := by nlinarith
      exact ⟨hp.1, by omega, by omega⟩
  have hsplit2' : (∑ p ∈ s.filter (fun p => 4 * R < p ∧ p ≤ R ^ 2), primeWeight p)
      + (∑ p ∈ s.filter (fun p => R ^ 2 < p), primeWeight p)
      = ∑ p ∈ s.filter (fun p => 4 * R < p), primeWeight p := by
    rw [← hmid_eq, ← hhigh_eq]
    exact hsplit2
  calc
    middleRowMass r x = ∑ p ∈ s, primeWeight p := by rfl
    _ = (∑ p ∈ s.filter (fun p => p ≤ 4 * R), primeWeight p)
        + (∑ p ∈ s.filter (fun p => 4 * R < p), primeWeight p) := by rw [hsplit1']
    _ = (∑ p ∈ s.filter (fun p => p ≤ 4 * R), primeWeight p)
        + ((∑ p ∈ s.filter (fun p => 4 * R < p ∧ p ≤ R ^ 2), primeWeight p)
          + (∑ p ∈ s.filter (fun p => R ^ 2 < p), primeWeight p)) := by
          rw [hsplit2']
    _ = middleRowMassLow R r x + middleRowMassMid R r x + middleRowMassHigh R r x := by
          simp [s, middleRowMassLow, middleRowMassMid, middleRowMassHigh, add_assoc]

/-- The block mass splits into LOW + MID + HIGH. -/
lemma Wmid_eq_low_add_mid_add_high (R x : ℕ) (hR : 4 ≤ R) :
    Wmid R x = WmidLow R x + WmidMid R x + WmidHigh R x := by
  classical
  calc
    Wmid R x = ∑ r ∈ Finset.Ico R (2 * R), middleRowMass r x := by rfl
    _ = ∑ r ∈ Finset.Ico R (2 * R),
          (middleRowMassLow R r x + middleRowMassMid R r x + middleRowMassHigh R r x) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [middleRowMass_eq_low_add_mid_add_high R r x hR]
    _ = WmidLow R x + WmidMid R x + WmidHigh R x := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp [WmidLow, WmidMid, WmidHigh, add_assoc]

/-- The weighted row sum splits into LOW + MID + HIGH. -/
lemma WmidWeightedRowSum_eq_low_add_mid_add_high (R x : ℕ) (hR : 4 ≤ R) :
    WmidWeightedRowSum R x =
      WmidWeightedRowSumLow R x + WmidWeightedRowSumMid R x + WmidWeightedRowSumHigh R x := by
  classical
  calc
    WmidWeightedRowSum R x = ∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMass r x := by rfl
    _ = ∑ r ∈ Finset.Ico R (2 * R),
          ((r : ℝ) * middleRowMassLow R r x + (r : ℝ) * middleRowMassMid R r x
            + (r : ℝ) * middleRowMassHigh R r x) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [middleRowMass_eq_low_add_mid_add_high R r x hR]
          ring
    _ = WmidWeightedRowSumLow R x + WmidWeightedRowSumMid R x + WmidWeightedRowSumHigh R x := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp [WmidWeightedRowSumLow, WmidWeightedRowSumMid, WmidWeightedRowSumHigh]

/-! ## LOW regime -/

/-- In the LOW regime every middle digit satisfies `r / (p - 1) < 1/2`. -/
lemma low_digit_ratio_lt_half (R r p : ℕ) (hR : 4 ≤ R)
    (hr : r ∈ Finset.Ico R (2 * R)) (h2rp : 2 * r + 1 < p) :
    (r : ℝ) / ((p - 1 : ℕ) : ℝ) < 1 / 2 := by
  have hp2 : 2 ≤ p := by omega
  have hp1pos : 0 < p - 1 := by omega
  have hden : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp1pos
  have h2r_lt : 2 * r < p - 1 := by omega
  have hcast : ((2 * r : ℕ) : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h2r_lt
  have h2rR : (2 : ℝ) * (r : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_mul] at hcast ⊢
    exact hcast
  rw [div_lt_iff₀ hden]
  nlinarith

/-- In the LOW regime `p ≤ 4R ≤ R² ≤ r²`. -/
lemma low_prime_le_sq (R r p : ℕ) (hR : 4 ≤ R) (hr : R ≤ r) (hp : p ≤ 4 * R) :
    p ≤ r ^ 2 := by
  have h1 : 4 * R ≤ R ^ 2 := by nlinarith
  have h2 : R ^ 2 ≤ r ^ 2 := by nlinarith
  exact le_trans hp (le_trans h1 h2)

/-! The LOW reindexing: the weighted row sum is controlled by the sum over
primes of their middle-active digits, each digit contributing `r/(p-1)`. -/

private lemma WmidWeightedRowSumLow_le_sum_middleActiveDigits_weight (R x : ℕ) :
    WmidWeightedRowSumLow R x ≤
      ∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R),
        ∑ r ∈ middleActiveDigits R p, (r : ℝ) * primeWeight p := by
  classical
  let P : Finset ℕ := (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R)
  have mem_digits {r p : ℕ} (hr : r ∈ Finset.Ico R (2 * R))
      (hp : p ∈ middlePrimes r x) : r ∈ middleActiveDigits R p := by
    have hpF := mem_middlePrimes_iff.mp hp
    have hrI := Finset.mem_Ico.mp hr
    have h1r : 1 ≤ r := by omega
    have hrp : r < p := by omega
    have hrE : r ∈ E p := (mem_E_iff_dvd_num p r hpF.2.2.2.1 h1r hrp).mpr hpF.2.2.2.2
    exact Finset.mem_filter.mpr ⟨hrE, by refine ⟨hrI.1, hrI.2, hpF.2.1, hpF.2.2.1⟩⟩
  have hinner_le (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      (r : ℝ) * middleRowMassLow R r x ≤
        ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), (r : ℝ) * primeWeight p := by
    unfold middleRowMassLow
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpMid : p ∈ middlePrimes r x := hpF.1
      have hple : p ≤ 4 * R := hpF.2
      have hpMidF := mem_middlePrimes_iff.mp hpMid
      have hpP : p ∈ P := by
        exact Finset.mem_filter.mpr ⟨hpMidF.1, ⟨hpMidF.2.2.2.1, hple⟩⟩
      exact Finset.mem_filter.mpr ⟨hpP, mem_digits hr hpMid⟩
    · intro p hp hpnot
      exact mul_nonneg (Nat.cast_nonneg r) (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))
  calc
    WmidWeightedRowSumLow R x = ∑ r ∈ Finset.Ico R (2 * R),
        (r : ℝ) * middleRowMassLow R r x := by rfl
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), (r : ℝ) * primeWeight p := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact hinner_le r hr
    _ = ∑ p ∈ P,
        ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
          (r : ℝ) * primeWeight p := by
          calc
            (∑ r ∈ Finset.Ico R (2 * R),
                ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), (r : ℝ) * primeWeight p)
                = ∑ r ∈ Finset.Ico R (2 * R),
                    ∑ p ∈ P, (if r ∈ middleActiveDigits R p then (r : ℝ) * primeWeight p else 0) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    rw [Finset.sum_filter]
            _ = ∑ p ∈ P,
                  ∑ r ∈ Finset.Ico R (2 * R),
                    (if r ∈ middleActiveDigits R p then (r : ℝ) * primeWeight p else 0) := by
                    rw [Finset.sum_comm]
            _ = ∑ p ∈ P,
                  ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
                    (r : ℝ) * primeWeight p := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    rw [Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ r ∈ middleActiveDigits R p, (r : ℝ) * primeWeight p := by
          apply Finset.sum_congr rfl
          intro p hp
          have hfilter : (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p)
              = middleActiveDigits R p := by
            ext r
            constructor
            · intro hr
              exact (Finset.mem_filter.mp hr).2
            · intro hr
              have hrF := Finset.mem_filter.mp hr
              exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hrF.2.1, hrF.2.2.1⟩, hr⟩
          rw [hfilter]

/-- The LOW weighted row sum is at most `π(4R)` plus the card-≥3 part. -/
lemma WmidWeightedRowSumLow_le_pi_fourR_add_cardGe3 (R x : ℕ) (hR : 4 ≤ R) :
    WmidWeightedRowSumLow R x ≤ (Nat.primeCounting (4 * R) : ℝ) + WmidWeightedRowSumLowCardGe3 R x := by
  classical
  let P : Finset ℕ := (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R)
  let inner : ℕ → ℝ := fun p => ∑ r ∈ middleActiveDigits R p, (r : ℝ) * primeWeight p
  have hreindex := WmidWeightedRowSumLow_le_sum_middleActiveDigits_weight R x
  have hle_two : (∑ p ∈ P.filter (fun p => (middleActiveDigits R p).card ≤ 2), inner p)
      ≤ ∑ p ∈ P.filter (fun p => (middleActiveDigits R p).card ≤ 2), (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpP := (Finset.mem_filter.mp hp).1
    have hcard := (Finset.mem_filter.mp hp).2
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hpP).2.1
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hterm_le (r : ℕ) (hr : r ∈ middleActiveDigits R p) :
        (r : ℝ) * primeWeight p ≤ 1 / 2 := by
      have hrF := Finset.mem_filter.mp hr
      have hrIco : r ∈ Finset.Ico R (2 * R) := Finset.mem_Ico.mpr ⟨hrF.2.1, hrF.2.2.1⟩
      have h2rp : 2 * r + 1 < p := hrF.2.2.2.1
      have hlt := low_digit_ratio_lt_half R r p hR hrIco h2rp
      have hrewrite : (r : ℝ) * primeWeight p = (r : ℝ) / ((p - 1 : ℕ) : ℝ) := by
        dsimp [primeWeight]
        rw [mul_one_div]
      rw [hrewrite]
      exact le_of_lt hlt
    have hsum_le := Finset.sum_le_card_nsmul (middleActiveDigits R p)
      (fun r => (r : ℝ) * primeWeight p) (1 / 2) (by intro r hr; exact hterm_le r hr)
    have hsum_le' : (∑ r ∈ middleActiveDigits R p, (r : ℝ) * primeWeight p)
        ≤ ((middleActiveDigits R p).card : ℝ) * (1 / 2) := by
      simpa [nsmul_eq_mul] using hsum_le
    have hcardR : (((middleActiveDigits R p).card : ℕ) : ℝ) * (1 / 2) ≤ 1 := by
      have hc : (((middleActiveDigits R p).card : ℕ) : ℝ) ≤ (2 : ℝ) := by exact_mod_cast hcard
      nlinarith
    exact hsum_le'.trans hcardR
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := P)
    (p := fun p => (middleActiveDigits R p).card ≤ 2) (f := inner)
  have hbound : (∑ p ∈ P, inner p)
      ≤ (∑ p ∈ P.filter (fun p => (middleActiveDigits R p).card ≤ 2), (1 : ℝ))
        + (∑ p ∈ P.filter (fun p => ¬ (middleActiveDigits R p).card ≤ 2), inner p) := by
    rw [← hsplit]
    exact add_le_add hle_two le_rfl
  have hfirst_le : (∑ p ∈ P.filter (fun p => (middleActiveDigits R p).card ≤ 2), (1 : ℝ))
      ≤ (Nat.primeCounting (4 * R) : ℝ) := by
    have hsub : P.filter (fun p => (middleActiveDigits R p).card ≤ 2) ⊆ Nat.primesLE (4 * R) := by
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hpF := Finset.mem_filter.mp hpP
      rw [Nat.mem_primesLE]
      exact ⟨hpF.2.2, hpF.2.1⟩
    have hcardle : (P.filter (fun p => (middleActiveDigits R p).card ≤ 2)).card
        ≤ (Nat.primesLE (4 * R)).card := Finset.card_le_card hsub
    have hcardeq : (Nat.primesLE (4 * R)).card = Nat.primeCounting (4 * R) :=
      Nat.primesLE_card_eq_primeCounting (4 * R)
    have hcardR : ((P.filter (fun p => (middleActiveDigits R p).card ≤ 2)).card : ℝ)
        ≤ (Nat.primeCounting (4 * R) : ℝ) := by
      exact_mod_cast (le_trans hcardle (le_of_eq hcardeq))
    rw [Finset.sum_const, nsmul_eq_mul]
    simpa using hcardR
  have hsecond_le : (∑ p ∈ P.filter (fun p => ¬ (middleActiveDigits R p).card ≤ 2), inner p)
      ≤ WmidWeightedRowSumLowCardGe3 R x := by
    have hsub : P.filter (fun p => ¬ (middleActiveDigits R p).card ≤ 2)
        ⊆ (Finset.Icc 2 x).filter
          (fun p => 2 * R < p ∧ p ≤ 4 * R ∧ Nat.Prime p ∧ 3 ≤ (middleActiveDigits R p).card) := by
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      have hnot := (Finset.mem_filter.mp hp).2
      have hcard : 3 ≤ (middleActiveDigits R p).card := by omega
      have hpF := Finset.mem_filter.mp hpP
      have hnon : (middleActiveDigits R p).Nonempty := by
        exact Finset.card_pos.mp (by omega : 0 < (middleActiveDigits R p).card)
      rcases hnon with ⟨r, hr⟩
      have hrF := Finset.mem_filter.mp hr
      have h2R : 2 * R < p := by omega
      exact Finset.mem_filter.mpr ⟨hpF.1, by refine ⟨h2R, hpF.2.2, hpF.2.1, hcard⟩⟩
    unfold WmidWeightedRowSumLowCardGe3
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro p hp hpnot
    exact Finset.sum_nonneg (by
      intro r hr
      exact mul_nonneg (Nat.cast_nonneg r)
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)))
  calc
    WmidWeightedRowSumLow R x ≤ ∑ p ∈ P, inner p := hreindex
    _ ≤ (∑ p ∈ P.filter (fun p => (middleActiveDigits R p).card ≤ 2), (1 : ℝ))
        + (∑ p ∈ P.filter (fun p => ¬ (middleActiveDigits R p).card ≤ 2), inner p) := hbound
    _ ≤ (Nat.primeCounting (4 * R) : ℝ) + WmidWeightedRowSumLowCardGe3 R x :=
          add_le_add hfirst_le hsecond_le

/-- The LOW prime count `π(4R)` is at most `lowPrimeCountConstant · R / log(2R)`. -/
lemma primeCounting_fourR_le_lowPrimeCountConstant_mul_R_div_log_twoR (R : ℕ) (hR : 1 ≤ R) :
    (Nat.primeCounting (4 * R) : ℝ) ≤
      lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ)) := by
  have h4R2 : 2 ≤ 4 * R := by omega
  have hpi := primeCounting_le_const_div_log (4 * R) h4R2
  have hRposR : 0 < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRge1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h2R_gt1 : 1 < 2 * (R : ℝ) := by nlinarith
  have hlog2Rpos : 0 < Real.log (2 * (R : ℝ)) := Real.log_pos h2R_gt1
  have h4R_gt1 : 1 < ((4 * R : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < 4 * R)
  have hlog4Rpos : 0 < Real.log ((4 * R : ℕ) : ℝ) := Real.log_pos h4R_gt1
  have h4Rcast : ((4 * R : ℕ) : ℝ) = 4 * (R : ℝ) := by
    norm_num [Nat.cast_mul]
  have hmono : Real.log (2 * (R : ℝ)) ≤ Real.log ((4 * R : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact mul_pos (by norm_num) hRposR
    · rw [h4Rcast]
      exact mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (le_of_lt hRposR)
  have hpc_nonneg : 0 ≤ primeCountingConst := by
    dsimp [primeCountingConst]
    positivity
  have hnum_nonneg : 0 ≤ primeCountingConst * ((4 * R : ℕ) : ℝ) :=
    mul_nonneg hpc_nonneg (Nat.cast_nonneg _)
  have hle : primeCountingConst * ((4 * R : ℕ) : ℝ) / Real.log ((4 * R : ℕ) : ℝ)
      ≤ primeCountingConst * ((4 * R : ℕ) : ℝ) / Real.log (2 * (R : ℝ)) := by
    exact div_le_div_of_nonneg_left (a := primeCountingConst * ((4 * R : ℕ) : ℝ))
      (b := Real.log ((4 * R : ℕ) : ℝ)) (c := Real.log (2 * (R : ℝ)))
      hnum_nonneg hlog2Rpos hmono
  have hnum_eq : primeCountingConst * ((4 * R : ℕ) : ℝ) = lowPrimeCountConstant * (R : ℝ) := by
    dsimp [lowPrimeCountConstant]
    rw [h4Rcast]
    ring
  calc
    (Nat.primeCounting (4 * R) : ℝ)
        ≤ primeCountingConst * ((4 * R : ℕ) : ℝ) / Real.log ((4 * R : ℕ) : ℝ) := hpi
    _ ≤ primeCountingConst * ((4 * R : ℕ) : ℝ) / Real.log (2 * (R : ℝ)) := hle
    _ = lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ)) := by rw [hnum_eq]

/-- `WmidLow` is at most the LOW weighted row sum divided by `R`. -/
lemma WmidLow_le_WmidWeightedRowSumLow_div_R (R x : ℕ) (hR : 0 < R) :
    WmidLow R x ≤ WmidWeightedRowSumLow R x / (R : ℝ) := by
  classical
  have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hR
  have hRreal_ne : (R : ℝ) ≠ 0 := ne_of_gt hRreal_pos
  have h_le (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      middleRowMassLow R r x ≤ ((r : ℝ) / (R : ℝ)) * middleRowMassLow R r x := by
    have hrI := Finset.mem_Ico.mp hr
    have hRle : (R : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrI.1
    have hone : (1 : ℝ) ≤ (r : ℝ) / (R : ℝ) := by
      rw [le_div_iff₀ hRreal_pos]
      simpa [one_mul] using hRle
    have hm : 0 ≤ middleRowMassLow R r x := middleRowMassLow_nonneg R r x
    calc
      middleRowMassLow R r x = (1 : ℝ) * middleRowMassLow R r x := by rw [one_mul]
      _ ≤ ((r : ℝ) / (R : ℝ)) * middleRowMassLow R r x :=
        mul_le_mul_of_nonneg_right hone hm
  have hsum : WmidLow R x ≤ ∑ r ∈ Finset.Ico R (2 * R),
      ((r : ℝ) / (R : ℝ)) * middleRowMassLow R r x := by
    rw [show WmidLow R x = ∑ r ∈ Finset.Ico R (2 * R), middleRowMassLow R r x by rfl]
    refine Finset.sum_le_sum ?_
    intro r hr
    exact h_le r hr
  have hsum_div : (∑ r ∈ Finset.Ico R (2 * R),
      ((r : ℝ) / (R : ℝ)) * middleRowMassLow R r x)
      = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassLow R r x) / (R : ℝ) := by
    calc
      (∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) / (R : ℝ)) * middleRowMassLow R r x)
          = ∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) * middleRowMassLow R r x) / (R : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            ring
      _ = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassLow R r x) / (R : ℝ) := by
            rw [Finset.sum_div]
  calc
    WmidLow R x ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ((r : ℝ) / (R : ℝ)) * middleRowMassLow R r x := hsum
    _ = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassLow R r x) / (R : ℝ) := hsum_div
    _ = WmidWeightedRowSumLow R x / (R : ℝ) := by rfl

/-! ## HIGH regime -/

/-- For `p > R²` and `R ≥ 2`, the prime weight is at most `2/R²`. -/
private lemma primeWeight_le_two_div_sq (R p : ℕ) (hR : 2 ≤ R) (hp : R ^ 2 < p) :
    primeWeight p ≤ 2 / (R : ℝ) ^ 2 := by
  have hRpos : 0 < R := by omega
  have hR2pos_nat : 0 < R ^ 2 := pow_pos hRpos 2
  have hp1pos_nat : 0 < p - 1 := by omega
  have hden_p : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hp1pos_nat
  have hden_R2 : 0 < ((R ^ 2 : ℕ) : ℝ) := by exact_mod_cast hR2pos_nat
  have hle_nat : R ^ 2 ≤ p - 1 := by omega
  have hle : ((R ^ 2 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hle_nat
  have h1 : (1 : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ (1 : ℝ) / ((R ^ 2 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hden_R2 hle
  have h2 : (1 : ℝ) / ((R ^ 2 : ℕ) : ℝ) ≤ 2 / (R : ℝ) ^ 2 := by
    rw [Nat.cast_pow]
    exact div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (sq_nonneg (R : ℝ))
  dsimp [primeWeight]
  exact h1.trans h2

/-- The HIGH row mass is at most the saturated HIGH cardinality times `2/R²`. -/
lemma middleRowMassHigh_le_cardHigh_mul_two_div_sq (R r x : ℕ)
    (hr : r ∈ Finset.Ico R (2 * R)) (hR : 2 ≤ R) :
    middleRowMassHigh R r x ≤ ((middlePrimesHigh R r).card : ℝ) * (2 / (R : ℝ) ^ 2) := by
  classical
  let s : Finset ℕ := (middlePrimes r x).filter (fun p => R ^ 2 < p)
  have hsub : s ⊆ middlePrimesHigh R r := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpMid : p ∈ middlePrimes r x := hpF.1
    have hpGt : R ^ 2 < p := hpF.2
    have hpMidF := mem_middlePrimes_iff.mp hpMid
    have hpIcc := Finset.mem_Icc.mp hpMidF.1
    have hrI := Finset.mem_Ico.mp hr
    have hpy : p ≤ 4 * R ^ 2 := by
      have hple : p ≤ r ^ 2 := hpMidF.2.2.1
      have hsq : r ^ 2 < 4 * R ^ 2 := by nlinarith
      omega
    have hpIn : p ∈ middlePrimes r (4 * R ^ 2) := by
      rw [mem_middlePrimes_iff]
      exact ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpy⟩, hpMidF.2.1, hpMidF.2.2.1,
        hpMidF.2.2.2.1, hpMidF.2.2.2.2⟩
    exact Finset.mem_filter.mpr ⟨hpIn, hpGt⟩
  have hterm_le (p : ℕ) (hp : p ∈ s) : primeWeight p ≤ 2 / (R : ℝ) ^ 2 :=
    primeWeight_le_two_div_sq R p hR (Finset.mem_filter.mp hp).2
  calc
    middleRowMassHigh R r x = ∑ p ∈ s, primeWeight p := by rfl
    _ ≤ ∑ p ∈ s, (2 / (R : ℝ) ^ 2) := by
          refine Finset.sum_le_sum ?_
          intro p hp
          exact hterm_le p hp
    _ ≤ ∑ p ∈ middlePrimesHigh R r, (2 / (R : ℝ) ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
          intro p hp hpnot
          exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (R : ℝ))
    _ = ((middlePrimesHigh R r).card : ℝ) * (2 / (R : ℝ) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- The saturated HIGH prime set has at most `middleRowConstant · r / (2 log R)` elements. -/
lemma middlePrimesHigh_card_le (R r : ℕ) (hR : 2 ≤ R) (hr : 1 ≤ r) :
    ((middlePrimesHigh R r).card : ℝ) ≤
      middleRowConstant * (r : ℝ) / (2 * Real.log (R : ℝ)) := by
  classical
  let s : Finset ℕ := middlePrimesHigh R r
  have hsub : s ⊆ middlePrimes r (4 * R ^ 2) := by
    dsimp [s, middlePrimesHigh]
    exact Finset.filter_subset _ _
  have hprod_dvd : (∏ p ∈ s, p) ∣ numNat r := by
    have hdvd := prod_middlePrimes_dvd_numNat r (4 * R ^ 2) hr
    exact dvd_trans (Finset.prod_dvd_prod_of_subset s (middlePrimes r (4 * R ^ 2)) (fun p => p) hsub) hdvd
  have hprod_le : (∏ p ∈ s, p) ≤ numNat r := Nat.le_of_dvd (numNat_pos r hr) hprod_dvd
  have hpow_le_prod : (R ^ 2) ^ s.card ≤ ∏ p ∈ s, p := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' ?_
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    exact le_of_lt hpF.2
  have hchain : (R ^ 2) ^ s.card ≤ numNat r := hpow_le_prod.trans hprod_le
  have hchainL : (R ^ 2) ^ s.card ≤ r * L r := hchain.trans (numNat_le_mul_L r)
  have hRpos : 0 < R := by omega
  have hR2pos_nat : 0 < R ^ 2 := pow_pos hRpos 2
  have hR2_gt1 : 1 < R ^ 2 := by nlinarith
  have hlogRpos : 0 < Real.log (R : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < R) : (1 : ℝ) < (R : ℝ))
  have hlog_le : Real.log (((R ^ 2) ^ s.card : ℕ) : ℝ) ≤ Real.log ((r * L r : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (pow_pos hR2pos_nat s.card)
    · exact_mod_cast hchainL
  have hlog_pow_eq : Real.log (((R ^ 2) ^ s.card : ℕ) : ℝ) =
      (s.card : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact Real.log_pow ((R ^ 2 : ℕ) : ℝ) s.card
  have hlogR2_eq : Real.log ((R ^ 2 : ℕ) : ℝ) = 2 * Real.log (R : ℝ) := by
    rw [Nat.cast_pow]
    rw [Real.log_pow]
    norm_num
  have hcard_log : (s.card : ℝ) * (2 * Real.log (R : ℝ)) ≤ Real.log ((r * L r : ℕ) : ℝ) := by
    rw [hlog_pow_eq] at hlog_le
    rwa [hlogR2_eq] at hlog_le
  have hlog_bound := log_mul_L_le_middleRowConstant r hr
  have hcard_log_le : (s.card : ℝ) * (2 * Real.log (R : ℝ)) ≤ middleRowConstant * (r : ℝ) :=
    le_trans hcard_log hlog_bound
  have hden : 0 < 2 * Real.log (R : ℝ) := mul_pos (by norm_num) hlogRpos
  have hmain : (s.card : ℝ) ≤ (middleRowConstant * (r : ℝ)) / (2 * Real.log (R : ℝ)) := by
    rw [le_div_iff₀ hden]
    exact hcard_log_le
  simpa [s] using hmain

/-- The HIGH weighted row sum is at most `highRegimeConstant · R / log R`. -/
lemma WmidWeightedRowSumHigh_le_highRegimeConstant_mul_R_div_log (R x : ℕ) (hR : 2 ≤ R) :
    WmidWeightedRowSumHigh R x ≤ highRegimeConstant * (R : ℝ) / Real.log (R : ℝ) := by
  classical
  have hRpos : 0 < R := by omega
  have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hRpos
  have hRgt1 : 1 < (R : ℝ) := by exact_mod_cast (by omega : 1 < R)
  have hlogRpos : 0 < Real.log (R : ℝ) := Real.log_pos hRgt1
  have hR2pos : 0 < (R : ℝ) ^ 2 := sq_pos_of_pos hRreal_pos
  have hR2ne : (R : ℝ) ^ 2 ≠ 0 := ne_of_gt hR2pos
  have hlogRne : Real.log (R : ℝ) ≠ 0 := ne_of_gt hlogRpos
  have h2logRne : 2 * Real.log (R : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hlogRne
  have hden_pos : 0 < (R : ℝ) ^ 2 * Real.log (R : ℝ) := mul_pos hR2pos hlogRpos
  have htwo_div_nonneg : 0 ≤ 2 / (R : ℝ) ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  unfold WmidWeightedRowSumHigh
  calc
    (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassHigh R r x)
        ≤ ∑ r ∈ Finset.Ico R (2 * R), (4 * middleRowConstant) / Real.log (R : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro r hr
          have hrI := Finset.mem_Ico.mp hr
          have hr1 : 1 ≤ r := by omega
          have hcard := middlePrimesHigh_card_le R r hR hr1
          have hmass := middleRowMassHigh_le_cardHigh_mul_two_div_sq R r x hr hR
          have hnum_le : middleRowConstant * (r : ℝ) ^ 2 ≤ middleRowConstant * (4 * (R : ℝ) ^ 2) := by
            have hRr : (R : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrI.1
            have hr2R : (r : ℝ) < 2 * (R : ℝ) := by exact_mod_cast hrI.2
            have hsq : (r : ℝ) ^ 2 ≤ 4 * (R : ℝ) ^ 2 := by nlinarith
            exact mul_le_mul_of_nonneg_left hsq middleRowConstant_nonneg
          calc
            (r : ℝ) * middleRowMassHigh R r x
                ≤ (r : ℝ) * (((middlePrimesHigh R r).card : ℝ) * (2 / (R : ℝ) ^ 2)) := by
                  exact mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg r)
            _ ≤ (r : ℝ) * ((middleRowConstant * (r : ℝ) / (2 * Real.log (R : ℝ))) * (2 / (R : ℝ) ^ 2)) := by
                  exact mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hcard htwo_div_nonneg) (Nat.cast_nonneg r)
            _ = middleRowConstant * (r : ℝ) ^ 2 / ((R : ℝ) ^ 2 * Real.log (R : ℝ)) := by
                  field_simp [hR2ne, hlogRne, h2logRne]
            _ ≤ middleRowConstant * (4 * (R : ℝ) ^ 2) / ((R : ℝ) ^ 2 * Real.log (R : ℝ)) := by
                  exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
            _ = (4 * middleRowConstant) / Real.log (R : ℝ) := by
                  field_simp [hR2ne, hlogRne]
    _ = (Finset.Ico R (2 * R)).card • ((4 * middleRowConstant) / Real.log (R : ℝ)) := by
          rw [Finset.sum_const]
    _ = (R : ℝ) * ((4 * middleRowConstant) / Real.log (R : ℝ)) := by
          rw [nsmul_eq_mul]
          have hcard : (Finset.Ico R (2 * R)).card = R := by
            simp
            omega
          rw [hcard]
    _ = highRegimeConstant * (R : ℝ) / Real.log (R : ℝ) := by
          dsimp [highRegimeConstant]
          field_simp [hlogRne]

/-- `WmidHigh` is at most the HIGH weighted row sum divided by `R`. -/
lemma WmidHigh_le_WmidWeightedRowSumHigh_div_R (R x : ℕ) (hR : 0 < R) :
    WmidHigh R x ≤ WmidWeightedRowSumHigh R x / (R : ℝ) := by
  classical
  have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hR
  have hRreal_ne : (R : ℝ) ≠ 0 := ne_of_gt hRreal_pos
  have h_le (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      middleRowMassHigh R r x ≤ ((r : ℝ) / (R : ℝ)) * middleRowMassHigh R r x := by
    have hrI := Finset.mem_Ico.mp hr
    have hRle : (R : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrI.1
    have hone : (1 : ℝ) ≤ (r : ℝ) / (R : ℝ) := by
      rw [le_div_iff₀ hRreal_pos]
      simpa [one_mul] using hRle
    have hm : 0 ≤ middleRowMassHigh R r x := middleRowMassHigh_nonneg R r x
    calc
      middleRowMassHigh R r x = (1 : ℝ) * middleRowMassHigh R r x := by rw [one_mul]
      _ ≤ ((r : ℝ) / (R : ℝ)) * middleRowMassHigh R r x :=
        mul_le_mul_of_nonneg_right hone hm
  have hsum : WmidHigh R x ≤ ∑ r ∈ Finset.Ico R (2 * R),
      ((r : ℝ) / (R : ℝ)) * middleRowMassHigh R r x := by
    rw [show WmidHigh R x = ∑ r ∈ Finset.Ico R (2 * R), middleRowMassHigh R r x by rfl]
    refine Finset.sum_le_sum ?_
    intro r hr
    exact h_le r hr
  have hsum_div : (∑ r ∈ Finset.Ico R (2 * R),
      ((r : ℝ) / (R : ℝ)) * middleRowMassHigh R r x)
      = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassHigh R r x) / (R : ℝ) := by
    calc
      (∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) / (R : ℝ)) * middleRowMassHigh R r x)
          = ∑ r ∈ Finset.Ico R (2 * R), ((r : ℝ) * middleRowMassHigh R r x) / (R : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            ring
      _ = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassHigh R r x) / (R : ℝ) := by
            rw [Finset.sum_div]
  calc
    WmidHigh R x ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ((r : ℝ) / (R : ℝ)) * middleRowMassHigh R r x := hsum
    _ = (∑ r ∈ Finset.Ico R (2 * R), (r : ℝ) * middleRowMassHigh R r x) / (R : ℝ) := hsum_div
    _ = WmidWeightedRowSumHigh R x / (R : ℝ) := by rfl

/-! ## Combined unconditional bound -/

/-- The unconditional LOW + HIGH bound leaves only the MID weighted row sum and the
LOW card-≥3 term, both divided by `R`. -/
lemma Wmid_le_low_high_plus_hard_div (R x : ℕ) (hR : 18 ≤ R) :
    Wmid R x ≤ lowPrimeCountConstant / Real.log (2 * (R : ℝ))
      + highRegimeConstant / Real.log (R : ℝ)
      + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x) / (R : ℝ) := by
  have hRpos : 0 < R := by omega
  have hR4 : 4 ≤ R := by omega
  have hR2 : 2 ≤ R := by omega
  have hR1 : 1 ≤ R := by omega
  have hRreal_pos : 0 < (R : ℝ) := by exact_mod_cast hRpos
  have hRreal_ne : (R : ℝ) ≠ 0 := ne_of_gt hRreal_pos
  have hRge1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlog2Rpos : 0 < Real.log (2 * (R : ℝ)) := by
    apply Real.log_pos
    have : (1 : ℝ) < 2 * (R : ℝ) := by nlinarith
    exact this
  have hlogRpos : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < R)
  have hlog2Rne : Real.log (2 * (R : ℝ)) ≠ 0 := ne_of_gt hlog2Rpos
  have hlogRne : Real.log (R : ℝ) ≠ 0 := ne_of_gt hlogRpos
  have hWmid := Wmid_le_WmidWeightedRowSum_div_R R x hRpos
  have hSyLow := WmidWeightedRowSumLow_le_pi_fourR_add_cardGe3 R x hR4
  have hpi := primeCounting_fourR_le_lowPrimeCountConstant_mul_R_div_log_twoR R hR1
  have hSyHigh := WmidWeightedRowSumHigh_le_highRegimeConstant_mul_R_div_log R x hR2
  have hSyLow' : WmidWeightedRowSumLow R x ≤
      lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ)) + WmidWeightedRowSumLowCardGe3 R x := by
    exact le_trans hSyLow (add_le_add hpi le_rfl)
  have hSyEq := WmidWeightedRowSum_eq_low_add_mid_add_high R x (by omega : 4 ≤ R)
  have hSy : WmidWeightedRowSum R x ≤
      lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ))
        + highRegimeConstant * (R : ℝ) / Real.log (R : ℝ)
        + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x) := by
    rw [hSyEq]
    nlinarith [hSyLow', hSyHigh]
  have hdiv : WmidWeightedRowSum R x / (R : ℝ) ≤
      (lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ))
        + highRegimeConstant * (R : ℝ) / Real.log (R : ℝ)
        + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x)) / (R : ℝ) := by
    exact div_le_div_of_nonneg_right hSy (le_of_lt hRreal_pos)
  have hrewrite : (lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ))
        + highRegimeConstant * (R : ℝ) / Real.log (R : ℝ)
        + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x)) / (R : ℝ)
      = lowPrimeCountConstant / Real.log (2 * (R : ℝ))
        + highRegimeConstant / Real.log (R : ℝ)
        + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x) / (R : ℝ) := by
    field_simp [hRreal_ne, hlog2Rne, hlogRne]
  calc
    Wmid R x ≤ WmidWeightedRowSum R x / (R : ℝ) := hWmid
    _ ≤ (lowPrimeCountConstant * (R : ℝ) / Real.log (2 * (R : ℝ))
        + highRegimeConstant * (R : ℝ) / Real.log (R : ℝ)
        + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x)) / (R : ℝ) := hdiv
    _ = lowPrimeCountConstant / Real.log (2 * (R : ℝ))
        + highRegimeConstant / Real.log (R : ℝ)
        + (WmidWeightedRowSumMid R x + WmidWeightedRowSumLowCardGe3 R x) / (R : ℝ) := hrewrite

/-! ## Diagonal injection from the second moment -/

/-- The middle pair mass: for each row `r ∈ [R, 2R)`, the mass of primes `p`
with `2r + 1 < p`, `p` prime, and `p ∣ num H_r` (no `p ≤ r²` restriction). -/
noncomputable def middlePairMass (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R), ∑ p ∈ (Finset.Icc 2 x).filter
      (fun p => 2 * r + 1 < p ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num), primeWeight p

/-- Twice the middle pair mass. -/
noncomputable def middleDiagMass (R x : ℕ) : ℝ := 2 * middlePairMass R x

/-- `Wmid` is at most the middle pair mass (the latter omits the `p ≤ r²` condition). -/
lemma Wmid_le_middlePairMass (R x : ℕ) : Wmid R x ≤ middlePairMass R x := by
  classical
  unfold Wmid middlePairMass
  refine Finset.sum_le_sum ?_
  intro r hr
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    have hpF := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpF.1, by
      refine ⟨hpF.2.1, hpF.2.2.2.1, hpF.2.2.2.2⟩⟩
  · intro p hp hpnot
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)

/-- `Wmid` is at most half the diagonal mass. -/
lemma Wmid_le_middleDiagMass_div_two (R x : ℕ) : Wmid R x ≤ middleDiagMass R x / 2 := by
  have h := Wmid_le_middlePairMass R x
  have h2 : middleDiagMass R x / 2 = middlePairMass R x := by
    dsimp [middleDiagMass]
    ring
  rwa [h2]

/-! ## Remaining hypotheses (definitions only) -/

/-- LOW+HIGH bound hypothesis: `WmidLow R x + WmidHigh R x ≤ 0.027` for `R ≥ 18`.
Evidence: exact C computation gives max `0.023679098679` at `R = 18` over `R = 18..1999`. -/
def HA_Wmid_low_high_bound : Prop :=
  ∀ R : ℕ, 18 ≤ R → ∀ x : ℕ, WmidLow R x + WmidHigh R x ≤ 0.027

/-- MID bound hypothesis: `WmidMid R x ≤ 0.045` for `R ≥ 18`.
Evidence: exact C computation gives max `0.043368692020` at `R = 242` over `R = 18..1999`. -/
def HA_Wmid_mid_constant_bound : Prop :=
  ∀ R : ℕ, 18 ≤ R → ∀ x : ℕ, WmidMid R x ≤ 0.045

/-! ## Capstone -/

/-- Under the LOW+HIGH and MID regime bounds, `HA_Wmid_constant_bound` holds with
`R₀ = 18` and `C = 0.072`. -/
theorem HA_Wmid_constant_bound_of_regime_bounds
    (hLH : HA_Wmid_low_high_bound) (hMid : HA_Wmid_mid_constant_bound) :
    HA_Wmid_constant_bound := by
  refine ⟨18, 0.072, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : (0.576 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (0.576 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have h8 : (0.072 : ℝ) * 8 = 0.576 := by norm_num
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hlog]
  · intro R hR x
    calc
      Wmid R x = WmidLow R x + WmidMid R x + WmidHigh R x := Wmid_eq_low_add_mid_add_high R x (by omega : 4 ≤ R)
      _ = WmidMid R x + (WmidLow R x + WmidHigh R x) := by ring
      _ ≤ 0.045 + 0.027 := add_le_add (hMid R hR x) (hLH R hR x)
      _ = 0.072 := by norm_num

/-- Under the LOW+HIGH and MID regime bounds, `x · prodOneSub x` tends to `atTop`. -/
theorem xP_tendsto_atTop_of_regime_bounds
    (hLH : HA_Wmid_low_high_bound) (hMid : HA_Wmid_mid_constant_bound) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop :=
  xP_tendsto_atTop_of_Wmid_constant_bound (HA_Wmid_constant_bound_of_regime_bounds hLH hMid)

end

end Erdos291
