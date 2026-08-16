import Erdos291.WmidBound
import Erdos291.BlockMidDyadic
import Erdos291.BlockActiveDyadic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős #291 — dyadic-block attack on `Wmid`

This file develops the unconditional dyadic-block bounds for `Wmid`.  For each
prime block `[P, 2P)` let

  `middleDigitCount R P = Σ_{p ∈ [P,2P) prime} |middleActiveDigits R p|`.

The block contribution `WmidBlock R P x` is bounded by
`2 · middleDigitCount R P / P` (for `P ≥ 2`), and only the dyadic blocks
intersecting the middle range `2R + 1 < p ≤ 4R²` can contribute.

We then record the block-mass replacement hypothesis
`HA_WmidBlock_mass_log_bound`: for every relevant dyadic block `P = 2^k`,

  `WmidBlock R P x ≤ 1.01 / (log R · log P)`.

The constant `1.01` is supported numerically: the maximum of
`WmidBlock · log P · log R` over the scanned range is `1.0063423353`,
attained at `(R, P) = (262, 1024)`, so `1.01` has a `0.36%` margin.

Together with the crude bound `Σ 1/(k log 2) ≤ 2.05` over the `O(log R)`
dyadic blocks, this hypothesis closes `HA_Wmid_constant_bound` with
`R₀ = 2^36` and `C = 0.085`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000

noncomputable section

/-- Local spelling of the (private) middle prime condition from `BlockMidDyadic`;
definitionally equal to it, so we can `change` unfolded `WmidBlock` goals. -/
private abbrev midPrimeCondSy (r p : ℕ) : Prop :=
  2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num

/-- The number of middle-active digits over the prime block `[P, 2P)`:
`Σ_{p ∈ [P,2P) prime} |middleActiveDigits R p|`. -/
noncomputable def middleDigitCount (R P : ℕ) : ℕ :=
  ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime, (middleActiveDigits R p).card

/-! ## Block count bounds -/

/-- The block contribution is bounded by the count of middle-active digits in the
same block, weighted by `primeWeight`. -/
lemma WmidBlock_le_sum_middleActiveDigits_card_weight_block (R P x : ℕ) :
    WmidBlock R P x ≤
      ∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ Nat.Prime p),
        ((middleActiveDigits R p).card : ℝ) * primeWeight p := by
  classical
  change (∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ midPrimeCondSy r p),
          (1 / ((p - 1 : ℕ) : ℝ))) ≤
      ∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ Nat.Prime p),
        ((middleActiveDigits R p).card : ℝ) * primeWeight p
  let Pblock : Finset ℕ := (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ Nat.Prime p)
  have mem_mid (r p : ℕ) (hrIco : r ∈ Finset.Ico R (2 * R))
      (hp : p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ midPrimeCondSy r p)) :
      r ∈ middleActiveDigits R p := by
    have hpF := Finset.mem_filter.mp hp
    have hpIco : p ∈ Finset.Ico P (2 * P) := hpF.1
    rcases hpF.2 with ⟨hpx, h2rp, hle, hpPrime, hdvd⟩
    have hrI := Finset.mem_Ico.mp hrIco
    have h1r : 1 ≤ r := by omega
    have hrp : r < p := by omega
    have hrE : r ∈ E p := (mem_E_iff_dvd_num p r hpPrime h1r hrp).mpr hdvd
    exact Finset.mem_filter.mpr ⟨hrE, hrI.1, hrI.2, h2rp, hle⟩
  have hinner_le (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      (∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ midPrimeCondSy r p),
        (1 / ((p - 1 : ℕ) : ℝ))) ≤
      ∑ p ∈ Pblock.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpPblock : p ∈ Pblock := by
        exact Finset.mem_filter.mpr ⟨hpF.1, hpF.2.1, hpF.2.2.2.2.1⟩
      exact Finset.mem_filter.mpr ⟨hpPblock, mem_mid r p hr hp⟩
    · intro p hp hpnot
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  calc
    (∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ midPrimeCondSy r p),
          (1 / ((p - 1 : ℕ) : ℝ))) ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ Pblock.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact hinner_le r hr
    _ = ∑ p ∈ Pblock,
        ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
          primeWeight p := by
          calc
            ∑ r ∈ Finset.Ico R (2 * R),
                ∑ p ∈ Pblock.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p
              = ∑ r ∈ Finset.Ico R (2 * R),
                  ∑ p ∈ Pblock, (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    rw [Finset.sum_filter]
            _ = ∑ p ∈ Pblock,
                  ∑ r ∈ Finset.Ico R (2 * R),
                    (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
                    rw [Finset.sum_comm]
            _ = ∑ p ∈ Pblock,
                  ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
                    primeWeight p := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    rw [Finset.sum_filter]
    _ = ∑ p ∈ Pblock,
        (((middleActiveDigits R p).card : ℕ) : ℝ) * primeWeight p := by
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
              refine Finset.mem_filter.mpr ⟨?_, hr⟩
              exact Finset.mem_Ico.mpr ⟨hrF.2.1, hrF.2.2.1⟩
          rw [hfilter, Finset.sum_const, nsmul_eq_mul]

/-- With the looser denominator `P`, each block contribution is at most
`2 * middleDigitCount R P / P`. -/
lemma WmidBlock_le_two_mul_middleDigitCount_div (R P x : ℕ) (hP : 2 ≤ P) :
    WmidBlock R P x ≤ 2 * (middleDigitCount R P : ℝ) / (P : ℝ) := by
  classical
  have htrunc_le_full :
      (∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ Nat.Prime p),
        ((middleActiveDigits R p).card : ℝ) * primeWeight p)
        ≤ ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
          ((middleActiveDigits R p).card : ℝ) * primeWeight p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.2⟩
    · intro p hp hpnot
      exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))
  have hwle : ∀ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
      primeWeight p ≤ 2 / (P : ℝ) := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpF.1
    have hPp : P ≤ p := hpIco.1
    have hsub : P - 1 ≤ p - 1 := Nat.sub_le_sub_right hPp 1
    have hposP : 0 < ((P - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < P - 1)
    have hcast : ((P - 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hsub
    have hle_inv : primeWeight p ≤ 1 / ((P - 1 : ℕ) : ℝ) := by
      dsimp [primeWeight]
      exact one_div_le_one_div_of_le hposP hcast
    exact le_trans hle_inv (one_div_sub_one_le_two_div P hP)
  have hfull_le : (∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
        ((middleActiveDigits R p).card : ℝ) * primeWeight p)
      ≤ ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
        ((middleActiveDigits R p).card : ℝ) * (2 / (P : ℝ)) := by
    exact Finset.sum_le_sum (by
      intro p hp
      exact mul_le_mul_of_nonneg_left (hwle p hp) (Nat.cast_nonneg _))
  have hsum_eq : (∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
        ((middleActiveDigits R p).card : ℝ) * (2 / (P : ℝ)))
      = 2 * (middleDigitCount R P : ℝ) / (P : ℝ) := by
    calc
      (∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
          ((middleActiveDigits R p).card : ℝ) * (2 / (P : ℝ)))
          = ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
              (2 / (P : ℝ)) * ((middleActiveDigits R p).card : ℝ) := by
                apply Finset.sum_congr rfl
                intro p hp
                ring
      _ = (2 / (P : ℝ)) * (∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
              ((middleActiveDigits R p).card : ℝ)) := by
                rw [Finset.mul_sum]
      _ = (2 / (P : ℝ)) * (middleDigitCount R P : ℝ) := by
                simp [middleDigitCount]
      _ = 2 * (middleDigitCount R P : ℝ) / (P : ℝ) := by ring
  calc
    WmidBlock R P x ≤ ∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ Nat.Prime p),
        ((middleActiveDigits R p).card : ℝ) * primeWeight p :=
      WmidBlock_le_sum_middleActiveDigits_card_weight_block R P x
    _ ≤ ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
        ((middleActiveDigits R p).card : ℝ) * primeWeight p := htrunc_le_full
    _ ≤ ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime,
        ((middleActiveDigits R p).card : ℝ) * (2 / (P : ℝ)) := hfull_le
    _ = 2 * (middleDigitCount R P : ℝ) / (P : ℝ) := hsum_eq

/-- Only blocks that meet the middle range can contain a middle-active digit. -/
lemma middleDigitCount_eq_zero_of_not_mid_range (R P : ℕ)
    (hP : 2 * P ≤ 2 * R + 1 ∨ 4 * R ^ 2 ≤ P) : middleDigitCount R P = 0 := by
  classical
  unfold middleDigitCount
  apply Finset.sum_eq_zero
  intro p hp
  have hpF := Finset.mem_filter.mp hp
  have hpIco := Finset.mem_Ico.mp hpF.1
  have hPp : P ≤ p := hpIco.1
  have hph : p < 2 * P := hpIco.2
  apply Finset.card_eq_zero.mpr
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨r, hr⟩
  have hrF := Finset.mem_filter.mp hr
  have hrI := Finset.mem_Ico.mpr ⟨hrF.2.1, hrF.2.2.1⟩
  have h2rp : 2 * r + 1 < p := hrF.2.2.2.1
  have hler : p ≤ r ^ 2 := hrF.2.2.2.2
  rcases hP with hleft | hright
  · have hp_le : p ≤ 2 * R := by omega
    have h2r : 2 * R ≤ 2 * r := Nat.mul_le_mul_left 2 (Finset.mem_Ico.mp hrI).1
    omega
  · have hsq : r ^ 2 < 4 * R ^ 2 := by nlinarith [Finset.mem_Ico.mp hrI]
    have hp_ge : 4 * R ^ 2 ≤ p := by omega
    omega

/-! ## The dyadic log-reciprocal sum -/

/-- The sum of `1/(k log 2)` over the dyadic indices `k` that can contribute. -/
noncomputable def dyadicLogReciprocalSum (R : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (Nat.log 2 R + 1) (Nat.log 2 (4 * R ^ 2)),
    (1 : ℝ) / ((k : ℝ) * Real.log 2)

/-- Crude but sufficient bound: for `R ≥ 16`, the dyadic log-reciprocal sum is
at most `2.05`. -/
lemma dyadicLogReciprocalSum_le_two (R : ℕ) (hR : 16 ≤ R) :
    dyadicLogReciprocalSum R ≤ 2.05 := by
  classical
  let L := Nat.log 2 R
  let U := Nat.log 2 (4 * R ^ 2)
  have hL4 : 4 ≤ L := by
    dsimp [L]
    have hmono : Nat.log 2 16 ≤ Nat.log 2 R := Nat.log_mono_right hR
    norm_num [Nat.log] at hmono ⊢
    exact hmono
  have hRpos : 0 < R := by omega
  have hRne : R ≠ 0 := Nat.ne_of_gt hRpos
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hL1pos : 0 < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < L + 1)
  have hden_pos : 0 < ((L + 1 : ℕ) : ℝ) * Real.log 2 := mul_pos hL1pos hlog2pos
  have hterm : ∀ k ∈ Finset.Icc (L + 1) U,
      (1 : ℝ) / ((k : ℝ) * Real.log 2) ≤ (1 : ℝ) / (((L + 1 : ℕ) : ℝ) * Real.log 2) := by
    intro k hk
    have hklo : L + 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkpos : 0 < k := by omega
    have hkcastpos : 0 < (k : ℝ) := by exact_mod_cast hkpos
    have hkden_pos : 0 < (k : ℝ) * Real.log 2 := mul_pos hkcastpos hlog2pos
    have hle : ((L + 1 : ℕ) : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hklo) (le_of_lt hlog2pos)
    exact one_div_le_one_div_of_le hden_pos hle
  have hsum_le : (∑ k ∈ Finset.Icc (L + 1) U, (1 : ℝ) / ((k : ℝ) * Real.log 2))
      ≤ (Finset.Icc (L + 1) U).card * (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2)) := by
    have h := Finset.sum_le_card_nsmul (Finset.Icc (L + 1) U)
      (fun k => (1 : ℝ) / ((k : ℝ) * Real.log 2))
      (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2)) hterm
    simpa [nsmul_eq_mul] using h
  have hcardNat : (Finset.Icc (L + 1) U).card ≤ L + 3 := by
    rw [Nat.card_Icc]
    have hUle : U ≤ 2 * L + 3 := by
      dsimp [U]
      have hRlt : R < 2 ^ (L + 1) := by
        dsimp [L]
        simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) R
      have hRsucc_le : R + 1 ≤ 2 ^ (L + 1) := Nat.succ_le_of_lt hRlt
      have hsq_le : (R + 1) ^ 2 ≤ (2 ^ (L + 1)) ^ 2 := Nat.pow_le_pow_left hRsucc_le 2
      have h4lt : 4 * R ^ 2 < 4 * (R + 1) ^ 2 := by nlinarith
      have h4le : 4 * (R + 1) ^ 2 ≤ 4 * (2 ^ (L + 1)) ^ 2 := Nat.mul_le_mul_left 4 hsq_le
      have hpow : (2 ^ (L + 1)) ^ 2 = 2 ^ (2 * (L + 1)) := by
        rw [← Nat.pow_mul]
        congr 1
        omega
      have hkey : 4 * 2 ^ (2 * (L + 1)) = 2 ^ (2 * L + 4) := by
        rw [show 2 * (L + 1) = 2 * L + 2 by omega]
        calc
          4 * 2 ^ (2 * L + 2) = 2 ^ 2 * 2 ^ (2 * L + 2) := by norm_num
          _ = 2 ^ (2 + (2 * L + 2)) := by rw [← pow_add]
          _ = 2 ^ (2 * L + 4) := by rw [show 2 + (2 * L + 2) = 2 * L + 4 by omega]
      have hlt : 4 * R ^ 2 < 2 ^ (2 * L + 4) := by
        have h4le2 : 4 * (R + 1) ^ 2 ≤ 4 * 2 ^ (2 * (L + 1)) := by
          simpa [hpow] using h4le
        have h4lt' : 4 * R ^ 2 < 4 * 2 ^ (2 * (L + 1)) := lt_of_lt_of_le h4lt h4le2
        rwa [hkey] at h4lt'
      have hloglt : Nat.log 2 (4 * R ^ 2) < 2 * L + 4 := by
        apply Nat.log_lt_of_lt_pow
        · have hR2pos : 0 < R ^ 2 := pow_pos hRpos 2
          have h4R2pos : 0 < 4 * R ^ 2 := Nat.mul_pos (by norm_num : 0 < 4) hR2pos
          exact Nat.ne_of_gt h4R2pos
        · simpa [show 2 * L + 4 = (2 * L + 3) + 1 by omega] using hlt
      omega
    omega
  have hcardle : (Finset.Icc (L + 1) U).card * (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2))
      ≤ ((L + 3 : ℕ) : ℝ) * (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2)) := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcardNat)
      (one_div_nonneg.mpr (le_of_lt hden_pos))
  have halg : ((L + 3 : ℕ) : ℝ) * (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2))
      = (((L + 3 : ℕ) : ℝ) / ((L + 1 : ℕ) : ℝ)) / Real.log 2 := by
    field_simp [ne_of_gt hL1pos, ne_of_gt hlog2pos]
  have hratio : (((L + 3 : ℕ) : ℝ) / ((L + 1 : ℕ) : ℝ)) ≤ 1.4 := by
    rw [div_le_iff₀ hL1pos]
    have hL4r : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL4
    rw [show ((L + 3 : ℕ) : ℝ) = (L : ℝ) + 3 by norm_num]
    rw [show ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 by norm_num]
    nlinarith
  have hdivle : (((L + 3 : ℕ) : ℝ) / ((L + 1 : ℕ) : ℝ)) / Real.log 2 ≤
      (1.4 : ℝ) / Real.log 2 := by
    exact div_le_div_of_nonneg_right hratio (le_of_lt hlog2pos)
  have hfinal : (1.4 : ℝ) / Real.log 2 ≤ 2.05 := by
    rw [div_le_iff₀ hlog2pos]
    have hconst : (1.4 : ℝ) < 2.05 * 0.6931471803 := by norm_num
    nlinarith [Real.log_two_gt_d9, hconst]
  calc
    dyadicLogReciprocalSum R = ∑ k ∈ Finset.Icc (L + 1) U,
        (1 : ℝ) / ((k : ℝ) * Real.log 2) := by
      dsimp [dyadicLogReciprocalSum, L, U]
    _ ≤ (Finset.Icc (L + 1) U).card * (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2)) := hsum_le
    _ ≤ ((L + 3 : ℕ) : ℝ) * (1 / (((L + 1 : ℕ) : ℝ) * Real.log 2)) := hcardle
    _ = (((L + 3 : ℕ) : ℝ) / ((L + 1 : ℕ) : ℝ)) / Real.log 2 := halg
    _ ≤ (1.4 : ℝ) / Real.log 2 := hdivle
    _ ≤ 2.05 := hfinal

/-! ## The block-mass replacement hypothesis -/

/-- Hypothesis: each relevant dyadic block `P = 2^k` satisfies
`WmidBlock R P x ≤ 1.01 / (log R · log P)` for `R ≥ 18`.

Numerical evidence (C scan): the maximum of `WmidBlock · log P · log R` is
`1.0063423353`, attained at `(R, P) = (262, 1024)`; the constant `1.01` has a
`0.36%` margin. -/
def HA_WmidBlock_mass_log_bound : Prop :=
  ∀ R : ℕ, 18 ≤ R → ∀ x : ℕ, ∀ k : ℕ,
    2 * R + 1 < 2 * 2 ^ k → 2 ^ k ≤ 4 * R ^ 2 →
      WmidBlock R (2 ^ k) x ≤
        1.01 / (Real.log (R : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ))

/-- Under the block-mass log bound, `HA_Wmid_constant_bound` holds with
`R₀ = 2^36` and `C = 0.085`. -/
theorem HA_Wmid_constant_bound_of_block_mass_log_bound
    (h : HA_WmidBlock_mass_log_bound) :
    HA_Wmid_constant_bound := by
  refine ⟨2 ^ 36, 0.085, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : (0.68 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (0.68 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have h8 : (0.085 : ℝ) * 8 = 0.68 := by norm_num
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hlog]
  · intro R hR x
    classical
    let L := Nat.log 2 R
    let U := Nat.log 2 (4 * R ^ 2)
    have hRpos : 0 < R := by omega
    have hRne : R ≠ 0 := Nat.ne_of_gt hRpos
    have hR18 : 18 ≤ R := by omega
    have hlogRpos : 0 < Real.log (R : ℝ) := by
      have hRgt1 : (1 : ℝ) < (R : ℝ) := by
        have : (18 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR18
        nlinarith
      exact Real.log_pos hRgt1
    have hlogRne : Real.log (R : ℝ) ≠ 0 := ne_of_gt hlogRpos
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hLU : L ≤ U := by
      dsimp [L, U]
      apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      have h2L : 2 ^ Nat.log 2 R ≤ R := Nat.pow_log_le_self 2 hRne
      have hRle : R ≤ 4 * R ^ 2 := by nlinarith
      exact le_trans h2L hRle
    have hsplit : (∑ k ∈ Finset.range (U + 1), WmidBlock R (2 ^ k) x) =
        (∑ k ∈ Finset.range (L + 1), WmidBlock R (2 ^ k) x) +
        (∑ k ∈ Finset.Icc (L + 1) U, WmidBlock R (2 ^ k) x) := by
      calc
        (∑ k ∈ Finset.range (U + 1), WmidBlock R (2 ^ k) x)
            = ∑ k ∈ Finset.Ico 0 (U + 1), WmidBlock R (2 ^ k) x := by rw [Finset.range_eq_Ico]
        _ = (∑ k ∈ Finset.Ico 0 (L + 1), WmidBlock R (2 ^ k) x) +
            (∑ k ∈ Finset.Ico (L + 1) (U + 1), WmidBlock R (2 ^ k) x) := by
              rw [← Finset.sum_Ico_consecutive (fun k => WmidBlock R (2 ^ k) x)
                (by omega : 0 ≤ L + 1) (by omega : L + 1 ≤ U + 1)]
        _ = (∑ k ∈ Finset.range (L + 1), WmidBlock R (2 ^ k) x) +
            (∑ k ∈ Finset.Icc (L + 1) U, WmidBlock R (2 ^ k) x) := by
              rw [Finset.range_eq_Ico]
              have hIco : Finset.Ico (L + 1) (U + 1) = Finset.Icc (L + 1) U := by
                ext k
                simp only [Finset.mem_Ico, Finset.mem_Icc]
                omega
              rw [hIco]
    have hzero_low : (∑ k ∈ Finset.range (L + 1), WmidBlock R (2 ^ k) x) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hkL : k ≤ L := by rw [Finset.mem_range] at hk; omega
      have hpow_le : 2 ^ k ≤ R := by
        have hpowL : 2 ^ L ≤ R := by dsimp [L]; exact Nat.pow_log_le_self 2 hRne
        exact le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 2) hkL) hpowL
      exact WmidBlock_eq_zero_of_not_mid_range R (2 ^ k) x (Or.inl (by omega))
    have hbound_icc : ∀ k ∈ Finset.Icc (L + 1) U,
        WmidBlock R (2 ^ k) x ≤ 1.01 / (Real.log (R : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ)) := by
      intro k hk
      have hklo : L + 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkU : k ≤ U := (Finset.mem_Icc.mp hk).2
      have hRlt : R < 2 ^ (L + 1) := by
        dsimp [L]
        simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) R
      have hpowk : 2 ^ (L + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hklo
      have hRltk : R < 2 ^ k := lt_of_lt_of_le hRlt hpowk
      have hlt : 2 * R + 1 < 2 * 2 ^ k := by omega
      have hpowU : 2 ^ U ≤ 4 * R ^ 2 := by
        dsimp [U]
        exact Nat.pow_log_le_self 2 (by
          have hR2pos : 0 < R ^ 2 := pow_pos hRpos 2
          have h4R2pos : 0 < 4 * R ^ 2 := Nat.mul_pos (by norm_num : 0 < 4) hR2pos
          exact Nat.ne_of_gt h4R2pos)
      have hpowkU : 2 ^ k ≤ 2 ^ U := Nat.pow_le_pow_right (by norm_num : 0 < 2) hkU
      have hle : 2 ^ k ≤ 4 * R ^ 2 := le_trans hpowkU hpowU
      exact h R hR18 x k hlt hle
    have hsum_icc_le : (∑ k ∈ Finset.Icc (L + 1) U, WmidBlock R (2 ^ k) x)
        ≤ ∑ k ∈ Finset.Icc (L + 1) U,
          1.01 / (Real.log (R : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum hbound_icc
    have hterm_eq : (∑ k ∈ Finset.Icc (L + 1) U,
          1.01 / (Real.log (R : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ)))
        = (1.01 / Real.log (R : ℝ)) * dyadicLogReciprocalSum R := by
      unfold dyadicLogReciprocalSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hklo : L + 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hkpos : 0 < k := by omega
      have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
      have hlog2ne : Real.log 2 ≠ 0 := ne_of_gt hlog2pos
      have hlog2pow : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      rw [hlog2pow]
      field_simp [hlogRne, hkne, hlog2ne]
    have hdyadic : dyadicLogReciprocalSum R ≤ 2.05 := dyadicLogReciprocalSum_le_two R (by omega)
    have hlogRlower : (36 : ℝ) * 0.6931471803 ≤ Real.log (R : ℝ) := by
      have hRreal : ((2 ^ 36 : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
      have hlogmono : Real.log ((2 ^ 36 : ℕ) : ℝ) ≤ Real.log (R : ℝ) := by
        exact Real.log_le_log (by positivity) hRreal
      have hlogpow : Real.log ((2 ^ 36 : ℕ) : ℝ) = 36 * Real.log 2 := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
      nlinarith [hlogmono, hlogpow, Real.log_two_gt_d9]
    have hconst : (1.01 : ℝ) * 2.05 ≤ 0.085 * ((36 : ℝ) * 0.6931471803) := by norm_num
    have hmain : (1.01 / Real.log (R : ℝ)) * dyadicLogReciprocalSum R ≤ 0.085 := by
      have hmul : (1.01 / Real.log (R : ℝ)) * dyadicLogReciprocalSum R ≤
          (1.01 / Real.log (R : ℝ)) * 2.05 := by
        exact mul_le_mul_of_nonneg_left hdyadic
          (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 1.01) hlogRpos))
      have hmul2 : (1.01 / Real.log (R : ℝ)) * 2.05 ≤ 0.085 := by
        rw [div_mul_eq_mul_div]
        rw [div_le_iff₀ hlogRpos]
        nlinarith [hlogRlower, hconst]
      exact le_trans hmul hmul2
    have hwmid : Wmid R x ≤ ∑ k ∈ Finset.range (U + 1), WmidBlock R (2 ^ k) x := by
      rw [Wmid_eq_sum_dyadic R x]
    calc
      Wmid R x ≤ ∑ k ∈ Finset.range (U + 1), WmidBlock R (2 ^ k) x := hwmid
      _ = (∑ k ∈ Finset.range (L + 1), WmidBlock R (2 ^ k) x) +
          (∑ k ∈ Finset.Icc (L + 1) U, WmidBlock R (2 ^ k) x) := hsplit
      _ ≤ ∑ k ∈ Finset.Icc (L + 1) U, WmidBlock R (2 ^ k) x := by
            rw [hzero_low, zero_add]
      _ ≤ ∑ k ∈ Finset.Icc (L + 1) U,
          1.01 / (Real.log (R : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ)) := hsum_icc_le
      _ = (1.01 / Real.log (R : ℝ)) * dyadicLogReciprocalSum R := hterm_eq
      _ ≤ 0.085 := hmain

/-- Under the block-mass log bound, `x · prodOneSub x` tends to `atTop`. -/
theorem xP_tendsto_atTop_of_block_mass_log_bound
    (h : HA_WmidBlock_mass_log_bound) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop :=
  xP_tendsto_atTop_of_Wmid_constant_bound
    (HA_Wmid_constant_bound_of_block_mass_log_bound h)

end

end Erdos291
