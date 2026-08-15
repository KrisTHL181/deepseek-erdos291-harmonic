import Erdos291.BlockActive
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Dyadic decomposition of the active prime mass

Cloud data suggests the whole remaining goal reduces to the active-prime-mass
bound `activeMass R x ≤ C` with `C < log 2 / 16`.  This file supplies the
dyadic-in-`p` machinery for attacking that bound.

Two honest decompositions are proved.

* `activeMass R x`, whose active condition is only `E p ∩ [R, 2R) ≠ ∅`, has
  **no** upper bound on `p` (a prime with a bad digit in `[R, 2R)` can be much
  larger than `R²`), so its dyadic decomposition runs over
  `k = 0, …, Nat.log 2 x`:

    `activeMass R x = Σ_k activeMassBlock R (2 ^ k) x`.

  Only the lower cutoff `R < p` is forced by the active condition, which gives
  the zero-range lemma `activeMassBlock R P x = 0` when `2P ≤ R + 1`.

* The quantity actually needed for `Wmid` is the **middle** active mass, where
  we additionally require `p ≤ 4R²` (every middle prime satisfies
  `p ≤ r² < 4R²`).  We define `middleActiveMass R x` with that cutoff; then only
  the `O(log R)` blocks `P = 2^k ≤ 4R²` can contribute:

    `middleActiveMass R x = Σ_{k ≤ Nat.log 2 (4R²)} middleActiveMassBlock R (2 ^ k) x`.

The per-block count `activePrimeCount R P x` and the inequalities
`activeMassBlock R P x ≤ activePrimeCount / (P-1) ≤ 2 · activePrimeCount / P`
reduce the active-mass problem to the zero-density statement that few primes in
`[P, 2P)` are active; the target block-density hypothesis is recorded as
`HA_activeMass_block_density`.
-/

open scoped BigOperators

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The contribution of the prime block `[P, 2P)` to `activeMass R x`. -/
noncomputable def activeMassBlock (R P x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ico P (2 * P)).filter
      (fun p => p ≤ x ∧ Nat.Prime p ∧ (E p ∩ Finset.Ico R (2 * R)).Nonempty),
    primeWeight p

/-- The number of active primes in the block `[P, 2P)`: primes `p ≤ x` with
`E p ∩ [R, 2R) ≠ ∅`. -/
noncomputable def activePrimeCount (R P x : ℕ) : ℕ :=
  ((Finset.Ico P (2 * P)).filter
    (fun p => p ≤ x ∧ Nat.Prime p ∧ (E p ∩ Finset.Ico R (2 * R)).Nonempty)).card

/-- The middle active mass: only primes `p ≤ 4R²` are kept, which is the range
relevant for `Wmid` (every middle pair satisfies `p ≤ r² < 4R²`). -/
noncomputable def middleActiveMass (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R ^ 2),
    if (E p ∩ Finset.Ico R (2 * R)).Nonempty then
      primeWeight p
    else 0

/-- The contribution of the prime block `[P, 2P)` to `middleActiveMass R x`. -/
noncomputable def middleActiveMassBlock (R P x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ico P (2 * P)).filter
      (fun p => p ≤ x ∧ Nat.Prime p ∧
        (E p ∩ Finset.Ico R (2 * R)).Nonempty ∧ p ≤ 4 * R ^ 2),
    primeWeight p

/-- `activeMassBlock` is nonnegative. -/
lemma activeMassBlock_nonneg (R P x : ℕ) : 0 ≤ activeMassBlock R P x := by
  unfold activeMassBlock
  exact Finset.sum_nonneg (by
    intro p hp
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

/-- `middleActiveMassBlock` is nonnegative. -/
lemma middleActiveMassBlock_nonneg (R P x : ℕ) : 0 ≤ middleActiveMassBlock R P x := by
  unfold middleActiveMassBlock
  exact Finset.sum_nonneg (by
    intro p hp
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

/-- The set of primes considered by `activeMass`. -/
private abbrev primeSet (x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter Nat.Prime

/-- The set of primes considered by `middleActiveMass`. -/
private abbrev middlePrimeSet (R x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R ^ 2)

/-- The active indicator for the full active mass. -/
noncomputable abbrev activeIndicator (R p : ℕ) : ℝ :=
  if (E p ∩ Finset.Ico R (2 * R)).Nonempty then primeWeight p else 0

/-! ## Generic dyadic partition lemmas -/

/-- Dyadic blocks are pairwise disjoint. -/
private lemma dyadic_blocks_pairwiseDisjoint (S : Finset ℕ) (K : ℕ) :
    (↑(Finset.range (K + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => S.filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))) := by
  unfold Set.PairwiseDisjoint Function.onFun
  intro k hk l hl hkl
  rw [Finset.disjoint_left]
  intro p hpk hpl
  have hpk_lo : 2 ^ k ≤ p := (Finset.mem_filter.mp hpk).2.1
  have hpk_hi : p < 2 ^ (k + 1) := (Finset.mem_filter.mp hpk).2.2
  have hpl_lo : 2 ^ l ≤ p := (Finset.mem_filter.mp hpl).2.1
  have hpl_hi : p < 2 ^ (l + 1) := (Finset.mem_filter.mp hpl).2.2
  rcases lt_or_gt_of_ne hkl with hklt | hlkt
  · have hs : k + 1 ≤ l := Nat.succ_le_of_lt hklt
    have hpow : 2 ^ (k + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num : 0 < 2) hs
    omega
  · have hs : l + 1 ≤ k := Nat.succ_le_of_lt hlkt
    have hpow : 2 ^ (l + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hs
    omega

/-- `primeSet x` is partitioned by the dyadic blocks
`[2^k, 2^(k+1))`, `k = 0, …, Nat.log 2 x`. -/
private lemma primeSet_eq_biUnion_dyadic (x : ℕ) :
    primeSet x = (Finset.range (Nat.log 2 x + 1)).biUnion
      (fun k => (primeSet x).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))) := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 p, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hpF := Finset.mem_filter.mp hp
      have hpIcc := Finset.mem_Icc.mp hpF.1
      have hpx : p ≤ x := hpIcc.2
      have hpow : x < 2 ^ (Nat.log 2 x + 1) := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) x)
      have hp_lt : p < 2 ^ (Nat.log 2 x + 1) := lt_of_le_of_lt hpx hpow
      have hp_ne : p ≠ 0 := by omega
      exact Nat.log_lt_of_lt_pow (b := 2) (y := p)
        (x := Nat.log 2 x + 1) hp_ne hp_lt
    · rw [Finset.mem_filter]
      constructor
      · exact hp
      · constructor
        · have hpF := Finset.mem_filter.mp hp
          have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hpF.1).1
          have hp_ne : p ≠ 0 := by omega
          exact Nat.pow_log_le_self 2 hp_ne
        · simpa [Nat.succ_eq_add_one] using
            (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) p)
  · intro hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨k, hk, hkblock⟩
    exact (Finset.mem_filter.mp hkblock).1

/-- `middlePrimeSet R x` is partitioned by the dyadic blocks
`[2^k, 2^(k+1))`, `k = 0, …, Nat.log 2 (4R²)`. -/
private lemma middlePrimeSet_eq_biUnion_dyadic (R x : ℕ) :
    middlePrimeSet R x = (Finset.range (Nat.log 2 (4 * R ^ 2) + 1)).biUnion
      (fun k => (middlePrimeSet R x).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))) := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 p, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hpF := Finset.mem_filter.mp hp
      have hpIcc := Finset.mem_Icc.mp hpF.1
      have hple : p ≤ 4 * R ^ 2 := hpF.2.2
      have hpow : 4 * R ^ 2 < 2 ^ (Nat.log 2 (4 * R ^ 2) + 1) := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) (4 * R ^ 2))
      have hp_lt : p < 2 ^ (Nat.log 2 (4 * R ^ 2) + 1) := lt_of_le_of_lt hple hpow
      have hp_ne : p ≠ 0 := by omega
      exact Nat.log_lt_of_lt_pow (b := 2) (y := p)
        (x := Nat.log 2 (4 * R ^ 2) + 1) hp_ne hp_lt
    · rw [Finset.mem_filter]
      constructor
      · exact hp
      · constructor
        · have hpF := Finset.mem_filter.mp hp
          have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hpF.1).1
          have hp_ne : p ≠ 0 := by omega
          exact Nat.pow_log_le_self 2 hp_ne
        · simpa [Nat.succ_eq_add_one] using
            (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) p)
  · intro hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨k, hk, hkblock⟩
    exact (Finset.mem_filter.mp hkblock).1

/-! ## The full dyadic decomposition of `activeMass` -/

/-- The active block vanishes unless its prime range can meet `[R, 2R)`:
an active `p` satisfies `R < p`, so `2P ≤ R + 1` kills the block. -/
lemma activeMassBlock_eq_zero_of_not_active_range (R P x : ℕ)
    (h : 2 * P ≤ R + 1) :
    activeMassBlock R P x = 0 := by
  unfold activeMassBlock
  apply Finset.sum_eq_zero
  intro p hp
  have hpF := Finset.mem_filter.mp hp
  have hpIco : p ∈ Finset.Ico P (2 * P) := hpF.1
  have hactive : (E p ∩ Finset.Ico R (2 * R)).Nonempty := hpF.2.2.2
  rcases hactive with ⟨r, hr⟩
  have hrE : r ∈ E p := (Finset.mem_inter.mp hr).1
  have hrI := Finset.mem_Ico.mp (Finset.mem_inter.mp hr).2
  have hrEp : r ≤ p - 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).2
  have hp_lt : p < 2 * P := (Finset.mem_Ico.mp hpIco).2
  have hp_le_R : p ≤ R := by omega
  omega

/-- `activeMass R x` is exactly the sum of its prime-dyadic block contributions
`activeMassBlock R (2 ^ k) x` over `k = 0, …, Nat.log 2 x`. -/
theorem activeMass_eq_sum_dyadic (R x : ℕ) :
    activeMass R x =
      ∑ k ∈ Finset.range (Nat.log 2 x + 1), activeMassBlock R (2 ^ k) x := by
  calc
    activeMass R x = ∑ p ∈ primeSet x, activeIndicator R p := by
      dsimp [activeMass, activeIndicator]
    _ = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ p ∈ (primeSet x).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)),
          activeIndicator R p := by
          conv_lhs => rw [primeSet_eq_biUnion_dyadic x]
          rw [Finset.sum_biUnion
            (hs := dyadic_blocks_pairwiseDisjoint (primeSet x) (Nat.log 2 x))]
    _ = ∑ k ∈ Finset.range (Nat.log 2 x + 1),
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
            (fun p => p ≤ x ∧ Nat.Prime p ∧ (E p ∩ Finset.Ico R (2 * R)).Nonempty),
          primeWeight p := by
          apply Finset.sum_congr rfl
          intro k hk
          have hsum : (∑ p ∈ (primeSet x).filter
                (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)), activeIndicator R p)
              = ∑ p ∈ ((primeSet x).filter
                    (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))).filter
                  (fun p => (E p ∩ Finset.Ico R (2 * R)).Nonempty), primeWeight p := by
            dsimp [activeIndicator]
            rw [← Finset.sum_filter]
          have hset : ((primeSet x).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))).filter
                (fun p => (E p ∩ Finset.Ico R (2 * R)).Nonempty)
              = (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
                  (fun p => p ≤ x ∧ Nat.Prime p ∧
                    (E p ∩ Finset.Ico R (2 * R)).Nonempty) := by
            ext p
            constructor
            · intro hp
              have hpf := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
              have hprimeSet : p ∈ primeSet x := hpf.1
              have hdy := hpf.2
              have hactive : (E p ∩ Finset.Ico R (2 * R)).Nonempty :=
                (Finset.mem_filter.mp hp).2
              have hpP := Finset.mem_filter.mp hprimeSet
              have hpIcc : p ∈ Finset.Icc 2 x := hpP.1
              have hpx : p ≤ x := (Finset.mem_Icc.mp hpIcc).2
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_Ico.mpr hdy, hpx, hpP.2, hactive⟩
            · intro hp
              have hpF := Finset.mem_filter.mp hp
              have hpIco : p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := hpF.1
              have hcond : p ≤ x ∧ Nat.Prime p ∧
                  (E p ∩ Finset.Ico R (2 * R)).Nonempty := hpF.2
              have hp2 : 2 ≤ p := hcond.2.1.two_le
              have hpP : p ∈ primeSet x := Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨hp2, hcond.1⟩, hcond.2.1⟩
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨hpP, Finset.mem_Ico.mp hpIco⟩, hcond.2.2⟩
          rw [hsum, hset]
    _ = ∑ k ∈ Finset.range (Nat.log 2 x + 1), activeMassBlock R (2 ^ k) x := by
          apply Finset.sum_congr rfl
          intro k hk
          unfold activeMassBlock
          rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ']]

/-! ## The middle active mass and its dyadic decomposition -/

/-- The middle active mass is at most the full active mass. -/
lemma middleActiveMass_le_activeMass (R x : ℕ) :
    middleActiveMass R x ≤ activeMass R x := by
  unfold middleActiveMass activeMass
  have hsub : (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R ^ 2)
      ⊆ (Finset.Icc 2 x).filter Nat.Prime := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
  have hnonneg : ∀ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      p ∉ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ p ≤ 4 * R ^ 2) →
        0 ≤ (if (E p ∩ Finset.Ico R (2 * R)).Nonempty then primeWeight p else 0) := by
    intro p hp hnot
    by_cases h : (E p ∩ Finset.Ico R (2 * R)).Nonempty
    · simp [h]
    · simp [h]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

/-- `middleActiveMass R x` is exactly the sum of its prime-dyadic block
contributions over `k = 0, …, Nat.log 2 (4R²)`. -/
theorem middleActiveMass_eq_sum_dyadic (R x : ℕ) :
    middleActiveMass R x =
      ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        middleActiveMassBlock R (2 ^ k) x := by
  calc
    middleActiveMass R x = ∑ p ∈ middlePrimeSet R x, activeIndicator R p := by
      dsimp [middleActiveMass, activeIndicator]
    _ = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        ∑ p ∈ (middlePrimeSet R x).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)),
          activeIndicator R p := by
          conv_lhs => rw [middlePrimeSet_eq_biUnion_dyadic R x]
          rw [Finset.sum_biUnion
            (hs := dyadic_blocks_pairwiseDisjoint (middlePrimeSet R x)
              (Nat.log 2 (4 * R ^ 2)))]
    _ = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
            (fun p => p ≤ x ∧ Nat.Prime p ∧
              (E p ∩ Finset.Ico R (2 * R)).Nonempty ∧ p ≤ 4 * R ^ 2),
          primeWeight p := by
          apply Finset.sum_congr rfl
          intro k hk
          have hsum : (∑ p ∈ (middlePrimeSet R x).filter
                (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)), activeIndicator R p)
              = ∑ p ∈ ((middlePrimeSet R x).filter
                    (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))).filter
                  (fun p => (E p ∩ Finset.Ico R (2 * R)).Nonempty), primeWeight p := by
            dsimp [activeIndicator]
            rw [← Finset.sum_filter]
          have hset : ((middlePrimeSet R x).filter
                  (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))).filter
                (fun p => (E p ∩ Finset.Ico R (2 * R)).Nonempty)
              = (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
                  (fun p => p ≤ x ∧ Nat.Prime p ∧
                    (E p ∩ Finset.Ico R (2 * R)).Nonempty ∧ p ≤ 4 * R ^ 2) := by
            ext p
            constructor
            · intro hp
              have hpf := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
              have hmP : p ∈ middlePrimeSet R x := hpf.1
              have hdy := hpf.2
              have hactive : (E p ∩ Finset.Ico R (2 * R)).Nonempty :=
                (Finset.mem_filter.mp hp).2
              have hmP' := Finset.mem_filter.mp hmP
              have hpIcc : p ∈ Finset.Icc 2 x := hmP'.1
              have hpx : p ≤ x := (Finset.mem_Icc.mp hpIcc).2
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_Ico.mpr hdy, hpx, hmP'.2.1, hactive, hmP'.2.2⟩
            · intro hp
              have hpF := Finset.mem_filter.mp hp
              have hpIco : p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := hpF.1
              have hcond : p ≤ x ∧ Nat.Prime p ∧
                  (E p ∩ Finset.Ico R (2 * R)).Nonempty ∧ p ≤ 4 * R ^ 2 := hpF.2
              have hp2 : 2 ≤ p := hcond.2.1.two_le
              have hmP : p ∈ middlePrimeSet R x := Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨hp2, hcond.1⟩, hcond.2.1, hcond.2.2.2⟩
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_filter.mpr ⟨hmP, Finset.mem_Ico.mp hpIco⟩, hcond.2.2.1⟩
          rw [hsum, hset]
    _ = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        middleActiveMassBlock R (2 ^ k) x := by
          apply Finset.sum_congr rfl
          intro k hk
          unfold middleActiveMassBlock
          rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ']]

/-! ## From active mass to the active-prime count -/

/-- `1/(P-1) ≤ 2/P` for `2 ≤ P`. -/
lemma one_div_sub_one_le_two_div (P : ℕ) (hP : 2 ≤ P) :
    (1 : ℝ) / ((P - 1 : ℕ) : ℝ) ≤ 2 / (P : ℝ) := by
  have hPpos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hPm1pos : 0 < ((P - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < P - 1)
  have hPm1 : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ P)]
    norm_num
  field_simp [hPpos.ne', hPm1pos.ne']
  rw [hPm1]
  have hP2 : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  nlinarith

/-- The block mass is controlled by the count of active primes in the block,
with the exact denominator `P - 1`. -/
theorem activeMassBlock_le_activePrimeCount_div_sub_one (R P x : ℕ) (hP : 2 ≤ P) :
    activeMassBlock R P x ≤
      (activePrimeCount R P x : ℝ) / ((P - 1 : ℕ) : ℝ) := by
  unfold activeMassBlock activePrimeCount
  let S : Finset ℕ := (Finset.Ico P (2 * P)).filter
    (fun p => p ≤ x ∧ Nat.Prime p ∧ (E p ∩ Finset.Ico R (2 * R)).Nonempty)
  have hwle : ∀ p ∈ S, primeWeight p ≤ 1 / ((P - 1 : ℕ) : ℝ) := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpF.1
    have hPp : P ≤ p := hpIco.1
    have hsub : P - 1 ≤ p - 1 := Nat.sub_le_sub_right hPp 1
    have hpos : 0 < ((P - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < P - 1)
    have hcast : ((P - 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hsub
    dsimp [primeWeight]
    exact one_div_le_one_div_of_le hpos hcast
  have hsum' : (∑ q ∈ S, primeWeight q) ≤ S.card • (1 / ((P - 1 : ℕ) : ℝ)) :=
    Finset.sum_le_card_nsmul S (fun q => primeWeight q) (1 / ((P - 1 : ℕ) : ℝ)) hwle
  have hsum'' : (∑ q ∈ S, primeWeight q) ≤ (S.card : ℝ) / ((P - 1 : ℕ) : ℝ) := by
    calc
      (∑ q ∈ S, primeWeight q) ≤ S.card • (1 / ((P - 1 : ℕ) : ℝ)) := hsum'
      _ = (S.card : ℝ) * (1 / ((P - 1 : ℕ) : ℝ)) := by rw [nsmul_eq_mul]
      _ = (S.card : ℝ) / ((P - 1 : ℕ) : ℝ) := by rw [mul_one_div]
  simpa [S] using hsum''

/-- With the looser denominator `P`, each block mass is at most
`2 * activePrimeCount R P x / P`. -/
theorem activeMassBlock_le_two_mul_activePrimeCount_div (R P x : ℕ) (hP : 2 ≤ P) :
    activeMassBlock R P x ≤ 2 * (activePrimeCount R P x : ℝ) / (P : ℝ) := by
  calc
    activeMassBlock R P x ≤
        (activePrimeCount R P x : ℝ) / ((P - 1 : ℕ) : ℝ) :=
      activeMassBlock_le_activePrimeCount_div_sub_one R P x hP
    _ = (activePrimeCount R P x : ℝ) * (1 / ((P - 1 : ℕ) : ℝ)) := by
      rw [mul_one_div]
    _ ≤ (activePrimeCount R P x : ℝ) * (2 / (P : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (one_div_sub_one_le_two_div P hP)
        (Nat.cast_nonneg _)
    _ = 2 * (activePrimeCount R P x : ℝ) / (P : ℝ) := by
      ring_nf

/-! ## The per-block zero-density target -/

/-- **The zero-density target.**  For every relevant dyadic prime block
(`R + 1 < 2P`, `P ≤ 4R²`), the active prime mass of the block is at most
`C / log P` with a universal constant `C < log 2 / 16`.  Cloud data supports
this with `C ≈ 0.04`; together with the dyadic decomposition of the middle
active mass it is the intended route to `HA_activeMass_small`. -/
def HA_activeMass_block_density : Prop :=
  ∃ C : ℝ, 0 < C ∧ C < Real.log 2 / 16 ∧
    ∀ R P x : ℕ, 2 ≤ R → 2 ≤ P → R + 1 < 2 * P → P ≤ 4 * R ^ 2 →
      activeMassBlock R P x ≤ C / Real.log (P : ℝ)

end Erdos291
