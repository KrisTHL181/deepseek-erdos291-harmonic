import Erdos291.BlockMid
import Erdos291.DyadicBlocks
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Dyadic decomposition of `Wmid` in the prime variable

We define the block contribution

  `WmidBlock R P x = Σ_{R ≤ r < 2R} Σ_{P ≤ p < 2P, p ≤ x, 2r+1 < p ≤ r²,
      p prime, p ∣ num H_r} 1/(p-1)`

and prove the exact decomposition

  `Wmid R x = Σ_{k ∈ range (Nat.log 2 (4 * R ^ 2) + 1)} WmidBlock R (2 ^ k) x`.

For `r ∈ [R, 2R)` every middle prime satisfies `2r + 1 < p ≤ r² < 4R²`, so all
such primes lie below `2^(Nat.log 2 (4R²) + 1)`.  The dyadic intervals
`[2^k, 2^(k+1))`, `k = 0, …, Nat.log 2 (4R²)`, therefore partition the prime
range: the proof follows `DyadicBlocks.Aextra_eq_sum_dyadic_blocks`, first
partitioning the inner `p`-finset for each fixed `r`, then commuting the two
outer sums.

We also record the trivial facts that each block contribution is nonnegative
and that only blocks with `2R + 1 < 2P` and `P ≤ 4R²` can be nonzero.
-/

open scoped BigOperators

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The middle prime condition attached to `r`: `2r + 1 < p ≤ r²`, `p` is prime,
and `p` divides the numerator of the harmonic number `H_r`. -/
private abbrev midPrimeCond (r p : ℕ) : Prop :=
  2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num

/-- The contribution of the `r`-block `[R, 2R)` and the `p`-block `[P, 2P)` to
`Wmid R x`. -/
noncomputable def WmidBlock (R P x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R),
    ∑ p ∈ (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ midPrimeCond r p),
      (1 / ((p - 1 : ℕ) : ℝ))

/-- Each block contribution is nonnegative. -/
lemma WmidBlock_nonneg (R P x : ℕ) : 0 ≤ WmidBlock R P x := by
  unfold WmidBlock
  exact Finset.sum_nonneg (by
    intro r hr
    exact Finset.sum_nonneg (by
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)))

/-- If the prime block `[P, 2P)` does not intersect the middle range
`2R + 1 < p ≤ 4R²`, the block contribution vanishes. -/
lemma WmidBlock_eq_zero_of_not_mid_range (R P x : ℕ)
    (hP : 2 * P ≤ 2 * R + 1 ∨ 4 * R ^ 2 ≤ P) :
    WmidBlock R P x = 0 := by
  unfold WmidBlock
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro p hp
  have hpF := Finset.mem_filter.mp hp
  have hpIco : p ∈ Finset.Ico P (2 * P) := hpF.1
  have hcond : p ≤ x ∧ midPrimeCond r p := hpF.2
  rcases hcond with ⟨_hpx, h2rp, hle, _hpPrime, _hdvd⟩
  have hp_lo : P ≤ p := (Finset.mem_Ico.mp hpIco).1
  have hp_hi : p < 2 * P := (Finset.mem_Ico.mp hpIco).2
  have hr_lo : R ≤ r := (Finset.mem_Ico.mp hr).1
  have hr_hi : r < 2 * R := (Finset.mem_Ico.mp hr).2
  rcases hP with hleft | hright
  · have hp_le : p ≤ 2 * R := by omega
    have h_low : 2 * R + 1 ≤ 2 * r + 1 := by omega
    omega
  · have hsq : r ^ 2 < 4 * R ^ 2 := by nlinarith
    have hp_ge : 4 * R ^ 2 ≤ p := by omega
    omega

/-- The finset of middle primes for a fixed `r`, over the full range `[2, x]`. -/
private abbrev midPrimes (x r : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter (fun p => midPrimeCond r p)

/-! ## Partition of the prime range into dyadic blocks -/

/-- For `r ∈ [R, 2R)`, the middle primes `p ≤ r² < 4R²` are partitioned by the
dyadic blocks `[2^k, 2^(k+1))`, `k = 0, …, Nat.log 2 (4R²)`. -/
private lemma midPrimes_eq_biUnion_dyadic_blocks (R x r : ℕ)
    (hr : r ∈ Finset.Ico R (2 * R)) :
    midPrimes x r =
      (Finset.range (Nat.log 2 (4 * R ^ 2) + 1)).biUnion
        (fun k => (midPrimes x r).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))) := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 p, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hcond : midPrimeCond r p := (Finset.mem_filter.mp hp).2
      rcases hcond with ⟨_h2rp, hle, hpPrime, _hdvd⟩
      have hr_hi : r < 2 * R := (Finset.mem_Ico.mp hr).2
      have hsq : r ^ 2 < 4 * R ^ 2 := by nlinarith
      have hp_lt : p < 4 * R ^ 2 := lt_of_le_of_lt hle hsq
      have hpow : 4 * R ^ 2 < 2 ^ (Nat.log 2 (4 * R ^ 2) + 1) := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) (4 * R ^ 2))
      have hp_lt_pow : p < 2 ^ (Nat.log 2 (4 * R ^ 2) + 1) := lt_trans hp_lt hpow
      have hp_ne : p ≠ 0 := by
        have hp2 : 2 ≤ p := hpPrime.two_le
        omega
      exact Nat.log_lt_of_lt_pow (b := 2) (y := p)
        (x := Nat.log 2 (4 * R ^ 2) + 1) hp_ne hp_lt_pow
    · rw [Finset.mem_filter]
      constructor
      · exact hp
      · constructor
        · have hp_ne : p ≠ 0 := by
            have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.2.2.1
            have hp2 : 2 ≤ p := hpPrime.two_le
            omega
          exact Nat.pow_log_le_self 2 hp_ne
        · simpa [Nat.succ_eq_add_one] using
            (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) p)
  · intro hp
    rw [Finset.mem_biUnion] at hp
    rcases hp with ⟨k, hk, hkblock⟩
    exact (Finset.mem_filter.mp hkblock).1

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

/-- Restricting `midPrimes x r` to the dyadic block `[2^k, 2^(k+1))` is the same
as the `p`-block finset used in `WmidBlock R (2 ^ k) x`. -/
private lemma midPrimes_filter_dyadic_eq_block (R x r k : ℕ) :
    (midPrimes x r).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1))
      = (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun p => p ≤ x ∧ midPrimeCond r p) := by
  ext p
  constructor
  · intro hp
    have hpMidF := Finset.mem_filter.mp (Finset.mem_filter.mp hp).1
    have hpIcc : p ∈ Finset.Icc 2 x := hpMidF.1
    have hcond : midPrimeCond r p := hpMidF.2
    have hpdy : 2 ^ k ≤ p ∧ p < 2 ^ (k + 1) := (Finset.mem_filter.mp hp).2
    have hpx : p ≤ x := (Finset.mem_Icc.mp hpIcc).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hpdy, ⟨hpx, hcond⟩⟩
  · intro hp
    have hpF := Finset.mem_filter.mp hp
    have hpIco : p ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := hpF.1
    have hcond : p ≤ x ∧ midPrimeCond r p := hpF.2
    have hpPrime : Nat.Prime p := hcond.2.2.2.1
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hpIcc : p ∈ Finset.Icc 2 x := Finset.mem_Icc.mpr ⟨hp2, hcond.1⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hpIcc, hcond.2⟩, Finset.mem_Ico.mp hpIco⟩

/-! ## The dyadic decomposition of `Wmid` -/

/-- `Wmid R x` is the sum of its prime-dyadic block contributions
`WmidBlock R (2 ^ k) x` over `k = 0, …, Nat.log 2 (4R²)`. -/
theorem Wmid_eq_sum_dyadic (R x : ℕ) :
    Wmid R x =
      ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        WmidBlock R (2 ^ k) x := by
  calc
    Wmid R x = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ midPrimes x r, (1 / ((p - 1 : ℕ) : ℝ)) := by
          dsimp [Wmid, midPrimes, midPrimeCond]
    _ = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
          ∑ p ∈ (midPrimes x r).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)),
            (1 / ((p - 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro r hr
          have hpart := midPrimes_eq_biUnion_dyadic_blocks R x r hr
          have hdisj := dyadic_blocks_pairwiseDisjoint (midPrimes x r) (Nat.log 2 (4 * R ^ 2))
          conv_lhs => rw [hpart]
          rw [Finset.sum_biUnion (hs := hdisj)]
    _ = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        ∑ r ∈ Finset.Ico R (2 * R),
          ∑ p ∈ (midPrimes x r).filter (fun p => 2 ^ k ≤ p ∧ p < 2 ^ (k + 1)),
            (1 / ((p - 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        ∑ r ∈ Finset.Ico R (2 * R),
          ∑ p ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
              (fun p => p ≤ x ∧ midPrimeCond r p),
            (1 / ((p - 1 : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro r hr
          rw [midPrimes_filter_dyadic_eq_block R x r k]
    _ = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        WmidBlock R (2 ^ k) x := by
          apply Finset.sum_congr rfl
          intro k hk
          unfold WmidBlock
          rw [show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ']]

end Erdos291
