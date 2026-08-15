import Erdos291.SymmetryOrbits
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Dyadic block decomposition of `Aextra`

We define the dyadic block contribution

  `W R x = Σ_{p ≤ x, p prime} Σ_{r ∈ T p, R ≤ r < 2R} 1/(p-1)`

and prove that `Aextra x` is exactly the sum of the contributions of the
dyadic blocks `[2^k, 2^(k+1))` for `k = 0, …, Nat.log 2 x`:

  `Aextra x = Σ_{k ∈ range (Nat.log 2 x + 1)} W (2^k) x`.

The proof avoids a bijection between the double and triple sums: for each
prime `p` the finset `T p` is partitioned by the dyadic blocks, the blocks
are pairwise disjoint, and `Finset.sum_biUnion` together with
`Finset.sum_comm` performs the rearrangement.
-/

open scoped BigOperators

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The contribution of the dyadic block `[R, 2R)` to `Aextra x`. -/
noncomputable def W (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
    ∑ r ∈ (T p).filter (fun r => R ≤ r ∧ r < 2 * R),
      (1 / ((p - 1 : ℕ) : ℝ))

private lemma one_le_of_mem_T (p r : ℕ) (hr : r ∈ T p) : 1 ≤ r := by
  dsimp [T] at hr
  have hrE : r ∈ E p := (Finset.mem_filter.mp hr).1
  dsimp [E] at hrE
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).1

private lemma T_eq_biUnion_dyadic_blocks (x p : ℕ)
    (hp : p ∈ (Finset.Icc 2 x).filter Nat.Prime) :
    T p = (Finset.range (Nat.log 2 x + 1)).biUnion
      (fun k => (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1))) := by
  ext r
  constructor
  · intro hr
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 r, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hpIcc : 2 ≤ p ∧ p ≤ x := Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1
      have hrTlt : 2 * r < p - 1 := (Finset.mem_filter.mp hr).2
      have hr_ge1 : 1 ≤ r := one_le_of_mem_T p r hr
      have hr_pos : r ≠ 0 := by omega
      have hr_lt_x : r < x := by omega
      have hxpow : x < 2 ^ (Nat.log 2 x + 1) := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) x)
      have hrpow : r < 2 ^ (Nat.log 2 x + 1) := lt_trans hr_lt_x hxpow
      have hloglt : Nat.log 2 r < Nat.log 2 x + 1 := by
        simpa [Nat.succ_eq_add_one] using
          (Nat.log_lt_of_lt_pow (b := 2) (y := r) (x := Nat.log 2 x + 1) hr_pos hrpow)
      omega
    · rw [Finset.mem_filter]
      constructor
      · exact hr
      · constructor
        · have hr_pos : r ≠ 0 := by
            have hr_ge1 : 1 ≤ r := one_le_of_mem_T p r hr
            omega
          exact Nat.pow_log_le_self 2 hr_pos
        · simpa [Nat.succ_eq_add_one] using
            (Nat.lt_pow_succ_log_self (b := 2) (by norm_num : 1 < 2) r)
  · intro hr
    rw [Finset.mem_biUnion] at hr
    rcases hr with ⟨k, hk, hkblock⟩
    exact (Finset.mem_filter.mp hkblock).1

private lemma dyadic_blocks_pairwiseDisjoint (p K : ℕ) :
    (↑(Finset.range (K + 1)) : Set ℕ).PairwiseDisjoint
      (fun k => (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1))) := by
  unfold Set.PairwiseDisjoint Function.onFun
  intro k hk l hl hkl
  rw [Finset.disjoint_left]
  intro r hrk hrl
  have hrk_lo : 2 ^ k ≤ r := (Finset.mem_filter.mp hrk).2.1
  have hrk_hi : r < 2 ^ (k + 1) := (Finset.mem_filter.mp hrk).2.2
  have hrl_lo : 2 ^ l ≤ r := (Finset.mem_filter.mp hrl).2.1
  have hrl_hi : r < 2 ^ (l + 1) := (Finset.mem_filter.mp hrl).2.2
  rcases lt_or_gt_of_ne hkl with hklt | hlkt
  · have hs : k + 1 ≤ l := Nat.succ_le_of_lt hklt
    have hpow : 2 ^ (k + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num : 0 < 2) hs
    omega
  · have hs : l + 1 ≤ k := Nat.succ_le_of_lt hlkt
    have hpow : 2 ^ (l + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) hs
    omega

private lemma T_card_div (p : ℕ) :
    ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) =
      ∑ r ∈ T p, (1 / ((p - 1 : ℕ) : ℝ)) := by
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_div]

theorem Aextra_eq_sum_dyadic_blocks (x : ℕ) :
    Aextra x =
      ∑ k ∈ Finset.range (Nat.log 2 x + 1), W (2 ^ k) x := by
  let K := Nat.log 2 x
  let P : Finset ℕ := (Finset.Icc 2 x).filter Nat.Prime
  unfold Aextra
  calc
    (∑ p ∈ P, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ))
        = ∑ p ∈ P, ∑ r ∈ T p, (1 / ((p - 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact T_card_div p
    _ = ∑ k ∈ Finset.range (K + 1), W (2 ^ k) x := by
            have hpart (p : ℕ) (hp : p ∈ P) :
                T p = (Finset.range (K + 1)).biUnion
                  (fun k => (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1))) := by
              have := T_eq_biUnion_dyadic_blocks x p hp
              simpa [P, K] using this
            have hdisj (p : ℕ) :
                (↑(Finset.range (K + 1)) : Set ℕ).PairwiseDisjoint
                  (fun k => (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1))) := by
              have := dyadic_blocks_pairwiseDisjoint p K
              simpa [K] using this
            have hinner (p : ℕ) (hp : p ∈ P) :
                (∑ r ∈ T p, (1 / ((p - 1 : ℕ) : ℝ))) =
                  ∑ k ∈ Finset.range (K + 1),
                    ∑ r ∈ (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1)),
                      (1 / ((p - 1 : ℕ) : ℝ)) := by
              conv_lhs =>
                rw [hpart p hp]
              rw [Finset.sum_biUnion (hs := hdisj p)]
            calc
              (∑ p ∈ P, ∑ r ∈ T p, (1 / ((p - 1 : ℕ) : ℝ)))
                  = ∑ p ∈ P, ∑ k ∈ Finset.range (K + 1),
                      ∑ r ∈ (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1)),
                        (1 / ((p - 1 : ℕ) : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    exact hinner p hp
              _ = ∑ k ∈ Finset.range (K + 1), ∑ p ∈ P,
                    ∑ r ∈ (T p).filter (fun r => 2 ^ k ≤ r ∧ r < 2 ^ (k + 1)),
                      (1 / ((p - 1 : ℕ) : ℝ)) := by
                    rw [Finset.sum_comm]
              _ = ∑ k ∈ Finset.range (K + 1), W (2 ^ k) x := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    unfold W
                    apply Finset.sum_congr rfl
                    intro p hp
                    have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by
                      rw [pow_succ']
                    rw [hpow]

end Erdos291
