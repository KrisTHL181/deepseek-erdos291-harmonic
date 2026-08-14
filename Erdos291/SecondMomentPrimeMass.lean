import Erdos291.SecondMomentDoubleCount
import Erdos291.PairGCD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Erdős #291 — the gcd-prime-mass identity for the second moment

This file proves identity (E): the column second moment

  `M x = Σ_{p ≤ x} f_p (f_p - 1) / (p - 1)`

equals twice a gcd-prime-mass double sum:

  `M x = 2 · Σ_{r ≤ x} Σ_{d ≤ x} Σ_{p ≤ x, r + d < p, p ∣ gcd(A_r, Q_d(r))} 1 / (p - 1)`.

The chain is:

* `M_eq_two_mul_sum_dist` (in `SecondMomentDoubleCount`) expresses `M x` as a sum over
  primes `p` and distances `d` of the pair-count `#{r | r, r + d ∈ E p}`.
* `E_filter_add_eq_gcd_filter` uses `pair_bad_iff_prime_dvd_gcd` (in `PairGCD`) to rewrite
  each pair-count fibre as a gcd filter.
* Two Fubini steps (`sum_comm'`, `sum_subset`, `sum_comm`, `sum_filter`) reindex the triple
  sum so that `r, d` range over `Finset.Icc 1 x` and `p` is innermost.

There are no unproved declarations in this file.
-/

open scoped BigOperators

namespace Erdos291

/-! ## Step (b): each distance fibre is a gcd filter -/

/-- For a prime `p`, the set of `r` with `r, r + d ∈ E p` is exactly the set of
`r ∈ [1, p - 1 - d]` such that `p ∣ gcd (A r) (Qval r d)`. -/
lemma E_filter_add_eq_gcd_filter (p d : ℕ) [Fact p.Prime] :
    (E p).filter (fun r => r + d ∈ E p)
      = (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)) := by
  ext r
  simp only [Finset.mem_filter]
  constructor
  · intro hr
    rcases hr with ⟨hrE, hrdE⟩
    have hEsub : E p ⊆ Finset.Icc 1 (p - 1) := by
      rw [E]
      exact Finset.filter_subset _ _
    have hrIcc : r ∈ Finset.Icc 1 (p - 1) := hEsub hrE
    have hrdIcc : r + d ∈ Finset.Icc 1 (p - 1) := hEsub hrdE
    have h1r : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
    have hrd_le : r + d ≤ p - 1 := (Finset.mem_Icc.mp hrdIcc).2
    have hrd_lt : r + d < p := by omega
    have hgcd : p ∣ Nat.gcd (A r) (Qval r d) :=
      (pair_bad_iff_prime_dvd_gcd p r d h1r hrd_lt).mp ⟨hrE, hrdE⟩
    refine ⟨?_, hgcd⟩
    rw [Finset.mem_Icc]
    exact ⟨h1r, by omega⟩
  · intro hr
    rcases hr with ⟨hrIcc, hgcd⟩
    have h1r : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
    have hr_le : r ≤ p - 1 - d := (Finset.mem_Icc.mp hrIcc).2
    have hrd_lt : r + d < p := by omega
    exact (pair_bad_iff_prime_dvd_gcd p r d h1r hrd_lt).mpr hgcd

/-- The cardinality of a distance fibre, as a sum of ones over the gcd filter. -/
lemma E_add_card_eq_sum_gcd (p d : ℕ) [Fact p.Prime] :
    (((E p).filter (fun r => r + d ∈ E p)).card : ℝ)
      = ∑ _r ∈ (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)), (1 : ℝ) := by
  rw [E_filter_add_eq_gcd_filter p d]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp

/-! ## Step (a) + (b) + (c): `M x` as the gcd-prime triple sum -/

/-- `M x` expressed as a triple sum over primes `p`, distances `d`, and residues `r` with
`p ∣ gcd (A r) (Qval r d)`. -/
lemma M_eq_two_mul_sum_gcd_dist (x : ℕ) :
    M x = 2 * ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      ∑ d ∈ Finset.Icc 1 (p - 2),
        ∑ _r ∈ (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)),
          (1 / ((p - 1 : ℕ) : ℝ)) := by
  rw [M_eq_two_mul_sum_dist x]
  apply congrArg (fun t : ℝ => 2 * t)
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
  letI : Fact p.Prime := ⟨hp'⟩
  rw [E_add_card_eq_sum_gcd p d]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-! ## Step (d): Fubini #1 — swap `r` and `d` -/

/-- For fixed `p`, swapping the `d`- and `r`-sums in the gcd triple. The `r`-fibre ranges over
`[1, p - 1]` and the `d`-fibre over `[1, p - 1 - r]`. -/
lemma sum_dist_gcd_eq_swap (p : ℕ) (c : ℝ) :
    (∑ d ∈ Finset.Icc 1 (p - 2),
      ∑ _r ∈ (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)), c)
    = ∑ r ∈ Finset.Icc 1 (p - 1),
      ∑ _d ∈ (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d)), c := by
  refine Finset.sum_comm'
    (s := Finset.Icc 1 (p - 2))
    (t := fun d => (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)))
    (t' := Finset.Icc 1 (p - 1))
    (s' := fun r => (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d)))
    (f := fun _d _r => c) ?_
  intro d r
  constructor
  · intro h
    rcases h with ⟨hd, hr⟩
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_filter] at hr
    rcases hr with ⟨hrIcc, hg⟩
    rw [Finset.mem_Icc] at hrIcc
    rcases hd with ⟨hd1, hd2⟩
    rcases hrIcc with ⟨hr1, hr2⟩
    constructor
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hd1, by omega⟩, hg⟩
    · rw [Finset.mem_Icc]
      exact ⟨hr1, by omega⟩
  · intro h
    rcases h with ⟨hd, hr⟩
    rw [Finset.mem_filter] at hd
    rcases hd with ⟨hdIcc, hg⟩
    rw [Finset.mem_Icc] at hdIcc
    rw [Finset.mem_Icc] at hr
    rcases hdIcc with ⟨hd1, hd2⟩
    rcases hr with ⟨hr1, hr2⟩
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hd1, by omega⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hr1, by omega⟩, hg⟩

/-- The `r`-fibre `[1, p - 1 - r]` can be extended to the full range `[1, x]` (for `p ≤ x`),
with the bound `r + d < p` written as a filter condition. -/
lemma filter_Icc_pred_sub_eq_filter (p x r : ℕ) (hp : p ≤ x) :
    (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d))
      = (Finset.Icc 1 x).filter (fun d => r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d)) := by
  ext d
  constructor
  · intro hd
    rw [Finset.mem_filter] at hd
    rcases hd with ⟨hdIcc, hg⟩
    rw [Finset.mem_Icc] at hdIcc
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hdIcc.1, by omega⟩, ⟨by omega, hg⟩⟩
  · intro hd
    rw [Finset.mem_filter] at hd
    rcases hd with ⟨hdIcc, hcond⟩
    rw [Finset.mem_Icc] at hdIcc
    rcases hcond with ⟨hlt, hg⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hdIcc.1, by omega⟩, hg⟩

/-! ## Step (e): Fubini #2 — extend `r, d` to `[1, x]` and push `p` innermost -/

/-- For fixed `p ≤ x`, the swapped double sum equals the extended double sum with the
`r + d < p` condition as an `if`. -/
lemma sum_swap_gcd_eq_extend (p x : ℕ) (c : ℝ) (hp : p ≤ x) :
    (∑ r ∈ Finset.Icc 1 (p - 1),
      ∑ _d ∈ (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d)), c)
    = ∑ r ∈ Finset.Icc 1 x,
      ∑ d ∈ Finset.Icc 1 x,
        (if r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d) then c else 0) := by
  calc
    (∑ r ∈ Finset.Icc 1 (p - 1),
        ∑ _d ∈ (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d)), c)
        = ∑ r ∈ Finset.Icc 1 x,
            ∑ _d ∈ (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d)), c := by
            refine Finset.sum_subset ?_ ?_
            · intro r hr
              rw [Finset.mem_Icc] at hr ⊢
              exact ⟨hr.1, by omega⟩
            · intro r hr hnot
              rw [Finset.mem_Icc] at hr hnot
              have h1r : 1 ≤ r := hr.1
              have hnle : ¬ r ≤ p - 1 := by
                intro h
                exact hnot ⟨h1r, h⟩
              have hzero : p - 1 - r = 0 := by omega
              have hempty : Finset.Icc 1 (p - 1 - r) = ∅ := by
                rw [hzero]
                simp
              simp [hempty]
    _ = ∑ r ∈ Finset.Icc 1 x,
            ∑ d ∈ (Finset.Icc 1 x).filter (fun d => r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d)), c := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [filter_Icc_pred_sub_eq_filter p x r hp]
    _ = ∑ r ∈ Finset.Icc 1 x,
            ∑ d ∈ Finset.Icc 1 x,
              (if r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d) then c else 0) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_filter]

/-- The complete reindexing: the `(p, d, r)`-triple sum equals the `(r, d, p)`-triple sum with
`p` ranging over the primes `≤ x` satisfying `r + d < p` and `p ∣ gcd (A r) (Qval r d)`. -/
lemma mass_eq (x : ℕ) :
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      ∑ d ∈ Finset.Icc 1 (p - 2),
        ∑ _r ∈ (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)),
          (1 / ((p - 1 : ℕ) : ℝ)))
    = ∑ r ∈ Finset.Icc 1 x,
      ∑ d ∈ Finset.Icc 1 x,
        ∑ p ∈ ((Finset.Icc 2 x).filter Nat.Prime).filter
              (fun p => r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d)),
          (1 / ((p - 1 : ℕ) : ℝ)) := by
  calc
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        ∑ d ∈ Finset.Icc 1 (p - 2),
          ∑ _r ∈ (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)),
            (1 / ((p - 1 : ℕ) : ℝ)))
        = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
            ∑ r ∈ Finset.Icc 1 (p - 1),
              ∑ _d ∈ (Finset.Icc 1 (p - 1 - r)).filter (fun d => p ∣ Nat.gcd (A r) (Qval r d)),
                (1 / ((p - 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact sum_dist_gcd_eq_swap p (1 / ((p - 1 : ℕ) : ℝ))
    _ = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
            ∑ r ∈ Finset.Icc 1 x,
              ∑ d ∈ Finset.Icc 1 x,
                (if r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d) then (1 / ((p - 1 : ℕ) : ℝ)) else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hp_le : p ≤ x := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
            exact sum_swap_gcd_eq_extend p x (1 / ((p - 1 : ℕ) : ℝ)) hp_le
    _ = ∑ r ∈ Finset.Icc 1 x,
            ∑ d ∈ Finset.Icc 1 x,
              ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
                (if r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d) then (1 / ((p - 1 : ℕ) : ℝ)) else 0) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro r hr
            rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.Icc 1 x,
            ∑ d ∈ Finset.Icc 1 x,
              ∑ p ∈ ((Finset.Icc 2 x).filter Nat.Prime).filter
                    (fun p => r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d)),
                (1 / ((p - 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro d hd
            rw [← Finset.sum_filter]

/-! ## The main identity (E) -/

/-- **The gcd-prime-mass identity.** The column second moment `M x` equals twice the sum over
`r, d ∈ [1, x]` of the prime mass `Σ_{p ≤ x, r + d < p, p ∣ gcd(A_r, Q_d(r))} 1/(p - 1)`. -/
theorem M_eq_two_mul_sum_gcd_prime_mass (x : ℕ) :
    M x = 2 * (∑ r ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x,
      ∑ p ∈ ((Finset.Icc 2 x).filter Nat.Prime).filter
            (fun p => r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d)),
        (1 / ((p - 1 : ℕ) : ℝ))) := by
  calc
    M x = 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              ∑ d ∈ Finset.Icc 1 (p - 2),
                ∑ _r ∈ (Finset.Icc 1 (p - 1 - d)).filter (fun r => p ∣ Nat.gcd (A r) (Qval r d)),
                  (1 / ((p - 1 : ℕ) : ℝ))) := M_eq_two_mul_sum_gcd_dist x
    _ = 2 * (∑ r ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x,
              ∑ p ∈ ((Finset.Icc 2 x).filter Nat.Prime).filter
                    (fun p => r + d < p ∧ p ∣ Nat.gcd (A r) (Qval r d)),
                (1 / ((p - 1 : ℕ) : ℝ))) := by
        apply congrArg (fun t : ℝ => 2 * t)
        exact mass_eq x

end Erdos291
