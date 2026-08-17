import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# Erdős #291 — the finite-path holonomy `E_s` and the `s = 2` resonance

This file formalizes the rational-side core of the difference-connection analysis
(ChatGPT report 20260817-2238, sections 4-8):

    Ω_s = ∑_{j=0}^{s-1} 1/(2j+1),
    Λ_s = ∑_{j=0}^{s-1} (-1)^j/(2j+1),
    E_s = 2Λ_s - (-1)^s Ω_s.

The two proved structural facts are:

1. `E_{s+2} - E_s = (-1)^{s+1} · 4s / ((2s+1)(2s+3))`, with `E_0 = 0`,
   `E_1 = 3`, `E_2 = 0`; consequently the odd subsequence is strictly positive
   and the even subsequence is zero exactly at `s = 0, 2` and negative for
   `s ≥ 4`.  Hence over `ℚ` one has `E_s = 0 ↔ s = 0 ∨ s = 2`: among all
   rational gap values only `s = 0` (the Wieferich resonance) and `s = 2`
   (the dangerous line `p = 4r + 5`) are exact resonances.
2. The reduced transport multiplier of the `s = 2` resonance,
   `𝒯₂(T) = (T-1)(T+3)/((T+4)(T+8))`, has vanishing first logarithmic
   derivative at `T = -2` and second logarithmic derivative `-5/6` there.

Note: the resonance statements themselves live in `ZMod p` (see
`MidQuarterConsequences` for the dangerous-line equivalences); this file is the
exact-arithmetic layer used to show that `E_s` does *not* vanish rationally for
`s ≠ 0, 2`, so the other gap cases reduce to a genuine mod-`p` divisibility of a
nonzero rational numerator rather than an identity.
-/

open scoped BigOperators

namespace Erdos291

set_option linter.unusedVariables false

/-- The odd harmonic walk over `ℚ` to depth `s`: `Ω_s = ∑_{j=0}^{s-1} 1/(2j+1)`. -/
def holOmegaQ (s : ℕ) : ℚ :=
  ∑ j ∈ Finset.range s, (1 : ℚ) / ((2 * j + 1 : ℕ) : ℚ)

/-- The alternating odd harmonic sum over `ℚ` to depth `s`:
`Λ_s = ∑_{j=0}^{s-1} (-1)^j/(2j+1)`. -/
def holLambdaQ (s : ℕ) : ℚ :=
  ∑ j ∈ Finset.range s, ((-1 : ℚ) ^ j) / ((2 * j + 1 : ℕ) : ℚ)

/-- The gap holonomy `E_s = 2Λ_s - (-1)^s Ω_s` over `ℚ`. -/
def holonomyE (s : ℕ) : ℚ :=
  (2 : ℚ) * holLambdaQ s - ((-1 : ℚ) ^ s) * holOmegaQ s

/-! ## Splitting off the two new terms -/

/-- `Ω_{s+2} = Ω_s + 1/(2s+1) + 1/(2s+3)`. -/
lemma holOmegaQ_succ_succ (s : ℕ) :
    holOmegaQ (s + 2) = holOmegaQ s + (1 : ℚ) / ((2 * s + 1 : ℕ) : ℚ)
      + (1 : ℚ) / ((2 * s + 3 : ℕ) : ℚ) := by
  unfold holOmegaQ
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  ring_nf

/-- `Λ_{s+2} = Λ_s + (-1)^s/(2s+1) + (-1)^{s+1}/(2s+3)`. -/
lemma holLambdaQ_succ_succ (s : ℕ) :
    holLambdaQ (s + 2) = holLambdaQ s + ((-1 : ℚ) ^ s) / ((2 * s + 1 : ℕ) : ℚ)
      + ((-1 : ℚ) ^ (s + 1)) / ((2 * s + 3 : ℕ) : ℚ) := by
  unfold holLambdaQ
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  ring_nf

/-! ## The recurrence and base values -/

/-- The recurrence `E_{s+2} - E_s = (-1)^{s+1} · 4s / ((2s+1)(2s+3))`. -/
theorem holonomyE_succ_succ_sub (s : ℕ) :
    holonomyE (s + 2) - holonomyE s =
      ((-1 : ℚ) ^ (s + 1)) * (4 * s : ℕ) / (((2 * s + 1 : ℕ) : ℚ) * ((2 * s + 3 : ℕ) : ℚ)) := by
  unfold holonomyE
  rw [holOmegaQ_succ_succ s, holLambdaQ_succ_succ s]
  have hpos1 : (0 : ℚ) < ((2 * s + 1 : ℕ) : ℚ) := by
    exact_mod_cast (Nat.succ_pos (2 * s))
  have hpos3 : (0 : ℚ) < ((2 * s + 3 : ℕ) : ℚ) := by
    exact_mod_cast (by omega : 0 < 2 * s + 3)
  have hne1 : ((2 * s + 1 : ℕ) : ℚ) ≠ 0 := ne_of_gt hpos1
  have hne3 : ((2 * s + 3 : ℕ) : ℚ) ≠ 0 := ne_of_gt hpos3
  have hpow : (-1 : ℚ) ^ (s + 2) = (-1 : ℚ) ^ s := by
    rw [pow_add, pow_two]
    ring_nf
  have hpow' : (-1 : ℚ) ^ (s + 1) = -(-1 : ℚ) ^ s := by
    rw [pow_succ]
    ring
  have h4s : ((4 * s : ℕ) : ℚ) = ((2 * s + 1 : ℕ) : ℚ) + ((2 * s + 3 : ℕ) : ℚ) - 4 := by
    push_cast
    ring
  rw [hpow, hpow', h4s]
  field_simp [hne1, hne3]
  push_cast
  ring

@[simp] theorem holonomyE_zero : holonomyE 0 = 0 := by
  unfold holonomyE holOmegaQ holLambdaQ
  norm_num

@[simp] theorem holonomyE_one : holonomyE 1 = 3 := by
  unfold holonomyE holOmegaQ holLambdaQ
  norm_num

@[simp] theorem holonomyE_two : holonomyE 2 = 0 := by
  unfold holonomyE holOmegaQ holLambdaQ
  norm_num

/-! ## Sign structure of the two subsequences -/

/-- The odd subsequence `E_{2k+1}` is strictly increasing from `E_1 = 3`, so it is
positive. -/
theorem holonomyE_odd_pos {s : ℕ} (hs : Odd s) : 0 < holonomyE s := by
  rcases hs with ⟨k, hk⟩
  subst s
  induction k with
  | zero =>
      norm_num [holonomyE_one]
  | succ k ih =>
      have hstep := holonomyE_succ_succ_sub (2 * k + 1)
      have hstep' : holonomyE (2 * (k + 1) + 1) - holonomyE (2 * k + 1) =
          ((-1 : ℚ) ^ (2 * k + 1 + 1)) * (4 * (2 * k + 1) : ℕ) /
            (((2 * (2 * k + 1) + 1 : ℕ) : ℚ) * ((2 * (2 * k + 1) + 3 : ℕ) : ℚ)) := by
        simpa [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega] using hstep
      have hpow : (-1 : ℚ) ^ (2 * k + 1 + 1) = 1 := by
        have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
        exact heven.neg_one_pow
      have hdiff : 0 < holonomyE (2 * (k + 1) + 1) - holonomyE (2 * k + 1) := by
        rw [hstep']
        rw [hpow]
        positivity
      nlinarith

/-- The even subsequence after `E_2 = 0` is strictly decreasing, hence negative
for `k ≥ 2`. -/
theorem holonomyE_even_neg_of_two_le_k {k : ℕ} (hk2 : 2 ≤ k) : holonomyE (k + k) < 0 := by
  let n : ℕ := k - 2
  have hk_eq : k = n + 2 := by dsimp [n]; omega
  rw [hk_eq]
  clear hk_eq
  induction n with
  | zero =>
      change holonomyE 4 < 0
      have hstep := holonomyE_succ_succ_sub 2
      have hodd : Odd (2 + 1) := ⟨1, by omega⟩
      have hpow : (-1 : ℚ) ^ (2 + 1) = -1 := hodd.neg_one_pow
      rw [hpow] at hstep
      have hstep' : holonomyE 4 - holonomyE 2 = (-1 : ℚ) * (8 : ℚ) / ((5 : ℚ) * (7 : ℚ)) := by
        simpa using hstep
      rw [holonomyE_two, sub_zero] at hstep'
      norm_num at hstep'
      linarith
  | succ n ih =>
      have htarget : ((n + 1) + 2) + ((n + 1) + 2) = 4 + 2 * n + 2 := by omega
      have hstep := holonomyE_succ_succ_sub (4 + 2 * n)
      have hodd : Odd (4 + 2 * n + 1) := ⟨n + 2, by omega⟩
      have hpow : (-1 : ℚ) ^ (4 + 2 * n + 1) = -1 := hodd.neg_one_pow
      have hstep' : holonomyE (4 + 2 * n + 2) - holonomyE (4 + 2 * n) =
          ((-1 : ℚ) ^ (4 + 2 * n + 1)) * (4 * (4 + 2 * n) : ℕ) /
            (((2 * (4 + 2 * n) + 1 : ℕ) : ℚ) * ((2 * (4 + 2 * n) + 3 : ℕ) : ℚ)) := by
        simpa using hstep
      have hdiff : holonomyE (4 + 2 * n + 2) - holonomyE (4 + 2 * n) < 0 := by
        rw [hstep', hpow]
        have hnum : 0 < ((4 * (4 + 2 * n) : ℕ) : ℚ) := by positivity
        have hden : 0 < ((2 * (4 + 2 * n) + 1 : ℕ) : ℚ) *
            ((2 * (4 + 2 * n) + 3 : ℕ) : ℚ) := by positivity
        rw [neg_mul, one_mul]
        exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden
      have ih' : holonomyE (4 + 2 * n) < 0 := by
        simpa [show n + 2 + (n + 2) = 4 + 2 * n by omega] using ih
      have hnext : holonomyE (4 + 2 * n + 2) < 0 := by
        nlinarith [ih', hdiff]
      rw [htarget]
      exact hnext

/-- The main exact-resonance theorem: over `ℚ`, `E_s = 0` iff `s = 0` or `s = 2`. -/
theorem holonomyE_eq_zero_iff (s : ℕ) : holonomyE s = 0 ↔ s = 0 ∨ s = 2 := by
  constructor
  · intro hs
    rcases Nat.even_or_odd s with hs_e | hs_o
    · rcases hs_e with ⟨k, hk⟩
      subst s
      by_cases hk0 : k = 0
      · subst k
        simp
      by_cases hk1 : k = 1
      · subst k
        simp
      · exfalso
        have hk2 : 2 ≤ k := by omega
        have h2k : 2 ≤ k + k := by omega
        have hneg : holonomyE (k + k) < 0 :=
          holonomyE_even_neg_of_two_le_k hk2
        linarith
    · have hpos := holonomyE_odd_pos hs_o
      exact False.elim ((ne_of_gt hpos) hs)
  · intro h
    rcases h with rfl | rfl
    · simp
    · simp

/-! ## The `s = 2` reduced transport multiplier -/

/-- The first logarithmic derivative of the reduced `s = 2` transport
`𝒯₂(T) = (T-1)(T+3)/((T+4)(T+8))` at `T = -2`:
`1/(T-1) + 1/(T+3) - 1/(T+4) - 1/(T+8)`. -/
def holonomyOneQ : ℚ :=
  (1 : ℚ) / ((-3 : ℚ)) + 1 - (1 : ℚ) / 2 - (1 : ℚ) / 6

/-- The second logarithmic derivative of the reduced `s = 2` transport at
`T = -2`: `-1/(T-1)² - 1/(T+3)² + 1/(T+4)² + 1/(T+8)²`. -/
def holonomyTwoQ : ℚ :=
  -((1 : ℚ) / 9) - 1 + (1 : ℚ) / 4 + (1 : ℚ) / 36

/-- The `s = 2` resonance is exactly first-order: the first holonomy vanishes. -/
theorem holonomyOneQ_eq_zero : holonomyOneQ = 0 := by
  unfold holonomyOneQ
  norm_num

/-- The second-order obstruction of the `s = 2` resonance is the nonzero constant
`-5/6`: any mechanism forcing a second-order match would contradict every prime
`p ≠ 5`. -/
theorem holonomyTwoQ_eq_neg_five_sixths : holonomyTwoQ = -(5 : ℚ) / 6 := by
  unfold holonomyTwoQ
  norm_num

end Erdos291
