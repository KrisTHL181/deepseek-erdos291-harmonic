import Erdos291.MidConjectures
import Erdos291.MidRoots
import Erdos291.MidResultant
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Erdős #291 — attack line 1: the symmetric-difference reduction for CR

Assume an intrinsic MID pair `(p, r)` (`4r + 1 < p`, `r ∈ E p`) and a candidate
common-root index `β ∈ [1, 2r] \ {r}`, i.e.

    `H_β = H_{β+r}` and `H_β = H_{2r-β}` in `ZMod p`.                      [CR]

This file extracts the *symmetric difference* of the two zero-sum intervals
behind [CR].  It is an interval `[a, b]` with `a + b = 3r + 1` (unless
`2β = r`, in which case the two equations coincide and the interval degenerates
to the single equation `H_{r/2} = H_{3r/2}`).  The resulting zero-sum interval
has a built-in pairing `i ↦ (3r+1) - i`, so the obstruction is a short
reciprocal sum whose denominators all lie below `p`.

We also prove the first two nontrivial exclusions coming from the pairing:

* length `1`: the interval is a single point, so its sum is `1/a`, impossible;
* length `2`: the interval is `[a, a+1]`, so its sum is
  `(2a+1)/(a(a+1)) = (3r+1)/(a(a+1))`, impossible because `3r+1 < p`.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The left endpoint of the symmetric-difference interval associated with a CR candidate `β`. -/
def crSymmLeft (r β : ℕ) : ℕ :=
  if 2 * β < r then β + r + 1 else 2 * r - β + 1

/-- The right endpoint of the symmetric-difference interval associated with a CR candidate `β`. -/
def crSymmRight (r β : ℕ) : ℕ :=
  if 2 * β < r then 2 * r - β else β + r

/-! ## Basic endpoint algebra -/

/-- For `2β ≠ r` the symmetric-difference interval is nonempty. -/
lemma crSymmLeft_le_right (r β : ℕ) (hne : 2 * β ≠ r) (hβ2 : β ≤ 2 * r) :
    crSymmLeft r β ≤ crSymmRight r β := by
  unfold crSymmLeft crSymmRight
  by_cases h : 2 * β < r
  · rw [if_pos h, if_pos h]
    omega
  · have hr : r < 2 * β := by omega
    rw [if_neg h, if_neg h]
    omega

/-- The two endpoints sum to `3r + 1` (the pairing constant). -/
lemma crSymmLeft_add_right (r β : ℕ) (hne : 2 * β ≠ r) (hβ2 : β ≤ 2 * r) :
    crSymmLeft r β + crSymmRight r β = 3 * r + 1 := by
  unfold crSymmLeft crSymmRight
  by_cases h : 2 * β < r
  · rw [if_pos h, if_pos h]
    omega
  · rw [if_neg h, if_neg h]
    omega

/-- The left endpoint is at least `1`. -/
lemma one_le_crSymmLeft (r β : ℕ) (hβ2 : β ≤ 2 * r) : 1 ≤ crSymmLeft r β := by
  unfold crSymmLeft
  by_cases h : 2 * β < r
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The right endpoint is at most `3r`. -/
lemma crSymmRight_le_three_mul_r (r β : ℕ) (hβ2 : β ≤ 2 * r) :
    crSymmRight r β ≤ 3 * r := by
  unfold crSymmRight
  by_cases h : 2 * β < r
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- For `2β ≠ r`, the interval length is positive. -/
lemma crSymmInterval_nonempty (r β : ℕ) (hne : 2 * β ≠ r) (hβ2 : β ≤ 2 * r) :
    (Finset.Icc (crSymmLeft r β) (crSymmRight r β)).Nonempty := by
  rw [Finset.nonempty_Icc]
  exact crSymmLeft_le_right r β hne hβ2

/-- All indices in the symmetric-difference interval are below `p` in the intrinsic regime. -/
lemma crSymmRight_lt_p (p r β : ℕ) (hmid : 4 * r + 1 < p) (hβ2 : β ≤ 2 * r) :
    crSymmRight r β < p := by
  have hle := crSymmRight_le_three_mul_r r β hβ2
  have h3r : 3 * r < p := by omega
  omega

/-- The pairing constant `3r + 1` is nonzero and below `p` in the intrinsic regime. -/
lemma three_mul_r_add_one_lt_p (p r : ℕ) (hmid : 4 * r + 1 < p) :
    3 * r + 1 < p := by
  omega

/-! ## The symmetric-difference interval sum vanishes -/

/-- [CR] forces the reciprocal sum over the symmetric-difference interval to vanish.
This is the key reduction of attack line 1. -/
lemma crSymm_sum_eq_zero_of_CR (p r β : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2 * r) (hne : 2 * β ≠ r)
    (hEq1 : harmonicSum p β = harmonicSum p (β + r))
    (hEq2 : harmonicSum p β = harmonicSum p (2 * r - β)) :
    (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmRight r β), ((i : ZMod p)⁻¹)) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have hβr : β + r < p := by omega
  have h2rβ : 2 * r - β < p := by omega
  by_cases h : 2 * β < r
  · -- interval is [β+r+1, 2r-β] = I2 \ I1
    have hleft : crSymmLeft r β = β + r + 1 := by
      simp [crSymmLeft, h]
    have hright : crSymmRight r β = 2 * r - β := by
      simp [crSymmRight, h]
    have hfirst : 2 * r - β = β + r + (r - 2 * β) := by omega
    have hlen_lt : β + r + (r - 2 * β) < p := by
      simpa [hfirst] using h2rβ
    have hsum_sub := harmonicSum_sub_eq_sum_inv_Icc p (β + r) (r - 2 * β) hlen_lt
    have hEq12 : harmonicSum p (β + r) = harmonicSum p (2 * r - β) := by
      rw [← hEq1, ← hEq2]
    have hdiff : harmonicSum p (2 * r - β) - harmonicSum p (β + r) = 0 := by
      rw [hEq12]
      simp
    calc
      (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmRight r β), ((i : ZMod p)⁻¹))
          = ∑ i ∈ Finset.Icc (β + r + 1) (2 * r - β), ((i : ZMod p)⁻¹) := by
              rw [hleft, hright]
      _ = harmonicSum p (2 * r - β) - harmonicSum p (β + r) := by
              rw [hfirst]
              rw [← harmonicSum_sub_eq_sum_inv_Icc p (β + r) (r - 2 * β) hlen_lt]
      _ = 0 := hdiff
  · -- r < 2β, interval is [2r-β+1, β+r] (the symmetric difference on the right)
    have hgt : r < 2 * β := by omega
    have hleft : crSymmLeft r β = 2 * r - β + 1 := by
      simp [crSymmLeft, h]
    have hright : crSymmRight r β = β + r := by
      simp [crSymmRight, h]
    have hfirst : β + r = 2 * r - β + (2 * β - r) := by omega
    have hlen_lt : 2 * r - β + (2 * β - r) < p := by
      simpa [hfirst] using hβr
    have hsum_sub := harmonicSum_sub_eq_sum_inv_Icc p (2 * r - β) (2 * β - r) hlen_lt
    have hEq12 : harmonicSum p (2 * r - β) = harmonicSum p (β + r) := by
      rw [← hEq2, hEq1]
    have hdiff : harmonicSum p (β + r) - harmonicSum p (2 * r - β) = 0 := by
      rw [hEq12]
      simp
    calc
      (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmRight r β), ((i : ZMod p)⁻¹))
          = ∑ i ∈ Finset.Icc (2 * r - β + 1) (β + r), ((i : ZMod p)⁻¹) := by
              rw [hleft, hright]
      _ = harmonicSum p (β + r) - harmonicSum p (2 * r - β) := by
              rw [hfirst]
              rw [← harmonicSum_sub_eq_sum_inv_Icc p (2 * r - β) (2 * β - r) hlen_lt]
      _ = 0 := hdiff

/-- When `2β = r` the two CR equations coincide: both say `H_β = H_{3β}`.
This is the exact remaining case after the symmetric-difference reduction. -/
lemma CR_iff_of_two_mul_beta_eq_r (p r β : ℕ)
    (h : 2 * β = r) :
    (harmonicSum p β = harmonicSum p (β + r) ∧
      harmonicSum p β = harmonicSum p (2 * r - β)) ↔
      harmonicSum p β = harmonicSum p (3 * β) := by
  have hβr : β + r = 3 * β := by omega
  have h2rβ : 2 * r - β = 3 * β := by omega
  constructor
  · intro hCR
    rw [hβr] at hCR
    exact hCR.1
  · intro hβ
    rw [hβr, h2rβ]
    exact ⟨hβ, hβ⟩

/-! ## Exclusions from interval length one and two -/

/-- If the symmetric-difference interval has length one, its sum is a single unit inverse,
so it cannot vanish.  This excludes `β = (r±1)/2` (r odd). -/
lemma not_crSymm_sum_eq_zero_of_length_one (p r β : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) (hβ2 : β ≤ 2 * r) (hne : 2 * β ≠ r)
    (hL : crSymmLeft r β = crSymmRight r β)
    (hsum : (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmRight r β),
        ((i : ZMod p)⁻¹)) = 0) : False := by
  have hp : Nat.Prime p := Fact.out
  have hleft_pos : 1 ≤ crSymmLeft r β := one_le_crSymmLeft r β hβ2
  have hadd := crSymmLeft_add_right r β hne hβ2
  have h2left : 2 * crSymmLeft r β = 3 * r + 1 := by omega
  have hleft_lt : crSymmLeft r β < p := by
    have h3 : 3 * r + 1 < p := three_mul_r_add_one_lt_p p r hmid
    omega
  have hleft_ne : (crSymmLeft r β : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ crSymmLeft r β := (ZMod.natCast_eq_zero_iff (crSymmLeft r β) p).mp hz
    exact (not_lt_of_ge (Nat.le_of_dvd hleft_pos hdvd)) hleft_lt
  have hsum_single : ((crSymmLeft r β : ℕ) : ZMod p)⁻¹ = 0 := by
    have hIcc : Finset.Icc (crSymmLeft r β) (crSymmRight r β) =
        Finset.Icc (crSymmLeft r β) (crSymmLeft r β) := by
      rw [hL]
    have hsum' := hsum
    rw [hIcc] at hsum'
    have hsingle : (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmLeft r β),
        ((i : ZMod p)⁻¹)) = ((crSymmLeft r β : ℕ) : ZMod p)⁻¹ := by
      simp
    rw [hsingle] at hsum'
    exact hsum'
  have hprod := congrArg (fun t : ZMod p => (crSymmLeft r β : ZMod p) * t) hsum_single
  have hprod' : (crSymmLeft r β : ZMod p) * ((crSymmLeft r β : ℕ) : ZMod p)⁻¹ = 1 :=
    mul_inv_cancel₀ hleft_ne
  rw [hprod', mul_zero] at hprod
  exact one_ne_zero hprod

/-- If the symmetric-difference interval has length two, its sum is
`(3r+1)/(a(a+1))`; since `a, a+1` are units and `3r+1 < p`, it cannot vanish.
This excludes `β = r/2 ± 1` (r even). -/
lemma not_crSymm_sum_eq_zero_of_length_two (p r β : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) (hβ2 : β ≤ 2 * r) (hne : 2 * β ≠ r)
    (hL : crSymmLeft r β + 1 = crSymmRight r β)
    (hsum : (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmRight r β),
        ((i : ZMod p)⁻¹)) = 0) : False := by
  have hp : Nat.Prime p := Fact.out
  have hleft_pos : 1 ≤ crSymmLeft r β := one_le_crSymmLeft r β hβ2
  have hadd := crSymmLeft_add_right r β hne hβ2
  have h2left : 2 * crSymmLeft r β = 3 * r := by omega
  have hleft_lt : crSymmLeft r β < p := by
    have h3 : 3 * r < p := by omega
    omega
  have hleft1_lt : crSymmLeft r β + 1 < p := by
    have h3 : 3 * r + 2 < p := by omega
    omega
  have hleft_ne : (crSymmLeft r β : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ crSymmLeft r β := (ZMod.natCast_eq_zero_iff (crSymmLeft r β) p).mp hz
    exact (not_lt_of_ge (Nat.le_of_dvd hleft_pos hdvd)) hleft_lt
  have hleft1_ne : ((crSymmLeft r β + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ crSymmLeft r β + 1 :=
      (ZMod.natCast_eq_zero_iff (crSymmLeft r β + 1) p).mp hz
    have hpos : 1 ≤ crSymmLeft r β + 1 := by omega
    exact (not_lt_of_ge (Nat.le_of_dvd hpos hdvd)) hleft1_lt
  have hsum_two : ((crSymmLeft r β : ℕ) : ZMod p)⁻¹ +
      ((crSymmLeft r β + 1 : ℕ) : ZMod p)⁻¹ = 0 := by
    have hIcc : Finset.Icc (crSymmLeft r β) (crSymmRight r β) =
        Finset.Icc (crSymmLeft r β) (crSymmLeft r β + 1) := by
      rw [hL]
    have hsum' := hsum
    rw [hIcc] at hsum'
    have hsingle : (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmLeft r β + 1),
        ((i : ZMod p)⁻¹)) = ((crSymmLeft r β : ℕ) : ZMod p)⁻¹ +
          ((crSymmLeft r β + 1 : ℕ) : ZMod p)⁻¹ := by
      rw [Finset.sum_Icc_succ_top (a := crSymmLeft r β) (b := crSymmLeft r β) (by omega)]
      simp
    rw [hsingle] at hsum'
    exact hsum'
  have hcross := congrArg
    (fun t : ZMod p => (crSymmLeft r β : ZMod p) * ((crSymmLeft r β + 1 : ℕ) : ZMod p) * t)
    hsum_two
  have hcross_exp : (crSymmLeft r β : ZMod p) * ((crSymmLeft r β + 1 : ℕ) : ZMod p) *
        (((crSymmLeft r β : ℕ) : ZMod p)⁻¹ + ((crSymmLeft r β + 1 : ℕ) : ZMod p)⁻¹)
        = ((crSymmLeft r β + 1 : ℕ) : ZMod p) + (crSymmLeft r β : ZMod p) := by
    rw [mul_add]
    have h1 : (crSymmLeft r β : ZMod p) * ((crSymmLeft r β + 1 : ℕ) : ZMod p) *
        ((crSymmLeft r β : ℕ) : ZMod p)⁻¹ = ((crSymmLeft r β + 1 : ℕ) : ZMod p) := by
      rw [mul_assoc, mul_comm (((crSymmLeft r β + 1 : ℕ) : ZMod p))
        (((crSymmLeft r β : ℕ) : ZMod p)⁻¹), ← mul_assoc]
      rw [mul_inv_cancel₀ hleft_ne, one_mul]
    have h2 : (crSymmLeft r β : ZMod p) * ((crSymmLeft r β + 1 : ℕ) : ZMod p) *
        ((crSymmLeft r β + 1 : ℕ) : ZMod p)⁻¹ = (crSymmLeft r β : ZMod p) := by
      rw [mul_assoc]
      rw [mul_inv_cancel₀ hleft1_ne, mul_one]
    rw [h1, h2]
  have hcross_zero : (crSymmLeft r β : ZMod p) * ((crSymmLeft r β + 1 : ℕ) : ZMod p) *
        (((crSymmLeft r β : ℕ) : ZMod p)⁻¹ + ((crSymmLeft r β + 1 : ℕ) : ZMod p)⁻¹) = 0 := by
    rw [hsum_two]
    simp
  have hsum_cast : ((crSymmLeft r β + 1 : ℕ) : ZMod p) + (crSymmLeft r β : ZMod p) = 0 := by
    rw [← hcross_exp, hcross_zero]
  have hsum_cast' : ((2 * crSymmLeft r β + 1 : ℕ) : ZMod p) = 0 := by
    have hcast : ((2 * crSymmLeft r β + 1 : ℕ) : ZMod p) =
        ((crSymmLeft r β + 1 : ℕ) : ZMod p) + (crSymmLeft r β : ZMod p) := by
      rw [show (2 * crSymmLeft r β + 1 : ℕ) = (crSymmLeft r β + 1) + crSymmLeft r β by omega]
      norm_num [Nat.cast_add]
    rw [hcast, hsum_cast]
  have h3r : ((3 * r + 1 : ℕ) : ZMod p) = 0 := by
    rw [show 3 * r + 1 = 2 * crSymmLeft r β + 1 by omega]
    exact hsum_cast'
  have hpdvd : p ∣ 3 * r + 1 := (ZMod.natCast_eq_zero_iff (3 * r + 1) p).mp h3r
  have hpos : 1 ≤ 3 * r + 1 := by omega
  have hlt : 3 * r + 1 < p := three_mul_r_add_one_lt_p p r hmid
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hpdvd)) hlt

/-! ## Combined exclusions -/

/-- If the symmetric-difference interval has length one, [CR] is impossible.
This excludes `β = (r±1)/2` when `r` is odd. -/
lemma not_CR_of_length_one (p r β : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2 * r) (hne : 2 * β ≠ r)
    (hL : crSymmLeft r β = crSymmRight r β)
    (hEq1 : harmonicSum p β = harmonicSum p (β + r))
    (hEq2 : harmonicSum p β = harmonicSum p (2 * r - β)) : False := by
  exact not_crSymm_sum_eq_zero_of_length_one p r β hmid hβ2 hne hL
    (crSymm_sum_eq_zero_of_CR p r β hmid hβ1 hβ2 hne hEq1 hEq2)

/-- If the symmetric-difference interval has length two, [CR] is impossible.
This excludes `β = r/2 ± 1` when `r` is even. -/
lemma not_CR_of_length_two (p r β : ℕ) [Fact p.Prime]
    (hmid : 4 * r + 1 < p) (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2 * r) (hne : 2 * β ≠ r)
    (hL : crSymmLeft r β + 1 = crSymmRight r β)
    (hEq1 : harmonicSum p β = harmonicSum p (β + r))
    (hEq2 : harmonicSum p β = harmonicSum p (2 * r - β)) : False := by
  exact not_crSymm_sum_eq_zero_of_length_two p r β hmid hβ2 hne hL
    (crSymm_sum_eq_zero_of_CR p r β hmid hβ1 hβ2 hne hEq1 hEq2)

/-! ## Proposition-level reduction -/

/-- Hypothesis A': for every intrinsic MID pair and every candidate `β`, the
symmetric-difference interval has length at least `3` or its reciprocal sum is
nonzero. -/
def HA_mid_crSymm_sum_ne_zero : Prop :=
  ∀ p r β : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    1 ≤ β → β ≤ 2 * r → β ≠ r → 2 * β ≠ r →
    crSymmLeft r β + 1 < crSymmRight r β →
    (∑ i ∈ Finset.Icc (crSymmLeft r β) (crSymmRight r β), ((i : ZMod p)⁻¹)) ≠ 0

/-- Hypothesis for the degenerate `2β = r` case: when `r` is even,
`H_{r/2} ≠ H_{3r/2}`. -/
def HA_mid_harmonicSum_half_ne_three_half : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → Even r →
    harmonicSum p (r / 2) ≠ harmonicSum p (3 * (r / 2))

/-- The symmetric-difference hypothesis plus the half/three-half hypothesis
together imply the full CR-free statement. -/
theorem HA_mid_CR_free_of_crSymm_sum_ne_zero_and_half
    (hR1 : HA_mid_crSymm_sum_ne_zero) (hR2 : HA_mid_harmonicSum_half_ne_three_half) :
    HA_mid_CR_free := by
  intro p r hp hmid hrE β hβ1 hβ2 hβne hEq1 hEq2
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hβ1eq : β = 1
  · subst β
    exact not_CR_beta_eq_one p r hrE hmid hEq1
  have hβne1 : β ≠ 1 := hβ1eq
  by_cases hβrsub : β = r - 1
  · subst β
    have hEq2' : harmonicSum p (r - 1) = harmonicSum p (r + 1) := by
      simpa [show 2 * r - (r - 1) = r + 1 by omega] using hEq2
    exact not_CR_beta_r_sub_one p r hrE hmid hEq2'
  have hβner_sub : β ≠ r - 1 := hβrsub
  by_cases hβradd : β = r + 1
  · subst β
    have hEq2' : harmonicSum p (r - 1) = harmonicSum p (r + 1) := by
      have h' : harmonicSum p (r + 1) = harmonicSum p (r - 1) := by
        simpa [show 2 * r - (r + 1) = r - 1 by omega] using hEq2
      exact h'.symm
    exact not_CR_beta_r_add_one p r hrE hmid hEq2'
  have hβne_radd : β ≠ r + 1 := hβradd
  by_cases h2βr : 2 * β = r
  · have hβeq : β = r / 2 := by omega
    have hr_even : Even r := by
      rw [← h2βr]
      exact even_two_mul β
    have hCR' : harmonicSum p β = harmonicSum p (3 * β) :=
      (CR_iff_of_two_mul_beta_eq_r p r β h2βr).mp ⟨hEq1, hEq2⟩
    have hne := hR2 p r hp hmid hrE hr_even
    exact hne (by simpa [hβeq] using hCR')
  have h2βne : 2 * β ≠ r := h2βr
  have hsum0 := crSymm_sum_eq_zero_of_CR p r β hmid hβ1 hβ2 h2βne hEq1 hEq2
  by_cases hlen1 : crSymmLeft r β = crSymmRight r β
  · exact not_CR_of_length_one p r β hmid hβ1 hβ2 h2βne hlen1 hEq1 hEq2
  have hlen1ne : crSymmLeft r β ≠ crSymmRight r β := hlen1
  by_cases hlen2 : crSymmLeft r β + 1 = crSymmRight r β
  · exact not_CR_of_length_two p r β hmid hβ1 hβ2 h2βne hlen2 hEq1 hEq2
  have hle := crSymmLeft_le_right r β h2βne hβ2
  have hlt : crSymmLeft r β + 1 < crSymmRight r β := by omega
  exact (hR1 p r β hp hmid hrE hβ1 hβ2 hβne h2βne hlt) hsum0

end

end Erdos291
