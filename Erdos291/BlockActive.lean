import Erdos291.BlockEstimateToGoal
import Erdos291.BlockMid
import Erdos291.BadDensity
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The active prime mass and a constant bound for `W`

Cloud data (full `Wmid`, no `x` truncation) shows that `Wmid R x` stabilizes near
`0.03–0.04`, far below the threshold `log 2 / 8 ≈ 0.08664` used by
`xP_tendsto_atTop_of_block_bound`.  The right target is therefore a *constant*
upper bound for `W`, not the (too strong) vanishing `W → 0`.

This file sets up the intermediate quantity

  `activeMass R x = Σ_{p ≤ x prime, E p ∩ [R, 2R) ≠ ∅} 1/(p-1)`

and proves the reduction

  `Wmid R x ≤ 2 * activeMass R x + R * exceptionalMassAboveR R x`,

where `exceptionalMassAboveR R x` sums `1/(p-1)` over primes `p > R` dividing
the fixed exceptional integer `Nall R`.  The primes `p ≤ R` are deliberately
excluded: for them `E p ⊆ [1, p-1]` cannot meet `[R, 2R)`, so they carry no
`Wmid` contribution and must not enter the exceptional term with the `R`
amplification.  The non-exceptional primes have at most two bad digits in
`[R, 2R)`, by the no-three-bad-digits-of-span-`R` lemma.  Under the natural
hypotheses

  * `activeMass R x ≤ C` with `C < log 2 / 16`, and
  * `R * exceptionalMassAboveR R x → 0` uniformly in `x`,

the combined middle bound is eventually `≤ 2C + ε < log 2 / 8`, and together
with the already-proved uniform tail decay `Wtail ≤ Ctail / log R` this yields
the block bound required by `xP_tendsto_atTop_of_block_bound`.
-/

open Filter
open scoped BigOperators

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The reciprocal weight `1/(p-1)` of a prime `p`. -/
noncomputable abbrev primeWeight (p : ℕ) : ℝ :=
  1 / ((p - 1 : ℕ) : ℝ)

/-- The active prime mass of the dyadic block `[R, 2R)`: the sum of `1/(p-1)`
over primes `p ≤ x` for which `E p` meets `[R, 2R)`. -/
noncomputable def activeMass (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
    if (E p ∩ Finset.Ico R (2 * R)).Nonempty then
      primeWeight p
    else 0

/-- The exceptional prime mass above `R`: the sum of `1/(p-1)` over primes
`R < p ≤ x` dividing the fixed exceptional integer `Nall R`.  Primes `p ≤ R`
are omitted because `E p ⊆ [1, p-1]` never meets `[R, 2R)`. -/
noncomputable def exceptionalMassAboveR (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter (fun p => R < p ∧ Nat.Prime p ∧ p ∣ Nall R),
    primeWeight p

/-- `activeMass` is nonnegative. -/
lemma activeMass_nonneg (R x : ℕ) : 0 ≤ activeMass R x := by
  unfold activeMass
  exact Finset.sum_nonneg (by
    intro p hp
    by_cases h : (E p ∩ Finset.Ico R (2 * R)).Nonempty
    · simp [h, primeWeight]
    · simp [h])

/-- `exceptionalMassAboveR` is nonnegative. -/
lemma exceptionalMassAboveR_nonneg (R x : ℕ) : 0 ≤ exceptionalMassAboveR R x := by
  unfold exceptionalMassAboveR
  exact Finset.sum_nonneg (by
    intro p hp
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _))

/-- The tail contribution `Wtail R x` is nonnegative. -/
lemma Wtail_nonneg (R x : ℕ) : 0 ≤ Wtail R x := by
  unfold Wtail
  exact Finset.sum_nonneg (by
    intro r hr
    exact Finset.sum_nonneg (by
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)))

/-- Since `W = Wtail + Wmid` and `Wtail ≥ 0`, the middle part is at most `W`. -/
lemma Wmid_le_W (R x : ℕ) : Wmid R x ≤ W R x := by
  have h := W_eq_Wtail_add_Wmid R x
  have hn : 0 ≤ Wtail R x := Wtail_nonneg R x
  linarith

/-- `W` is controlled by the sum over primes of `|E p ∩ [R, 2R)| / (p-1)`. -/
lemma W_le_sum_E_card_weight (R x : ℕ) :
    W R x ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  unfold W
  refine Finset.sum_le_sum ?_
  intro p hp
  let S : Finset ℕ := (T p).filter (fun r => R ≤ r ∧ r < 2 * R)
  have hsub : S ⊆ E p ∩ Finset.Ico R (2 * R) := by
    intro r hr
    have hrF := Finset.mem_filter.mp hr
    have hrT : r ∈ T p := hrF.1
    have hrE : r ∈ E p := (Finset.mem_filter.mp hrT).1
    have hrIco : r ∈ Finset.Ico R (2 * R) := Finset.mem_Ico.mpr hrF.2
    exact Finset.mem_inter.mpr ⟨hrE, hrIco⟩
  have hcard_le : S.card ≤ (E p ∩ Finset.Ico R (2 * R)).card :=
    Finset.card_le_card hsub
  have hw : 0 ≤ primeWeight p := by
    dsimp [primeWeight]
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  have hcardR : (S.card : ℝ) ≤ ((E p ∩ Finset.Ico R (2 * R)).card : ℝ) := by
    exact_mod_cast hcard_le
  have hsum := Finset.sum_le_card_nsmul S (fun _ => primeWeight p) (primeWeight p)
    (by intro r hr; rfl)
  calc
    (∑ r ∈ S, primeWeight p) ≤ S.card • primeWeight p := hsum
    _ = (S.card : ℝ) * primeWeight p := by rw [nsmul_eq_mul]
    _ ≤ ((E p ∩ Finset.Ico R (2 * R)).card : ℝ) * primeWeight p := by
      exact mul_le_mul_of_nonneg_right hcardR hw
    _ = (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
      dsimp [primeWeight]
      rw [mul_one_div]

/-- For a prime `p` not dividing `Nall R`, the bad set meets the dyadic block
`[R, 2R)` in at most two elements: any three elements have span `< R`, which is
forbidden by the no-three-bad-digits lemma with `D = R`. -/
lemma E_inter_card_le_two_of_not_dvd_Nall (p R : ℕ) (hp : Nat.Prime p)
    (h : ¬ p ∣ Nall R) :
    (E p ∩ Finset.Ico R (2 * R)).card ≤ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_contra hnot
  have hgt : 2 < (E p ∩ Finset.Ico R (2 * R)).card := by omega
  rcases Finset.two_lt_card.mp hgt with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have haS : a ∈ E p := (Finset.mem_inter.mp ha).1
  have hbS : b ∈ E p := (Finset.mem_inter.mp hb).1
  have hcS : c ∈ E p := (Finset.mem_inter.mp hc).1
  have haI := Finset.mem_Ico.mp (Finset.mem_inter.mp ha).2
  have hbI := Finset.mem_Ico.mp (Finset.mem_inter.mp hb).2
  have hcI := Finset.mem_Ico.mp (Finset.mem_inter.mp hc).2
  have hord : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨ (b < a ∧ a < c) ∨
      (b < c ∧ c < a) ∨ (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by omega
  rcases hord with h1 | h2 | h3 | h4 | h5 | h6
  · have hspan : c - a ≤ R := by omega
    exact (no_triple_of_not_dvd_Nall p R h) haS hbS hcS h1.1 h1.2 hspan
  · have hspan : b - a ≤ R := by omega
    exact (no_triple_of_not_dvd_Nall p R h) haS hcS hbS h2.1 h2.2 hspan
  · have hspan : c - b ≤ R := by omega
    exact (no_triple_of_not_dvd_Nall p R h) hbS haS hcS h3.1 h3.2 hspan
  · have hspan : a - b ≤ R := by omega
    exact (no_triple_of_not_dvd_Nall p R h) hbS hcS haS h4.1 h4.2 hspan
  · have hspan : b - c ≤ R := by omega
    exact (no_triple_of_not_dvd_Nall p R h) hcS haS hbS h5.1 h5.2 hspan
  · have hspan : a - c ≤ R := by omega
    exact (no_triple_of_not_dvd_Nall p R h) hcS hbS haS h6.1 h6.2 hspan

/-- Per-prime comparison: the contribution `|E p ∩ [R, 2R)| / (p-1)` is at most
the active contribution `2/(p-1)` for non-exceptional primes, plus the
exceptional contribution `R/(p-1)` when `R < p` and `p ∣ Nall R`. -/
private lemma E_card_mul_weight_le (R p : ℕ) (hp : Nat.Prime p) :
    (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * primeWeight p
      ≤ (if (E p ∩ Finset.Ico R (2 * R)).Nonempty then 2 * primeWeight p else 0)
        + (R : ℝ) * (if R < p ∧ p ∣ Nall R then primeWeight p else 0) := by
  have hw : 0 ≤ primeWeight p := by
    dsimp [primeWeight]
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  have hw' : 0 ≤ ((p - 1 : ℕ) : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcardR : (E p ∩ Finset.Ico R (2 * R)).card ≤ R := by
    have hsub : E p ∩ Finset.Ico R (2 * R) ⊆ Finset.Ico R (2 * R) :=
      Finset.inter_subset_right
    have hle := Finset.card_le_card hsub
    have hcard : (Finset.Ico R (2 * R)).card = R := by
      simp
      omega
    rwa [hcard] at hle
  by_cases hdvd : p ∣ Nall R
  · by_cases hRlt : R < p
    · by_cases hnon : (E p ∩ Finset.Ico R (2 * R)).Nonempty
      · simp [hnon, hRlt, hdvd]
        have hcardR' : (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) ≤ (R : ℝ) := by
          exact_mod_cast hcardR
        have hle' : (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) *
              ((p - 1 : ℕ) : ℝ)⁻¹ ≤ (R : ℝ) * ((p - 1 : ℕ) : ℝ)⁻¹ := by
          simpa [primeWeight] using mul_le_mul_of_nonneg_right hcardR' hw
        nlinarith [hle', hw']
      · have hcard0 : (E p ∩ Finset.Ico R (2 * R)).card = 0 := by
          rw [Finset.card_eq_zero]
          exact Finset.not_nonempty_iff_eq_empty.mp hnon
        simp [hnon, hRlt, hdvd, hcard0]
        exact mul_nonneg (Nat.cast_nonneg _) hw'
    · have hnon0 : ¬ (E p ∩ Finset.Ico R (2 * R)).Nonempty := by
        intro h
        rcases h with ⟨r, hr⟩
        have hrE : r ∈ E p := (Finset.mem_inter.mp hr).1
        have hrI := Finset.mem_Ico.mp (Finset.mem_inter.mp hr).2
        have hrEp : r ≤ p - 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrE).1).2
        have hp_le_R : p ≤ R := le_of_not_gt hRlt
        omega
      have hcard0 : (E p ∩ Finset.Ico R (2 * R)).card = 0 := by
        rw [Finset.card_eq_zero]
        exact Finset.not_nonempty_iff_eq_empty.mp hnon0
      simp [hnon0, hRlt, hdvd, hcard0]
  · have hcard2 : (E p ∩ Finset.Ico R (2 * R)).card ≤ 2 :=
      E_inter_card_le_two_of_not_dvd_Nall p R hp hdvd
    by_cases hnon : (E p ∩ Finset.Ico R (2 * R)).Nonempty
    · simp [hnon, hdvd]
      have hcard2' : (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) ≤ (2 : ℝ) := by
        exact_mod_cast hcard2
      exact mul_le_mul_of_nonneg_right hcard2' hw'
    · have hcard0 : (E p ∩ Finset.Ico R (2 * R)).card = 0 := by
        rw [Finset.card_eq_zero]
        exact Finset.not_nonempty_iff_eq_empty.mp hnon
      simp [hnon, hdvd, hcard0]

/-- The middle block is controlled by the active prime mass plus the exceptional
mass above `R`: `Wmid R x ≤ 2 * activeMass R x + R * exceptionalMassAboveR R x`. -/
theorem Wmid_le_two_mul_activeMass_add_R_mul_exceptionalMassAboveR (R x : ℕ) :
    Wmid R x ≤ 2 * activeMass R x + (R : ℝ) * exceptionalMassAboveR R x := by
  have h1 : Wmid R x ≤ W R x := Wmid_le_W R x
  have h2 : W R x ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) :=
    W_le_sum_E_card_weight R x
  have h2' : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ))
      = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * primeWeight p := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [primeWeight]
    rw [mul_one_div]
  have h3 : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * primeWeight p)
      ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        ((if (E p ∩ Finset.Ico R (2 * R)).Nonempty then 2 * primeWeight p else 0)
          + (R : ℝ) * (if R < p ∧ p ∣ Nall R then primeWeight p else 0)) := by
    refine Finset.sum_le_sum ?_
    intro p hp
    exact E_card_mul_weight_le R p (Finset.mem_filter.mp hp).2
  have h4 : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        ((if (E p ∩ Finset.Ico R (2 * R)).Nonempty then 2 * primeWeight p else 0)
          + (R : ℝ) * (if R < p ∧ p ∣ Nall R then primeWeight p else 0)))
      = 2 * activeMass R x + (R : ℝ) * exceptionalMassAboveR R x := by
    calc
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
          ((if (E p ∩ Finset.Ico R (2 * R)).Nonempty then 2 * primeWeight p else 0)
            + (R : ℝ) * (if R < p ∧ p ∣ Nall R then primeWeight p else 0)))
          = (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              (if (E p ∩ Finset.Ico R (2 * R)).Nonempty then 2 * primeWeight p else 0))
            + ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              ((R : ℝ) * (if R < p ∧ p ∣ Nall R then primeWeight p else 0)) := by
              rw [Finset.sum_add_distrib]
      _ = 2 * activeMass R x + (R : ℝ) * exceptionalMassAboveR R x := by
        congr 1
        · unfold activeMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          by_cases h : (E p ∩ Finset.Ico R (2 * R)).Nonempty <;> simp [h]
        · unfold exceptionalMassAboveR
          rw [Finset.mul_sum]
          have hdist : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              ((R : ℝ) * (if R < p ∧ p ∣ Nall R then primeWeight p else 0)))
            = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
              (if R < p ∧ p ∣ Nall R then (R : ℝ) * primeWeight p else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases h : R < p ∧ p ∣ Nall R <;> simp [h]
          have hset : ((Finset.Icc 2 x).filter Nat.Prime).filter
                (fun p => R < p ∧ p ∣ Nall R)
              = (Finset.Icc 2 x).filter (fun p => R < p ∧ Nat.Prime p ∧ p ∣ Nall R) := by
            ext p
            simp [and_assoc, and_left_comm, and_comm]
          rw [hdist, ← Finset.sum_filter, hset]
  calc
    Wmid R x ≤ W R x := h1
    _ ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := h2
    _ = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * primeWeight p := h2'
    _ ≤ 2 * activeMass R x + (R : ℝ) * exceptionalMassAboveR R x :=
        le_trans h3 (le_of_eq h4)

/-! ## Hypotheses and the capstone reductions -/

/-- The target hypothesis on the active mass alone: eventually
`activeMass R x ≤ C` for some constant `C < log 2 / 16`, uniformly in `x`. -/
def HA_activeMass_small : Prop :=
  ∃ R₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ C < Real.log 2 / 16 ∧
    ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, activeMass R x ≤ C

/-- The exceptional term vanishes: `R * exceptionalMassAboveR R x → 0`
uniformly in `x` as `R → ∞`. -/
def HA_exceptionalMass_vanishes : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ,
    (R : ℝ) * exceptionalMassAboveR R x ≤ ε

/-- The combined hypothesis needed for the constant block bound:
eventually `2 * activeMass R x + R * exceptionalMassAboveR R x ≤ C` with
`C < log 2 / 8`, uniformly in `x`. -/
def HA_active_mass_constant_bound : Prop :=
  ∃ R₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ C < Real.log 2 / 8 ∧
    ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ,
      2 * activeMass R x + (R : ℝ) * exceptionalMassAboveR R x ≤ C

/-- Small active mass plus vanishing exceptional mass imply the combined
constant bound. -/
theorem HA_active_mass_constant_bound_of_small_activeMass_and_vanishing_exceptional
    (hA : HA_activeMass_small) (hE : HA_exceptionalMass_vanishes) :
    HA_active_mass_constant_bound := by
  rcases hA with ⟨RA, CA, hCA0, hCAlt, hAmass⟩
  have htwice : 2 * CA < Real.log 2 / 8 := by nlinarith
  have hgap : 0 < Real.log 2 / 8 - 2 * CA := sub_pos.mpr htwice
  have hgap2 : 0 < (Real.log 2 / 8 - 2 * CA) / 2 := half_pos hgap
  rcases hE ((Real.log 2 / 8 - 2 * CA) / 2) hgap2 with ⟨RE, hExc⟩
  let C : ℝ := 2 * CA + (Real.log 2 / 8 - 2 * CA) / 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    nlinarith [hCA0, hgap]
  have hClt : C < Real.log 2 / 8 := by
    dsimp [C]
    nlinarith
  refine ⟨max RA RE, C, hC0, hClt, ?_⟩
  intro R hR x
  have hRA : RA ≤ R := le_trans (le_max_left RA RE) hR
  have hRE : RE ≤ R := le_trans (le_max_right RA RE) hR
  have hmass : 2 * activeMass R x ≤ 2 * CA :=
    mul_le_mul_of_nonneg_left (hAmass R hRA x) (by norm_num : (0 : ℝ) ≤ 2)
  have hexc : (R : ℝ) * exceptionalMassAboveR R x ≤ (Real.log 2 / 8 - 2 * CA) / 2 :=
    hExc R hRE x
  dsimp [C]
  nlinarith

/-- The capstone: under the combined active-mass bound, `x · ∏_{p≤x} (1 - c p)`
tends to infinity (the whole remaining goal of the project), via the existing
block-bound theorem. -/
theorem xP_tendsto_atTop_of_active_mass_bound (h : HA_active_mass_constant_bound) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  rcases h with ⟨Rmid₀, C, hC0, hClt, hmid⟩
  have hgap : 0 < Real.log 2 / 8 - C := sub_pos.mpr hClt
  have hε : 0 < (Real.log 2 / 8 - C) / 2 := half_pos hgap
  rcases Wtail_uniformly_tends_to_zero ((Real.log 2 / 8 - C) / 2) hε with ⟨Rt, htail⟩
  let C' : ℝ := (C + Real.log 2 / 8) / 2
  have hC'0 : 0 ≤ C' := by
    dsimp [C']
    nlinarith [hC0, hgap]
  have hC'lt : C' < Real.log 2 / 8 := by
    dsimp [C']
    nlinarith [hClt]
  have hW : ∀ R : ℕ, max Rmid₀ Rt ≤ R → ∀ x : ℕ, W R x ≤ C' := by
    intro R hR x
    have hRmid : Rmid₀ ≤ R := le_trans (le_max_left Rmid₀ Rt) hR
    have hRtail : Rt ≤ R := le_trans (le_max_right Rmid₀ Rt) hR
    have hWmid : Wmid R x ≤ C := by
      exact le_trans
        (Wmid_le_two_mul_activeMass_add_R_mul_exceptionalMassAboveR R x)
        (hmid R hRmid x)
    have hWtail : Wtail R x ≤ (Real.log 2 / 8 - C) / 2 := htail R hRtail x
    have hWdec := W_eq_Wtail_add_Wmid R x
    dsimp [C']
    nlinarith
  exact xP_tendsto_atTop_of_block_bound ⟨max Rmid₀ Rt, C', hC'0, hC'lt, hW⟩

/-- Small active mass plus vanishing exceptional mass imply the goal. -/
theorem xP_tendsto_atTop_of_activeMass_small_and_exceptional_vanishes
    (hA : HA_activeMass_small) (hE : HA_exceptionalMass_vanishes) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop :=
  xP_tendsto_atTop_of_active_mass_bound
    (HA_active_mass_constant_bound_of_small_activeMass_and_vanishing_exceptional hA hE)

end Erdos291
