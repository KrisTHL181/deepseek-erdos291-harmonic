import Erdos291.BlockActive
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The direct middle-block bound `HA_Wmid_constant_bound`

The previous active-mass decomposition
`Wmid R x ≤ 2 * activeMass R x + R * exceptionalMassAboveR R x` is not useful
for the final goal: numerical data shows that the exceptional term does not
vanish after multiplication by `R`, so `HA_active_mass_constant_bound` as
defined in `BlockActive.lean` is false.  The capstone
`xP_tendsto_atTop_of_block_bound` however only needs an eventual constant
bound for `W`; since `W = Wtail + Wmid` and the tail already decays uniformly,
it is enough to bound `Wmid` directly.

This file introduces the replacement target `HA_Wmid_constant_bound` and proves
that it implies the whole remaining goal.  It also records the concrete
candidate `R₀ = 18`, `C = 0.057082` (supported by computation) as the
conditional hypothesis `HA_Wmid_constant_bound_candidate`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The middle-active digits of a prime `p` for the block `[R,2R)`:
`r ∈ E p`, `R ≤ r < 2R`, and the `Wmid` range condition `2r+1 < p ≤ r²`. -/
noncomputable def middleActiveDigits (R p : ℕ) : Finset ℕ :=
  (E p).filter (fun r => R ≤ r ∧ r < 2 * R ∧ 2 * r + 1 < p ∧ p ≤ r ^ 2)

/-- The strict middle-active mass: one weight `1/(p-1)` for each prime `p ≤ x`
that has at least one middle-active digit in `[R,2R)`. -/
noncomputable def middleActiveMassStrict (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
    if (middleActiveDigits R p).Nonempty then primeWeight p else 0

/-- **The replacement target.**  Eventually `Wmid R x ≤ C` with `C < log 2 / 8`,
uniformly in `x`. -/
def HA_Wmid_constant_bound : Prop :=
  ∃ R₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ C < Real.log 2 / 8 ∧
    ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ C

/-- Concrete candidate supported by the data: `R₀ = 18`, `C = 0.057082`. -/
def HA_Wmid_constant_bound_candidate : Prop :=
  ∀ R : ℕ, 18 ≤ R → ∀ x : ℕ, Wmid R x ≤ 0.057082

/-- `middleActiveDigits R p` contains at most `R` digits: it is a subset of the
interval `[R, 2R)` of cardinality `R`. -/
lemma middleActiveDigits_card_le_R (R p : ℕ) :
    (middleActiveDigits R p).card ≤ R := by
  classical
  have hsub : middleActiveDigits R p ⊆ Finset.Ico R (2 * R) := by
    intro r hr
    have h := Finset.mem_filter.mp hr
    exact Finset.mem_Ico.mpr ⟨h.2.1, h.2.2.1⟩
  have hcard := Finset.card_le_card hsub
  have hIco : (Finset.Ico R (2 * R)).card = R := by
    simp
    omega
  rwa [hIco] at hcard

/-- `middleActiveMassStrict` is nonnegative. -/
lemma middleActiveMassStrict_nonneg (R x : ℕ) : 0 ≤ middleActiveMassStrict R x := by
  unfold middleActiveMassStrict
  exact Finset.sum_nonneg (by
    intro p hp
    by_cases h : (middleActiveDigits R p).Nonempty
    · simp [h, primeWeight]
    · simp [h])

/-- Every `Wmid` pair `(r,p)` gives a middle-active digit: the bridge is
`mem_E_iff_dvd_num`. -/
private lemma mem_middleActiveDigits_of_midPrimeCond {R x p r : ℕ}
    (hrIco : r ∈ Finset.Ico R (2 * R))
    (hp : p ∈ (Finset.Icc 2 x).filter
      (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)) :
    r ∈ middleActiveDigits R p := by
  have hpF := Finset.mem_filter.mp hp
  rcases hpF.2 with ⟨h2rp, hle, hpPrime, hdvd⟩
  have hrI := Finset.mem_Ico.mp hrIco
  have h1r : 1 ≤ r := by omega
  have hrp : r < p := by omega
  have hrE : r ∈ E p := (mem_E_iff_dvd_num p r hpPrime h1r hrp).mpr hdvd
  exact Finset.mem_filter.mpr ⟨hrE, hrI.1, hrI.2, h2rp, hle⟩

/-- Honest inequality: `Wmid` is controlled by the count of middle-active
digits per prime.  The proof follows the column rearrangement in
`BlockMidColumn.WmidBlock_le_sum_E_card_weight`, but with the sharper digit
condition `2r+1 < p ≤ r²` in place of the full `E p ∩ [R,2R)`. -/
theorem Wmid_le_sum_middleActiveDigits_card_weight (R x : ℕ) :
    Wmid R x ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      (((middleActiveDigits R p).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  classical
  let P : Finset ℕ := (Finset.Icc 2 x).filter Nat.Prime
  have hinner_le (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      (∑ p ∈ (Finset.Icc 2 x).filter
          (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
        (1 / ((p - 1 : ℕ) : ℝ))) ≤
      ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpP : p ∈ P := by
        exact Finset.mem_filter.mpr ⟨hpF.1, hpF.2.2.2.1⟩
      exact Finset.mem_filter.mpr ⟨hpP, mem_middleActiveDigits_of_midPrimeCond hr hp⟩
    · intro p hp hpnot
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  calc
    Wmid R x = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (Finset.Icc 2 x).filter
            (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
          (1 / ((p - 1 : ℕ) : ℝ)) := by rfl
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p := by
          refine Finset.sum_le_sum ?_
          intro r hr
          exact hinner_le r hr
    _ = ∑ p ∈ P,
        ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
          primeWeight p := by
          calc
            ∑ r ∈ Finset.Ico R (2 * R),
                ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p
              = ∑ r ∈ Finset.Ico R (2 * R),
                  ∑ p ∈ P, (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    rw [Finset.sum_filter]
            _ = ∑ p ∈ P,
                  ∑ r ∈ Finset.Ico R (2 * R),
                    (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
                    rw [Finset.sum_comm]
            _ = ∑ p ∈ P,
                  ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
                    primeWeight p := by
                    apply Finset.sum_congr rfl
                    intro p hp
                    rw [Finset.sum_filter]
    _ = ∑ p ∈ P,
        (((middleActiveDigits R p).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
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
          dsimp [primeWeight]
          rw [mul_one_div]

/-- Saturation at `x = 4R²`: for `r ∈ [R,2R)` every middle prime satisfies
`p ≤ r² < 4R²`, so `Wmid R x` is nondecreasing in `x` up to `4R²` and constant
afterwards. -/
lemma Wmid_le_Wmid_fourR2 (R x : ℕ) :
    Wmid R x ≤ Wmid R (4 * R ^ 2) := by
  classical
  let y : ℕ := 4 * R ^ 2
  by_cases hxy : x ≤ y
  · unfold Wmid
    refine Finset.sum_le_sum ?_
    intro r hr
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpIcc := Finset.mem_Icc.mp hpF.1
      have hpy : p ≤ y := le_trans hpIcc.2 hxy
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpy⟩, hpF.2⟩
    · intro p hp hpnot
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
  · have hyx : y ≤ x := by omega
    have hmain : Wmid R x = Wmid R y := by
      unfold Wmid
      apply Finset.sum_congr rfl
      intro r hr
      have hfilter : (Finset.Icc 2 x).filter
          (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)
          = (Finset.Icc 2 y).filter
          (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num) := by
        ext p
        constructor
        · intro hp
          have hpF := Finset.mem_filter.mp hp
          have hpIcc := Finset.mem_Icc.mp hpF.1
          have hple : p ≤ r ^ 2 := hpF.2.2.1
          have hrI := Finset.mem_Ico.mp hr
          have hsq : r ^ 2 < 4 * R ^ 2 := by nlinarith
          have hpy : p ≤ y := by dsimp [y]; omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpy⟩, hpF.2⟩
        · intro hp
          have hpF := Finset.mem_filter.mp hp
          have hpIcc := Finset.mem_Icc.mp hpF.1
          have hpx : p ≤ x := le_trans hpIcc.2 hyx
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpIcc.1, hpx⟩, hpF.2⟩
      rw [hfilter]
    exact le_of_eq hmain

/-- The capstone: under the direct `Wmid` constant bound, the block bound
required by `xP_tendsto_atTop_of_block_bound` follows by adding the uniformly
decaying tail, so the whole remaining goal holds. -/
theorem xP_tendsto_atTop_of_Wmid_constant_bound
    (h : HA_Wmid_constant_bound) :
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
    have hWmid : Wmid R x ≤ C := hmid R hRmid x
    have hWtail : Wtail R x ≤ (Real.log 2 / 8 - C) / 2 := htail R hRtail x
    have hWdec := W_eq_Wtail_add_Wmid R x
    dsimp [C']
    nlinarith
  exact xP_tendsto_atTop_of_block_bound ⟨max Rmid₀ Rt, C', hC'0, hC'lt, hW⟩

/-- Concrete candidate capstone: if the numerical candidate
`HA_Wmid_constant_bound_candidate` is proved (it is currently only a
hypothesis), the goal follows with `R₀ = 18` and `C = 0.057082`. -/
theorem xP_tendsto_atTop_of_Wmid_constant_bound_candidate
    (h : HA_Wmid_constant_bound_candidate) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  refine xP_tendsto_atTop_of_Wmid_constant_bound ⟨18, 0.057082, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : (0.456656 : ℝ) < Real.log 2 := by
      exact lt_trans (by norm_num : (0.456656 : ℝ) < 0.6931471803) Real.log_two_gt_d9
    have h8 : (0.057082 : ℝ) * 8 = 0.456656 := by norm_num
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    nlinarith [hlog]
  · intro R hR x
    exact h R hR x

end Erdos291
