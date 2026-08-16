import Erdos291.MidResultant
import Erdos291.MidRoots
import Erdos291.WmidRegimes

/-!
# Erdős #291 — MID-route conjectures (definitions + one conditional theorem)

This file records the three conjectural ingredients of the "MID column" route
and proves that they imply the MID regime bound `HA_Wmid_mid_constant_bound`,
hence (with the existing LOW+HIGH hypothesis) the full `HA_Wmid_constant_bound`.

Evidence (C scans):
* `HA_mid_harmonicSum_two_mul_r_ne_zero` and `HA_mid_harmonicSum_t_ne_zero`:
  0 counterexamples among the 10924 intrinsic MID pairs (`4r+1 < p`, `r ≤ 20000`).
* `HA_mid_resultant_F_G_ne_zero`: 0 counterexamples among 1238 intrinsic pairs
  with `p ≤ 50000`; `res(F,G) ≠ 0` for all 12 pairs with `p ≤ 500`.
* `HA_mid_column_single 8822647`: the largest observed multi-column prime is
  `8822647` for the `r ≤ 20000` range scans.
* `HA_mid_strict_active_mass_bound`: strict active mass maximum `0.0407338` for
  `R ≤ 1000` (evidence only).
* `HA_mid_small_R_finite_check 8822647`: unsupported beyond the scanned `R`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos291

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- Conjectural statement: for every intrinsic MID pair, `H_{2r} ≠ 0` in `ZMod p`.
Evidence: 0 counterexamples / 10924 MID pairs with `r ≤ 20000`. -/
def HA_mid_harmonicSum_two_mul_r_ne_zero : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p → harmonicSum p (2 * r) ≠ 0

/-- Conjectural statement: for every intrinsic MID pair, `H_t ≠ 0` in `ZMod p`,
where `t = (p-1-2r)/2`.
Evidence: 0 counterexamples / 10924 MID pairs with `r ≤ 20000`. -/
def HA_mid_harmonicSum_t_ne_zero : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    harmonicSum p ((p - 1 - 2 * r) / 2) ≠ 0

/-- Conjectural statement: for every intrinsic MID pair, the quotient resultant
`resultant (QrFactor p r) (QeFactor p r)` is nonzero in `ZMod p`.
Evidence: 0 counterexamples / 1238 intrinsic pairs `p ≤ 50000`; `res(F,G) ≠ 0`
for all 12 pairs with `p ≤ 500`. -/
def HA_mid_resultant_F_G_ne_zero : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    (Polynomial.resultant (QrFactor p r) (QeFactor p r) : ZMod p) ≠ 0

/-- The strict middle-active mass in the MID regime: one weight `1/(p-1)` for
each prime `p ≤ x` with `4R < p ≤ R²` that has at least one middle-active digit
in `[R, 2R)`. -/
noncomputable def middleActiveMassStrictMid (R x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ 4 * R < p ∧ p ≤ R ^ 2),
    if (middleActiveDigits R p).Nonempty then primeWeight p else 0

/-- Column-single hypothesis: in the MID regime above `P0`, each prime has at
most one middle-active digit in `[R, 2R)`. -/
def HA_mid_column_single (P0 : ℕ) : Prop :=
  ∀ R p : ℕ, 18 ≤ R → Nat.Prime p → P0 < p → 4 * R < p → p ≤ R ^ 2 →
    (middleActiveDigits R p).card ≤ 1

/-- Strict active mass hypothesis in the MID regime. -/
def HA_mid_strict_active_mass_bound : Prop :=
  ∀ R x : ℕ, 18 ≤ R → middleActiveMassStrictMid R x ≤ 0.045

/-- Small-`R` finite check: `WmidMid R x ≤ 0.045` whenever `4R ≤ P0`. -/
def HA_mid_small_R_finite_check (P0 : ℕ) : Prop :=
  ∀ R x : ℕ, 18 ≤ R → 4 * R ≤ P0 → WmidMid R x ≤ 0.045

/-! ## Reindexing `WmidMid` by middle-active digits -/

/-- A middle prime in the MID regime corresponds exactly to a middle-active digit
of the same prime. -/
private lemma mem_middlePrimes_mid_iff_mem_middleActiveDigits {R r x p : ℕ}
    (hr : r ∈ Finset.Ico R (2 * R)) :
    p ∈ (middlePrimes r x).filter (fun p => 4 * R < p ∧ p ≤ R ^ 2) ↔
      p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ 4 * R < p ∧ p ≤ R ^ 2) ∧
        r ∈ middleActiveDigits R p := by
  constructor
  · intro hp
    have hpF := Finset.mem_filter.mp hp
    have hpMid := hpF.1
    have hmid := hpF.2
    have hpMidF := mem_middlePrimes_iff.mp hpMid
    have hrI := Finset.mem_Ico.mp hr
    have h1r : 1 ≤ r := by omega
    have hrp : r < p := by omega
    have hrE : r ∈ E p :=
      (mem_E_iff_dvd_num p r hpMidF.2.2.2.1 h1r hrp).mpr hpMidF.2.2.2.2
    constructor
    · exact Finset.mem_filter.mpr ⟨hpMidF.1, by
        refine ⟨hpMidF.2.2.2.1, hmid.1, hmid.2⟩⟩
    · exact Finset.mem_filter.mpr ⟨hrE, by
        refine ⟨hrI.1, hrI.2, hpMidF.2.1, hpMidF.2.2.1⟩⟩
  · intro hp
    rcases hp with ⟨hpP, hrD⟩
    have hpF := Finset.mem_filter.mp hpP
    have hrF := Finset.mem_filter.mp hrD
    have hrE : r ∈ E p := hrF.1
    have hrI : R ≤ r ∧ r < 2 * R := ⟨hrF.2.1, hrF.2.2.1⟩
    have hmid : 2 * r + 1 < p := hrF.2.2.2.1
    have hpr2 : p ≤ r ^ 2 := hrF.2.2.2.2
    have hpPrime : Nat.Prime p := hpF.2.1
    have h1r : 1 ≤ r := mem_E_ge_one p r hrE
    have hrp : r < p := by omega
    have hdvd : (p : ℤ) ∣ (harmonic r).num :=
      (mem_E_iff_dvd_num p r hpPrime h1r hrp).mp hrE
    exact Finset.mem_filter.mpr ⟨mem_middlePrimes_iff.mpr
      ⟨hpF.1, hmid, hpr2, hpPrime, hdvd⟩, ⟨hpF.2.2.1, hpF.2.2.2⟩⟩

/-- `WmidMid` reindexed as the sum over MID primes of
`(middleActiveDigits R p).card * primeWeight p`. -/
private lemma WmidMid_eq_sum_middleActiveDigits_card_weight (R x : ℕ) :
    WmidMid R x =
      ∑ p ∈ (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ 4 * R < p ∧ p ≤ R ^ 2),
        ((middleActiveDigits R p).card : ℝ) * primeWeight p := by
  classical
  let P : Finset ℕ :=
    (Finset.Icc 2 x).filter (fun p => Nat.Prime p ∧ 4 * R < p ∧ p ≤ R ^ 2)
  have hinner (r : ℕ) (hr : r ∈ Finset.Ico R (2 * R)) :
      (∑ p ∈ (middlePrimes r x).filter (fun p => 4 * R < p ∧ p ≤ R ^ 2), primeWeight p)
        = ∑ p ∈ P, (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
    have hfilter : (middlePrimes r x).filter (fun p => 4 * R < p ∧ p ≤ R ^ 2)
        = P.filter (fun p => r ∈ middleActiveDigits R p) := by
      ext p
      constructor
      · intro hp
        exact Finset.mem_filter.mpr (mem_middlePrimes_mid_iff_mem_middleActiveDigits (r := r)
          (x := x) (p := p) hr |>.mp hp)
      · intro hp
        have hpF := Finset.mem_filter.mp hp
        exact (mem_middlePrimes_mid_iff_mem_middleActiveDigits (r := r) (x := x) (p := p) hr).mpr
          ⟨hpF.1, hpF.2⟩
    calc
      (∑ p ∈ (middlePrimes r x).filter (fun p => 4 * R < p ∧ p ≤ R ^ 2), primeWeight p)
          = ∑ p ∈ P.filter (fun p => r ∈ middleActiveDigits R p), primeWeight p := by
              rw [hfilter]
      _ = ∑ p ∈ P, (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
              rw [Finset.sum_filter]
  calc
    WmidMid R x = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (middlePrimes r x).filter (fun p => 4 * R < p ∧ p ≤ R ^ 2), primeWeight p := by
          rfl
    _ = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ P, (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          exact hinner r hr
    _ = ∑ p ∈ P,
        ∑ r ∈ Finset.Ico R (2 * R),
          (if r ∈ middleActiveDigits R p then primeWeight p else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ p ∈ P,
        ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ middleActiveDigits R p),
          primeWeight p := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.sum_filter]
    _ = ∑ p ∈ P, ∑ r ∈ middleActiveDigits R p, primeWeight p := by
          refine Finset.sum_congr rfl ?_
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
    _ = ∑ p ∈ P, ((middleActiveDigits R p).card : ℝ) * primeWeight p := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The conditional theorem -/

/-- Under the column-single, strict-mass and small-`R` hypotheses, the MID regime
bound `HA_Wmid_mid_constant_bound` holds. -/
theorem HA_Wmid_mid_constant_bound_of_column_single_and_strict_mass
    (hcol : HA_mid_column_single 8822647)
    (hstrict : HA_mid_strict_active_mass_bound)
    (hsmall : HA_mid_small_R_finite_check 8822647) :
    HA_Wmid_mid_constant_bound := by
  intro R hR x
  by_cases h4R : 4 * R ≤ 8822647
  · exact hsmall R x hR h4R
  · have h4Rgt : 8822647 < 4 * R := by omega
    have heq : WmidMid R x = middleActiveMassStrictMid R x := by
      classical
      rw [WmidMid_eq_sum_middleActiveDigits_card_weight]
      unfold middleActiveMassStrictMid
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpPrime : Nat.Prime p := hpF.2.1
      have hpgt : 8822647 < p := lt_trans h4Rgt hpF.2.2.1
      have hcard_le := hcol R p hR hpPrime hpgt hpF.2.2.1 hpF.2.2.2
      by_cases hne : (middleActiveDigits R p).Nonempty
      · have hpos : 0 < (middleActiveDigits R p).card := Finset.card_pos.mpr hne
        have hcard1 : (middleActiveDigits R p).card = 1 := by omega
        simp [hne, hcard1]
      · have hempty : middleActiveDigits R p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hempty]
    rw [heq]
    exact hstrict R x hR

/-- The MID-column route plus the LOW+HIGH bound implies `HA_Wmid_constant_bound`. -/
theorem HA_Wmid_constant_bound_of_mid_column_route
    (hcol : HA_mid_column_single 8822647) (hstrict : HA_mid_strict_active_mass_bound)
    (hsmall : HA_mid_small_R_finite_check 8822647)
    (hLH : HA_Wmid_low_high_bound) :
    HA_Wmid_constant_bound :=
  HA_Wmid_constant_bound_of_regime_bounds hLH
    (HA_Wmid_mid_constant_bound_of_column_single_and_strict_mass hcol hstrict hsmall)

/-- The MID-column route plus the LOW+HIGH bound implies `x · prodOneSub x → ∞`. -/
theorem xP_tendsto_atTop_of_mid_column_route
    (hcol : HA_mid_column_single 8822647) (hstrict : HA_mid_strict_active_mass_bound)
    (hsmall : HA_mid_small_R_finite_check 8822647) (hLH : HA_Wmid_low_high_bound) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop :=
  xP_tendsto_atTop_of_Wmid_constant_bound
    (HA_Wmid_constant_bound_of_mid_column_route hcol hstrict hsmall hLH)

/-! ## MID-route conjectures: common roots and the middle resultant -/

/-- No F_p-valued common-root (CR) solution for intrinsic MID pairs:
`H_β = H_{β+r} = H_{2r-β}` has no solution `β ∈ [1, 2r] \ {r}`.
Evidence: 0/4492 intrinsic pairs `p ≤ 200000`; 0/10924 intrinsic MID pairs
`r ≤ 20000` (all computed by C scans in earlier attack rounds). -/
def HA_mid_CR_free : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    ∀ β : ℕ, 1 ≤ β → β ≤ 2 * r → β ≠ r →
      harmonicSum p β = harmonicSum p (β + r) →
      harmonicSum p β = harmonicSum p (2 * r - β) → False

/-- The middle resultant `resultant (Q p r) (Q p (p-1-2r))` is nonzero for every intrinsic
MID pair.  Under `HA_mid_CR_free` this is equivalent to `H_{2r} ≠ 0` (via
`resultant_Qr_Qe_eq_zero_iff` and `Fp_common_root_iff_CR`); both sides hold in all scanned
data (0 counterexamples). -/
def HA_mid_resultant_Qr_Qe_ne_zero_intrinsic : Prop :=
  ∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) ≠ 0

/-- The safe implication available without an F_p-valued root assumption:
`H_{2r} ≠ 0` and `res(F,G) ≠ 0` together imply the middle resultant is nonzero.
This follows directly from `MidResultant.resultant_Qr_Qe_eq_zero_iff`. -/
theorem HA_mid_resultant_Qr_Qe_ne_zero_intrinsic_of_resultant_F_G_ne_zero_and_harmonicSum_two_mul_r_ne_zero
    (hH : HA_mid_harmonicSum_two_mul_r_ne_zero)
    (hFG : HA_mid_resultant_F_G_ne_zero) :
    HA_mid_resultant_Qr_Qe_ne_zero_intrinsic := by
  intro p r hp hmid hrE
  haveI : Fact p.Prime := ⟨hp⟩
  intro hres
  have h := (resultant_Qr_Qe_eq_zero_iff p r hrE (by omega : 2 * r + 1 < p)).mp hres
  rcases h with hH0 | hFG0
  · exact (hH p r hp hmid hrE) hH0
  · exact (hFG p r hp hmid hrE) hFG0

end

end Erdos291
