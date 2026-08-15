import Erdos291.BlockMidDyadic
import Erdos291.BadDensity
import Erdos291.GapResultantHeight
import Erdos291.MertensUpper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Erdős #291 — column estimate for the middle block

This file develops the *column route* for `Wmid`: for each prime `p` in a dyadic block
`[P, 2P)`, the contribution is controlled by the number of bad digits `r ∈ E p` that lie in
the `r`-block `[R, 2R)`.

We prove:

1. **Interval sparsity.** If `p ∤ Nall D`, then `E p ∩ [R, 2R)` has at most
   `2 * (R / D + 1)` elements (with the natural-division convention).  This is the
   interval version of the block-sparsity estimate from `Erdos291.BadDensity`.

2. **Column bound.** `WmidBlock R P x` is at most the pair-counting sum
   `Σ_{p ∈ primeBlock P x} |E p ∩ [R, 2R)| / (p - 1)`, and consequently (with
   `sparseBound R D = 2 * (R / D + 1)`)

   `WmidBlock R P x ≤ sparseBound R D * Σ_{p ∈ primeBlock P x} 1/(p-1)
       + R * Σ_{p ∈ primeBlock P x, p ∣ Nall D} 1/(p-1)`.

   The exceptional coefficient is `R` (not `1`): for an exceptional prime the
   no-triple sparsity estimate is unavailable, and `|E p ∩ [R,2R)| ≤ R` is the only
   unconditional bound.  The task-suggested coefficient `1` would need
   `|E p ∩ [R,2R)| ≤ 1` for exceptional `p`, which is false (e.g. `E p` can contain
   both `r` and `p - 1 - r` in `[R, 2R)`).  See the docstring for
   `WmidBlock_le_non_exceptional_add_exceptional`.

3. **Exceptional mass.** For `3 ≤ P`, the exceptional prime mass in a dyadic block is
   `≤ 2 log (Nall D) / ((P - 1) log (P - 1))`, obtained from
   `GapResultantHeight.sum_inv_prime_divisors_gt_le`.

4. **Dyadic prime mass.** For `3 ≤ P`, `Σ_{P ≤ p < 2P, p prime} 1/(p-1) ≤
   3 * primeCountingConst / log P`, derived from `MertensUpper.primeCounting_le_const_div_log`.

5. **Conditional capstones.** We give two explicit hypotheses under which uniform
   vanishing of `Wmid` follows by summing the dyadic blocks:
   a generic block-bound hypothesis `HA_column_bound`, and the concrete column-route
   hypothesis `HA_column_route` whose block bound is exactly the column estimate above.

The open question is whether `HA_column_route` can be discharged: with `D = D(R)` the
non-exceptional term is `O(1 / D(R))` per block (after summing `O(log R)` dyadic blocks,
each contributing `O(1 / log P)` reciprocal mass), while the exceptional term carries a
factor `R` and the existing files provide no height bound for `Nall (D(R))`; controlling it
appears to require a bound on the resultants `Nde d e` (or on `Nall D`) that is not present
in the repository.
-/

open scoped BigOperators Topology Nat.Prime

namespace Erdos291

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-- The reciprocal weight `1 / (p - 1)` used throughout the column estimates. -/
noncomputable def weight (p : ℕ) : ℝ := 1 / ((p - 1 : ℕ) : ℝ)

/-- The sparse coefficient `2 * (R / D + 1)` (natural division), cast to `ℝ`. -/
noncomputable def sparseBound (R D : ℕ) : ℝ := 2 * (((R / D + 1 : ℕ) : ℝ))

/-- The primes in the dyadic block `[P, 2P)` that are at most `x`. -/
def primeBlock (P x : ℕ) : Finset ℕ :=
  (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ Nat.Prime p)

/-- The middle-prime condition from `BlockMidDyadic`, repeated locally so that it can be
mentioned in this file (the original is a private abbrev). -/
private abbrev midPrimeCondCol (r p : ℕ) : Prop :=
  2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num

/-- Each reciprocal weight is nonnegative. -/
lemma weight_nonneg (p : ℕ) : 0 ≤ weight p := by
  dsimp [weight]
  exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)

/-! ## 1. Interval sparsity -/

private lemma card_image_sub_add_one_eq_card {S : Finset ℕ} {a : ℕ}
    (ha : ∀ r ∈ S, a ≤ r) :
    (S.image (fun r => r - a + 1)).card = S.card := by
  classical
  exact Finset.card_image_of_injOn (by
    intro r hr s hs h
    have hr_ge : a ≤ r := ha r hr
    have hs_ge : a ≤ s := ha s hs
    have hsub : r - a = s - a := Nat.succ.inj h
    have hr_eq : a + (r - a) = r := Nat.add_sub_of_le hr_ge
    have hs_eq : a + (s - a) = s := Nat.add_sub_of_le hs_ge
    omega)

private lemma noTripleWithin_image_sub_add_one {S : Finset ℕ} {a D : ℕ}
    (ha : ∀ r ∈ S, a ≤ r) (h : NoTripleWithin S D) :
    NoTripleWithin (S.image (fun r => r - a + 1)) D := by
  intro x₁ x₂ x₃ hx₁ hx₂ hx₃ h12 h23 hspan
  rcases Finset.mem_image.mp hx₁ with ⟨r₁, hr₁, rfl⟩
  rcases Finset.mem_image.mp hx₂ with ⟨r₂, hr₂, rfl⟩
  rcases Finset.mem_image.mp hx₃ with ⟨r₃, hr₃, rfl⟩
  have hr₁_ge : a ≤ r₁ := ha r₁ hr₁
  have hr₂_ge : a ≤ r₂ := ha r₂ hr₂
  have hr₃_ge : a ≤ r₃ := ha r₃ hr₃
  have h₁ : r₁ < r₂ := by omega
  have h₂ : r₂ < r₃ := by omega
  have h₃ : r₃ - r₁ ≤ D := by
    have hsub : (r₃ - a + 1) - (r₁ - a + 1) = r₃ - r₁ := by
      have h₃e : a + (r₃ - a) = r₃ := Nat.add_sub_of_le hr₃_ge
      have h₁e : a + (r₁ - a) = r₁ := Nat.add_sub_of_le hr₁_ge
      omega
    rwa [hsub] at hspan
  exact h hr₁ hr₂ hr₃ h₁ h₂ h₃

/-- **Interval sparsity (combinatorial).** If `S ⊆ [a, b]` has no three elements of span
`≤ D`, then `|S| ≤ 2 * ((b - a + 1) / D + 1)`.  The proof shifts `S` by `r ↦ r - a + 1`
into `[1, b - a + 1]` and applies `BadDensity.card_le_two_mul_div_add_two_of_no_triple`. -/
theorem card_le_two_mul_div_add_two_of_no_triple_Icc (S : Finset ℕ) (a b D : ℕ)
    (hD : 0 < D) (hS : S ⊆ Finset.Icc a b) (h : NoTripleWithin S D) :
    S.card ≤ 2 * ((b - a + 1) / D + 1) := by
  classical
  let S' : Finset ℕ := S.image (fun r => r - a + 1)
  have ha : ∀ r ∈ S, a ≤ r := by
    intro r hr
    exact (Finset.mem_Icc.mp (hS hr)).1
  have hS' : S' ⊆ Finset.Icc 1 (b - a + 1) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
    rw [Finset.mem_Icc]
    constructor
    · have hr_ge : a ≤ r := ha r hr
      omega
    · have hr_le : r ≤ b := (Finset.mem_Icc.mp (hS hr)).2
      omega
  have hNo' : NoTripleWithin S' D := noTripleWithin_image_sub_add_one (S := S) (a := a) ha h
  have hcard := card_le_two_mul_div_add_two_of_no_triple S' D (b - a + 1) hD hS' hNo'
  have hcard' : S'.card = S.card := card_image_sub_add_one_eq_card (S := S) (a := a) ha
  rwa [hcard'] at hcard

/-- **Interval sparsity for `E p`.** If `p` is prime and `p ∤ Nall D`, then the interval
`[R, 2R)` contains at most `2 * (R / D + 1)` bad digits of `p`. -/
lemma E_interval_card_le (p D R : ℕ) [Fact p.Prime] (hD : 0 < D)
    (h : ¬ p ∣ Nall D) :
    ((E p ∩ Finset.Ico R (2 * R)).card) ≤ 2 * (R / D + 1) := by
  by_cases hR : R = 0
  · subst R
    simp
  · have hS : E p ∩ Finset.Ico R (2 * R) ⊆ Finset.Icc R (2 * R - 1) := by
      intro r hr
      have hrIco := (Finset.mem_inter.mp hr).2
      have hlo : R ≤ r := (Finset.mem_Ico.mp hrIco).1
      have hhi : r < 2 * R := (Finset.mem_Ico.mp hrIco).2
      rw [Finset.mem_Icc]
      omega
    have hNo : NoTripleWithin (E p ∩ Finset.Ico R (2 * R)) D := by
      intro r₁ r₂ r₃ h₁ h₂ h₃ h12 h23 hspan
      have hE₁ : r₁ ∈ E p := (Finset.mem_inter.mp h₁).1
      have hE₂ : r₂ ∈ E p := (Finset.mem_inter.mp h₂).1
      have hE₃ : r₃ ∈ E p := (Finset.mem_inter.mp h₃).1
      exact no_triple_of_not_dvd_Nall p D h hE₁ hE₂ hE₃ h12 h23 hspan
    have hcard := card_le_two_mul_div_add_two_of_no_triple_Icc
      (E p ∩ Finset.Ico R (2 * R)) R (2 * R - 1) D hD hS hNo
    have hlen : 2 * R - 1 - R + 1 = R := by omega
    simpa [hlen] using hcard

/-! ## 2. Column bound for one prime block -/

private lemma filter_midPrime_eq_primeBlock_filter (P x r : ℕ) :
    (Finset.Ico P (2 * P)).filter (fun p => p ≤ x ∧ midPrimeCondCol r p)
      = (primeBlock P x).filter (fun p => midPrimeCondCol r p) := by
  ext p
  simp [primeBlock, midPrimeCondCol]
  tauto

private lemma WmidBlock_eq_sum_over_primeBlock (R P x : ℕ) :
    WmidBlock R P x =
      ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (primeBlock P x).filter (fun p => midPrimeCondCol r p),
          weight p := by
  unfold WmidBlock
  apply Finset.sum_congr rfl
  intro r hr
  rw [filter_midPrime_eq_primeBlock_filter P x r]
  unfold weight
  rfl

/-- For a fixed `r`, every middle prime `p` in the block that contributes to `WmidBlock`
satisfies `r ∈ E p`: the bridge is `mem_E_iff_dvd_num`. -/
private lemma sum_mid_le_sum_E_filter (P x r : ℕ) :
    (∑ p ∈ (primeBlock P x).filter (fun p => midPrimeCondCol r p), weight p) ≤
      ∑ p ∈ (primeBlock P x).filter (fun p => r ∈ E p), weight p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hcond : midPrimeCondCol r p := hpF.2
    rcases hcond with ⟨h2rp, hle, hpPrime, hdvd⟩
    have hp2 : 2 ≤ p := hpPrime.two_le
    have h1r : 1 ≤ r := by
      by_contra hrnot
      have hr0 : r = 0 := by omega
      subst r
      simp at hle
      omega
    have hrp : r < p := by
      have h2r_lt : 2 * r < p := by omega
      by_cases hr0 : r = 0
      · subst r; omega
      · have hle_mul : r ≤ 2 * r := by omega
        omega
    exact Finset.mem_filter.mpr ⟨hpF.1, (mem_E_iff_dvd_num p r hpPrime h1r hrp).mpr hdvd⟩
  · intro p hp hp'
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)

/-- **Pair-counting inequality.** `WmidBlock R P x` is bounded by the column sum
`Σ_p |E p ∩ [R, 2R)| / (p - 1)`. -/
lemma WmidBlock_le_sum_E_card_weight (R P x : ℕ) :
    WmidBlock R P x ≤
      ∑ p ∈ primeBlock P x,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  classical
  calc
    WmidBlock R P x = ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (primeBlock P x).filter (fun p => midPrimeCondCol r p), weight p :=
          WmidBlock_eq_sum_over_primeBlock R P x
    _ ≤ ∑ r ∈ Finset.Ico R (2 * R),
        ∑ p ∈ (primeBlock P x).filter (fun p => r ∈ E p), weight p := by
          apply Finset.sum_le_sum
          intro r hr
          exact sum_mid_le_sum_E_filter P x r
    _ = ∑ p ∈ primeBlock P x,
        ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ E p), weight p := by
          calc
            ∑ r ∈ Finset.Ico R (2 * R),
                ∑ p ∈ (primeBlock P x).filter (fun p => r ∈ E p), weight p
                = ∑ r ∈ Finset.Ico R (2 * R),
                    ∑ p ∈ primeBlock P x, (if r ∈ E p then weight p else 0) := by
                    apply Finset.sum_congr rfl
                    intro r hr
                    rw [Finset.sum_filter]
            _ = ∑ p ∈ primeBlock P x,
                  ∑ r ∈ Finset.Ico R (2 * R), (if r ∈ E p then weight p else 0) := by
                  rw [Finset.sum_comm]
            _ = ∑ p ∈ primeBlock P x,
                  ∑ r ∈ (Finset.Ico R (2 * R)).filter (fun r => r ∈ E p), weight p := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  rw [Finset.sum_filter]
    _ = ∑ p ∈ primeBlock P x,
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hfilter : (Finset.Ico R (2 * R)).filter (fun r => r ∈ E p) =
              E p ∩ Finset.Ico R (2 * R) := by
            ext r
            simp [Finset.mem_inter, and_comm]
          rw [hfilter]
          rw [Finset.sum_const, nsmul_eq_mul]
          dsimp [weight]
          rw [one_div, div_eq_mul_inv]

/-- **Column bound with split exceptional primes.** For non-exceptional primes we use the
interval sparsity; for exceptional primes we use the unconditional bound
`|E p ∩ [R,2R)| ≤ R`.  Hence

`WmidBlock R P x ≤ sparseBound R D * Σ_{p ∈ primeBlock P x} 1/(p-1)
    + R * Σ_{p ∈ primeBlock P x, p ∣ Nall D} 1/(p-1)`.

Note: the exceptional coefficient is `R`, not `1` as in the original task sketch.  The
coefficient `1` would require `|E p ∩ [R,2R)| ≤ 1` for every exceptional `p`, which is not
true: `E p` is symmetric (`r ↔ p - 1 - r`), so for `p > 2R + 1` the interval `[R, 2R)` can
contain several bad digits. -/
lemma WmidBlock_le_non_exceptional_add_exceptional (R P x D : ℕ) (hD : 0 < D) :
    WmidBlock R P x ≤
      sparseBound R D * (∑ p ∈ primeBlock P x, weight p)
      + (R : ℝ) * (∑ p ∈ (primeBlock P x).filter (fun p => p ∣ Nall D), weight p) := by
  classical
  let S := primeBlock P x
  have hpair := WmidBlock_le_sum_E_card_weight R P x
  have hcard_exc : ∀ p ∈ S, ((E p ∩ Finset.Ico R (2 * R)).card : ℝ) ≤ (R : ℝ) := by
    intro p hp
    have hcardNat : (E p ∩ Finset.Ico R (2 * R)).card ≤ R := by
      calc
        (E p ∩ Finset.Ico R (2 * R)).card ≤ (Finset.Ico R (2 * R)).card :=
          Finset.card_le_card (Finset.inter_subset_right)
        _ = 2 * R - R := by rw [Nat.card_Ico]
        _ = R := by omega
    exact_mod_cast hcardNat
  have hcard_non : ∀ p ∈ S, ¬ p ∣ Nall D →
      ((E p ∩ Finset.Ico R (2 * R)).card : ℝ) ≤ sparseBound R D := by
    intro p hp hnot
    have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2.2
    letI : Fact p.Prime := ⟨hpPrime⟩
    have hnat : (E p ∩ Finset.Ico R (2 * R)).card ≤ 2 * (R / D + 1) :=
      E_interval_card_le p D R hD hnot
    have hnatR : (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) ≤
        ((2 * (R / D + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    have hcast : ((2 * (R / D + 1) : ℕ) : ℝ) = sparseBound R D := by
      dsimp [sparseBound]
      norm_num
    simpa [hcast] using hnatR
  have hsum_non : (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D),
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p) ≤
      sparseBound R D * (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D), weight p) := by
    have hpoint : ∀ p ∈ S.filter (fun p => ¬ p ∣ Nall D),
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p ≤
          sparseBound R D * weight p := by
      intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hnot : ¬ p ∣ Nall D := (Finset.mem_filter.mp hp).2
      exact mul_le_mul_of_nonneg_right (hcard_non p hpS hnot) (weight_nonneg p)
    calc
      (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D),
          (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p)
          ≤ ∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D), sparseBound R D * weight p := by
            exact Finset.sum_le_sum hpoint
      _ = sparseBound R D * (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D), weight p) := by
            rw [Finset.mul_sum]
  have hsum_exc : (∑ p ∈ S.filter (fun p => p ∣ Nall D),
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p) ≤
      (R : ℝ) * (∑ p ∈ S.filter (fun p => p ∣ Nall D), weight p) := by
    have hpoint : ∀ p ∈ S.filter (fun p => p ∣ Nall D),
        (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p ≤
          (R : ℝ) * weight p := by
      intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      exact mul_le_mul_of_nonneg_right (hcard_exc p hpS) (weight_nonneg p)
    calc
      (∑ p ∈ S.filter (fun p => p ∣ Nall D),
          (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p)
          ≤ ∑ p ∈ S.filter (fun p => p ∣ Nall D), (R : ℝ) * weight p := by
            exact Finset.sum_le_sum hpoint
      _ = (R : ℝ) * (∑ p ∈ S.filter (fun p => p ∣ Nall D), weight p) := by
            rw [Finset.mul_sum]
  calc
    WmidBlock R P x ≤
        ∑ p ∈ S, (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) / ((p - 1 : ℕ) : ℝ) := hpair
    _ = ∑ p ∈ S, (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [weight]
          rw [one_div, div_eq_mul_inv]
    _ = (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D),
              (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p)
          + (∑ p ∈ S.filter (fun p => p ∣ Nall D),
              (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p) := by
          simpa [add_comm] using
            ((Finset.sum_filter_add_sum_filter_not S (fun p => p ∣ Nall D)
              (fun p => (((E p ∩ Finset.Ico R (2 * R)).card : ℕ) : ℝ) * weight p)).symm)
    _ ≤ sparseBound R D * (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D), weight p)
          + (R : ℝ) * (∑ p ∈ S.filter (fun p => p ∣ Nall D), weight p) := by
          exact add_le_add hsum_non hsum_exc
    _ ≤ sparseBound R D * (∑ p ∈ S, weight p)
          + (R : ℝ) * (∑ p ∈ S.filter (fun p => p ∣ Nall D), weight p) := by
          have hsubset : S.filter (fun p => ¬ p ∣ Nall D) ⊆ S := Finset.filter_subset _ _
          have hle : (∑ p ∈ S.filter (fun p => ¬ p ∣ Nall D), weight p) ≤ ∑ p ∈ S, weight p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset
              (by intro p hp hp'; exact weight_nonneg p)
          have hsparse_nonneg : 0 ≤ sparseBound R D := by dsimp [sparseBound]; positivity
          exact add_le_add_left (mul_le_mul_of_nonneg_left hle hsparse_nonneg) _
    _ = sparseBound R D * (∑ p ∈ primeBlock P x, weight p)
          + (R : ℝ) * (∑ p ∈ (primeBlock P x).filter (fun p => p ∣ Nall D), weight p) := by
          rfl

/-! ## 3. Exceptional mass -/

/-- **Exceptional mass in a prime block.** For `3 ≤ P`, the reciprocal mass of the prime
divisors of `Nall D` lying in `[P, 2P)` is at most
`2 log (Nall D) / ((P - 1) log (P - 1))`. -/
lemma exceptional_mass_primeBlock_le (D P x : ℕ) (hP : 3 ≤ P) :
    (∑ p ∈ (primeBlock P x).filter (fun p => p ∣ Nall D), weight p) ≤
      2 * Real.log (Nall D : ℝ) / (((P - 1 : ℕ) : ℝ) * Real.log ((P - 1 : ℕ) : ℝ)) := by
  classical
  let S : Finset ℕ := (primeBlock P x).filter (fun p => p ∣ Nall D)
  let Sbig : Finset ℕ := (Finset.Icc P (Nall D)).filter (fun p => Nat.Prime p ∧ p ∣ Nall D)
  have hsub : S ⊆ Sbig := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpPF := Finset.mem_filter.mp hpF.1
    have hpIco : p ∈ Finset.Ico P (2 * P) := hpPF.1
    have hpPrime : Nat.Prime p := hpPF.2.2
    have hp_dvd : p ∣ Nall D := hpF.2
    have hp_le_N : p ≤ Nall D := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nall_ne_zero D)) hp_dvd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hpIco).1, hp_le_N⟩, hpPrime, hp_dvd⟩
  have hweight_le : ∀ p ∈ S, weight p ≤ 2 * (1 / (p : ℝ)) := by
    intro p hp
    have hpS := Finset.mem_filter.mp hp
    have hpPrime : Nat.Prime p := by
      have hpPF := Finset.mem_filter.mp hpS.1
      exact hpPF.2.2
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hpm_pos : 0 < ((p - 1 : ℕ) : ℝ) := by
      have h : 0 < p - 1 := by omega
      exact_mod_cast h
    have hp_pos : 0 < (p : ℝ) := by positivity
    dsimp [weight]
    rw [show 2 * (1 / (p : ℝ)) = 2 / (p : ℝ) by rw [mul_one_div]]
    rw [div_le_div_iff₀ hpm_pos hp_pos]
    rw [Nat.cast_sub (show 1 ≤ p by omega)]
    norm_num
    have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hsum_weight_le : (∑ p ∈ S, weight p) ≤ ∑ p ∈ S, 2 * (1 / (p : ℝ)) := by
    exact Finset.sum_le_sum hweight_le
  have hsum_subset : (∑ p ∈ S, 2 * (1 / (p : ℝ))) ≤ ∑ p ∈ Sbig, 2 * (1 / (p : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp hp'
    positivity
  have hsum_big : (∑ p ∈ Sbig, 2 * (1 / (p : ℝ))) = 2 * (∑ p ∈ Sbig, 1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
  have hgap := sum_inv_prime_divisors_gt_le (Nall D) (P - 1) (Nall_ne_zero D) (by omega : 2 ≤ P - 1)
  have hbig_le : (∑ p ∈ Sbig, 1 / (p : ℝ)) ≤
      Real.log (Nall D : ℝ) / (((P - 1 : ℕ) : ℝ) * Real.log ((P - 1 : ℕ) : ℝ)) := by
    have hP' : P - 1 + 1 = P := by omega
    simpa [Sbig, one_div, hP'] using hgap
  calc
    (∑ p ∈ S, weight p) ≤ ∑ p ∈ S, 2 * (1 / (p : ℝ)) := hsum_weight_le
    _ ≤ ∑ p ∈ Sbig, 2 * (1 / (p : ℝ)) := hsum_subset
    _ = 2 * (∑ p ∈ Sbig, 1 / (p : ℝ)) := hsum_big
    _ ≤ 2 * Real.log (Nall D : ℝ) / (((P - 1 : ℕ) : ℝ) * Real.log ((P - 1 : ℕ) : ℝ)) := by
          simpa [mul_div_assoc] using
            (mul_le_mul_of_nonneg_left hbig_le (by norm_num : 0 ≤ (2 : ℝ)))

/-! ## 4. Dyadic prime mass -/

private lemma prime_mass_bound_real (P : ℕ) (hP : 3 ≤ P) :
    (primeCountingConst * (2 * (P : ℝ)) / Real.log (2 * (P : ℝ))) / ((P - 1 : ℕ) : ℝ)
      ≤ (3 * primeCountingConst) / Real.log (P : ℝ) := by
  have hPm_pos : 0 < ((P - 1 : ℕ) : ℝ) := by
    have h : 0 < P - 1 := by omega
    exact_mod_cast h
  have hlogP_pos : 0 < Real.log (P : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < P by omega)
  have hlog2P_pos : 0 < Real.log (2 * (P : ℝ)) := by
    apply Real.log_pos
    have hP_real : (1 : ℝ) ≤ P := by
      exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 3) hP)
    nlinarith
  have hC_nonneg : 0 ≤ primeCountingConst := by
    dsimp [primeCountingConst]
    positivity
  have hPm_le : 2 * (P : ℝ) ≤ 3 * ((P - 1 : ℕ) : ℝ) := by
    have hnat : 2 * P ≤ 3 * (P - 1) := by omega
    have hnatR : ((2 * P : ℕ) : ℝ) ≤ ((3 * (P - 1) : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by norm_num
    have h3 : ((3 * (P - 1) : ℕ) : ℝ) = 3 * ((P - 1 : ℕ) : ℝ) := by norm_num
    simpa [h2, h3] using hnatR
  have hlog_le : Real.log (P : ℝ) ≤ Real.log (2 * (P : ℝ)) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < P by omega)
    · have hP_real : (1 : ℝ) ≤ P := by
        exact_mod_cast (le_trans (by norm_num : (1 : ℕ) ≤ 3) hP)
      nlinarith
  have hlogP_nonneg : 0 ≤ Real.log (P : ℝ) := le_of_lt hlogP_pos
  have h3Pm_nonneg : 0 ≤ 3 * ((P - 1 : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul hPm_le hlog_le hlogP_nonneg h3Pm_nonneg
  have hmulC : primeCountingConst * (2 * (P : ℝ)) * Real.log (P : ℝ) ≤
      primeCountingConst * (3 * ((P - 1 : ℕ) : ℝ)) * Real.log (2 * (P : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hmul hC_nonneg
    nlinarith [this]
  have hflat : primeCountingConst * (2 * (P : ℝ)) / Real.log (2 * (P : ℝ)) /
      ((P - 1 : ℕ) : ℝ) =
      (primeCountingConst * (2 * (P : ℝ))) /
        (Real.log (2 * (P : ℝ)) * ((P - 1 : ℕ) : ℝ)) := by
    field_simp [hlog2P_pos.ne', hPm_pos.ne']
  rw [hflat]
  rw [div_le_div_iff₀ (mul_pos hlog2P_pos hPm_pos) hlogP_pos]
  nlinarith [hmulC]

/-- **Dyadic prime mass.** For `3 ≤ P`, the sum of `1/(p-1)` over the primes
`P ≤ p < 2P` is at most `3 * primeCountingConst / log P`. -/
lemma dyadic_prime_mass_le (P : ℕ) (hP : 3 ≤ P) :
    (∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime, 1 / ((p - 1 : ℕ) : ℝ)) ≤
      (3 * primeCountingConst) / Real.log (P : ℝ) := by
  classical
  let S : Finset ℕ := (Finset.Ico P (2 * P)).filter Nat.Prime
  have hsub : S ⊆ Nat.primesLE (2 * P) := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    have hpIco := Finset.mem_Ico.mp hpF.1
    have hpPrime : Nat.Prime p := hpF.2
    have hp_le : p ≤ 2 * P := le_of_lt hpIco.2
    exact (Nat.mem_primesLE).mpr ⟨hp_le, hpPrime⟩
  have hcardNat : S.card ≤ Nat.primeCounting (2 * P) := by
    have hcard := Finset.card_le_card hsub
    rwa [Nat.primesLE_card_eq_primeCounting] at hcard
  have hcardR : (S.card : ℝ) ≤ (Nat.primeCounting (2 * P) : ℝ) := by
    exact_mod_cast hcardNat
  have hpi : (Nat.primeCounting (2 * P) : ℝ) ≤
      primeCountingConst * (2 * (P : ℝ)) / Real.log (2 * (P : ℝ)) := by
    have h := primeCounting_le_const_div_log (2 * P) (by omega : 2 ≤ 2 * P)
    have hcast : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by norm_num
    simpa [hcast] using h
  have hPm_pos : 0 < ((P - 1 : ℕ) : ℝ) := by
    have h : 0 < P - 1 := by omega
    exact_mod_cast h
  have hsum_le : (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) ≤ (S.card : ℝ) / ((P - 1 : ℕ) : ℝ) := by
    calc
      (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) ≤ ∑ p ∈ S, 1 / ((P - 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1
        have hP_le_p : P ≤ p := hpIco.1
        have hpm_le : P - 1 ≤ p - 1 := by omega
        exact one_div_le_one_div_of_le hPm_pos (by exact_mod_cast hpm_le)
      _ = (S.card : ℝ) / ((P - 1 : ℕ) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [one_div, div_eq_mul_inv]
  have hcard_le_pi : (S.card : ℝ) ≤
      primeCountingConst * (2 * (P : ℝ)) / Real.log (2 * (P : ℝ)) := le_trans hcardR hpi
  have hdiv_le : (S.card : ℝ) / ((P - 1 : ℕ) : ℝ) ≤
      (primeCountingConst * (2 * (P : ℝ)) / Real.log (2 * (P : ℝ))) / ((P - 1 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_right hcard_le_pi (le_of_lt hPm_pos)
  have hfinal := prime_mass_bound_real P hP
  calc
    (∑ p ∈ S, 1 / ((p - 1 : ℕ) : ℝ)) ≤ (S.card : ℝ) / ((P - 1 : ℕ) : ℝ) := hsum_le
    _ ≤ (primeCountingConst * (2 * (P : ℝ)) / Real.log (2 * (P : ℝ))) /
          ((P - 1 : ℕ) : ℝ) := hdiv_le
    _ ≤ (3 * primeCountingConst) / Real.log (P : ℝ) := hfinal

/-- The same bound for the (possibly `x`-truncated) prime block used in `WmidBlock`. -/
lemma primeBlock_mass_le (P x : ℕ) (hP : 3 ≤ P) :
    (∑ p ∈ primeBlock P x, weight p) ≤ (3 * primeCountingConst) / Real.log (P : ℝ) := by
  classical
  have hsub : primeBlock P x ⊆ (Finset.Ico P (2 * P)).filter Nat.Prime := by
    intro p hp
    have hpF := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpF.1, hpF.2.2⟩
  calc
    (∑ p ∈ primeBlock P x, weight p) ≤
        ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime, weight p := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hp hp'
          exact weight_nonneg p
    _ = ∑ p ∈ (Finset.Ico P (2 * P)).filter Nat.Prime, 1 / ((p - 1 : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          rfl
    _ ≤ (3 * primeCountingConst) / Real.log (P : ℝ) := dyadic_prime_mass_le P hP

/-! ## 5. Conditional capstones -/

/-- **Generic column-block hypothesis.** There is a nonnegative block bound `B R k` for
`WmidBlock R (2^k) x` whose dyadic sum tends to `0` uniformly in `x`. -/
def HA_column_bound : Prop :=
  ∃ B : ℕ → ℕ → ℝ,
    (∀ R k, 0 ≤ B R k) ∧
    (∀ R x k, WmidBlock R (2 ^ k) x ≤ B R k) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      (∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1), B R k) ≤ ε)

/-- **The concrete column-route hypothesis.** The block bound is the column estimate
`sparseBound R (D R) * prime-block mass + R * exceptional mass`, with `D R` positive, and
the sum over the `O(log R)` dyadic blocks tends to `0` uniformly in `x`. -/
def HA_column_route : Prop :=
  ∃ D : ℕ → ℕ,
    (∀ R, 0 < D R) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      (∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
          (sparseBound R (D R) * (∑ p ∈ primeBlock (2 ^ k) (2 ^ (k + 1)), weight p)
            + (R : ℝ) * (∑ p ∈ (primeBlock (2 ^ k) (2 ^ (k + 1))).filter (fun p => p ∣ Nall (D R)), weight p))) ≤ ε)

/-- **Conditional capstone (generic).** If the column blocks satisfy `HA_column_bound`,
then `Wmid R x` tends to `0` uniformly in `x`. -/
theorem Wmid_uniformly_tends_to_zero_of_column_bound (h : HA_column_bound) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ ε := by
  classical
  rcases h with ⟨B, _hB_nonneg, hblock, hsum⟩
  intro ε hε
  rcases hsum ε hε with ⟨R₀, hR₀⟩
  refine ⟨R₀, ?_⟩
  intro R hR x
  calc
    Wmid R x = ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1),
        WmidBlock R (2 ^ k) x := Wmid_eq_sum_dyadic R x
    _ ≤ ∑ k ∈ Finset.range (Nat.log 2 (4 * R ^ 2) + 1), B R k := by
          apply Finset.sum_le_sum
          intro k hk
          exact hblock R x k
    _ ≤ ε := hR₀ R hR

/-- **Conditional capstone (concrete column route).** If the column estimate sum satisfies
`HA_column_route`, then `Wmid R x` tends to `0` uniformly in `x`. -/
theorem Wmid_uniformly_tends_to_zero_of_column_route (h : HA_column_route) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ ε := by
  classical
  rcases h with ⟨D, hDpos, hsum⟩
  refine Wmid_uniformly_tends_to_zero_of_column_bound ?_
  refine ⟨fun R k => sparseBound R (D R) * (∑ p ∈ primeBlock (2 ^ k) (2 ^ (k + 1)), weight p)
      + (R : ℝ) * (∑ p ∈ (primeBlock (2 ^ k) (2 ^ (k + 1))).filter (fun p => p ∣ Nall (D R)), weight p), ?_, ?_, ?_⟩
  · intro R k
    dsimp
    have hsparse_nonneg : 0 ≤ sparseBound R (D R) := by dsimp [sparseBound]; positivity
    have hsum1_nonneg : 0 ≤ ∑ p ∈ primeBlock (2 ^ k) (2 ^ (k + 1)), weight p := by
      exact Finset.sum_nonneg (by intro p hp; exact weight_nonneg p)
    have hsum2_nonneg : 0 ≤
        ∑ p ∈ (primeBlock (2 ^ k) (2 ^ (k + 1))).filter (fun p => p ∣ Nall (D R)), weight p := by
      exact Finset.sum_nonneg (by intro p hp; exact weight_nonneg p)
    have hR_nonneg : 0 ≤ (R : ℝ) := by positivity
    nlinarith [mul_nonneg hsparse_nonneg hsum1_nonneg, mul_nonneg hR_nonneg hsum2_nonneg]
  · intro R x k
    have hsplit := WmidBlock_le_non_exceptional_add_exceptional R (2 ^ k) x (D R) (hDpos R)
    have hsub1 : primeBlock (2 ^ k) x ⊆ primeBlock (2 ^ k) (2 ^ (k + 1)) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      have hpIco : p ∈ Finset.Ico (2 ^ k) (2 * 2 ^ k) := hpF.1
      have hpPrime : Nat.Prime p := hpF.2.2
      have hp_le : p ≤ 2 ^ (k + 1) := by
        have hp_lt : p < 2 * 2 ^ k := (Finset.mem_Ico.mp hpIco).2
        rw [← show 2 * 2 ^ k = 2 ^ (k + 1) by rw [pow_succ']]
        exact le_of_lt hp_lt
      exact Finset.mem_filter.mpr ⟨hpIco, ⟨hp_le, hpPrime⟩⟩
    have hle1 : (∑ p ∈ primeBlock (2 ^ k) x, weight p) ≤
        (∑ p ∈ primeBlock (2 ^ k) (2 ^ (k + 1)), weight p) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub1
        (by intro p hp hp'; exact weight_nonneg p)
    have hsub2 : (primeBlock (2 ^ k) x).filter (fun p => p ∣ Nall (D R)) ⊆
        (primeBlock (2 ^ k) (2 ^ (k + 1))).filter (fun p => p ∣ Nall (D R)) := by
      intro p hp
      have hpF := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hsub1 hpF.1, hpF.2⟩
    have hle2 : (∑ p ∈ (primeBlock (2 ^ k) x).filter (fun p => p ∣ Nall (D R)), weight p) ≤
        (∑ p ∈ (primeBlock (2 ^ k) (2 ^ (k + 1))).filter (fun p => p ∣ Nall (D R)), weight p) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub2
        (by intro p hp hp'; exact weight_nonneg p)
    have hsparse_nonneg : 0 ≤ sparseBound R (D R) := by dsimp [sparseBound]; positivity
    have hR_nonneg : 0 ≤ (R : ℝ) := by positivity
    have hle : sparseBound R (D R) * (∑ p ∈ primeBlock (2 ^ k) x, weight p)
          + (R : ℝ) * (∑ p ∈ (primeBlock (2 ^ k) x).filter (fun p => p ∣ Nall (D R)), weight p)
        ≤ sparseBound R (D R) * (∑ p ∈ primeBlock (2 ^ k) (2 ^ (k + 1)), weight p)
          + (R : ℝ) * (∑ p ∈ (primeBlock (2 ^ k) (2 ^ (k + 1))).filter (fun p => p ∣ Nall (D R)), weight p) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hle1 hsparse_nonneg)
        (mul_le_mul_of_nonneg_left hle2 hR_nonneg)
    exact le_trans hsplit hle
  · intro ε hε
    rcases hsum ε hε with ⟨R₀, hR₀⟩
    refine ⟨R₀, ?_⟩
    intro R hR
    exact hR₀ R hR

end

end Erdos291
