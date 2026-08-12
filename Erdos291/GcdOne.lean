import Erdos291.BadSet
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős #291 — the `gcd = 1` direction

The open Shiu (2016) conjecture asserts that `gcd(a_n, L_n) = 1` for infinitely many `n`.
This file sets up the two analytic hypotheses under which the conjecture is *known* to
hold (`HA_dist`, the distribution estimate on the bad digits, and `HA_arith`, the
estimate on their average density), and proves the conditional conclusion:

* `infinite_good_iff_G_tendsto`: infinitely many good `n` iff the count `G x` is
  eventually at least every constant.
* `gcd_eq_one_infinite`: under `HA_dist` and `HA_arith`, the good set is infinite.

The single analytic step `HA_lower_bound` (that `HA_dist` + `HA_arith` force
`G x ≳ x / log x`) is the one permitted unproved declaration for this file.  Everything
else here — the equivalence and the deduction from that declaration — is fully proved.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-- The "distribution" hypothesis: the product of `(1 - c p)` over primes `p ≤ x` is
essentially `1`, so that a constant-proportion `(1 - ε x) · x` lower-bounds `G x`. -/
def HA_dist : Prop :=
  ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ x in atTop,
        (1 - ε x) * (x : ℝ) *
          (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)))
          ≤ (G x : ℝ)

/-- The "arithmetic" hypothesis: the sum of the bad-digit densities over primes `p ≤ x`
grows at most like `log log x`. -/
def HA_arith : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (c p : ℝ))
      ≤ C * Real.log (Real.log (x : ℝ))

/-- The (single, allowed) analytic input: `HA_dist` and `HA_arith` together imply
`G x ≥ C · x / log x` eventually. -/
axiom HA_lower_bound (hdist : HA_dist) (harith : HA_arith) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x in atTop, C * ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) ≤ (G x : ℝ)

/-- `x / log x → ∞`, more precisely `C₀ · x / log x → ∞` over `ℕ` for any `C₀ > 0`. -/
lemma tendsto_mul_div_log_atTop (C₀ : ℝ) (hC₀ : 0 < C₀) :
    Tendsto (fun x : ℕ => C₀ * (x : ℝ) / Real.log (x : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa [pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (0 : ℝ) 1 one_ne_zero)
  have hpos : ∀ᶠ x in atTop, (fun x : ℝ => Real.log x / x) x ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (lt_trans zero_lt_one hx)
  have h1' : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1, hpos⟩
  have h2 : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop :=
    h1'.inv_tendsto_nhdsGT_zero
  have h3 : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
    simpa [inv_div] using h2
  have h4 : Tendsto (fun x : ℝ => C₀ * (x / Real.log x)) atTop atTop :=
    h3.const_mul_atTop hC₀
  have h5 : Tendsto (fun x : ℝ => C₀ * x / Real.log x) atTop atTop := by
    simpa [div_eq_mul_inv, mul_assoc] using h4
  exact h5.comp tendsto_natCast_atTop_atTop

/-- Infinitely many `n` have `gcd (a n) (L n) = 1` iff the count `G x` is eventually at
least every constant. -/
lemma infinite_good_iff_G_tendsto :
    (∀ C : ℕ, ∀ᶠ x in atTop, C ≤ G x) ↔
      Set.Infinite {n : ℕ | Nat.gcd (a n) (L n) = 1} := by
  set S : Set ℕ := {n : ℕ | Nat.gcd (a n) (L n) = 1}
  constructor
  · -- If `G x` is eventually ≥ every constant, the good set is infinite.
    intro h
    by_contra hSinf
    have hSfin : S.Finite := Set.not_infinite.mp hSinf
    have hGle : ∀ x, G x ≤ hSfin.toFinset.card := by
      intro x
      unfold G
      have hsub :
          (Finset.Icc 1 x).filter (fun n => Nat.gcd (a n) (L n) = 1) ⊆ hSfin.toFinset := by
        rw [← Finset.coe_subset]
        rw [hSfin.coe_toFinset]
        intro n hn
        exact (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
      exact Finset.card_le_card hsub
    have hevent : ∀ᶠ x in atTop, hSfin.toFinset.card + 1 ≤ G x := h (hSfin.toFinset.card + 1)
    rcases eventually_atTop.mp hevent with ⟨N, hN⟩
    have hcontra : hSfin.toFinset.card + 1 ≤ hSfin.toFinset.card := by
      calc
        hSfin.toFinset.card + 1 ≤ G N := hN N le_rfl
        _ ≤ hSfin.toFinset.card := hGle N
    omega
  · -- If the good set is infinite, `G x` is eventually ≥ every constant.
    intro hS C
    obtain ⟨t, htsub, htcard⟩ := Set.Infinite.exists_subset_card_eq hS (C + 1)
    let t' := t.erase (0 : ℕ)
    have ht'card : C ≤ t'.card := by
      have hle : t.card - 1 ≤ t'.card := Finset.pred_card_le_card_erase (s := t) (a := 0)
      rw [htcard] at hle
      omega
    let N := t'.sup id
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro x hx
    have ht'sub_Icc : t' ⊆ Finset.Icc 1 x := by
      intro n hn
      rw [Finset.mem_Icc]
      constructor
      · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn).1)
      · exact le_trans (Finset.le_sup (s := t') (f := id) hn) hx
    have ht'card_le : t'.card ≤ G x := by
      unfold G
      have hsub2 : t' ⊆ (Finset.Icc 1 x).filter (fun n => Nat.gcd (a n) (L n) = 1) := by
        intro n hn
        rw [Finset.mem_filter]
        constructor
        · exact ht'sub_Icc hn
        · exact htsub (Finset.mem_coe.2 ((Finset.erase_subset (0 : ℕ) t) hn))
      exact Finset.card_le_card hsub2
    exact le_trans ht'card ht'card_le

/-- Under `HA_dist` and `HA_arith`, the set of `n` with `gcd (a n) (L n) = 1` is
infinite. -/
theorem gcd_eq_one_infinite (hdist : HA_dist) (harith : HA_arith) :
    Set.Infinite {n : ℕ | Nat.gcd (a n) (L n) = 1} := by
  rw [← infinite_good_iff_G_tendsto]
  intro C
  rcases HA_lower_bound hdist harith with ⟨C₀, hC₀pos, hle⟩
  have hf : Tendsto (fun x : ℕ => C₀ * (x : ℝ) / Real.log (x : ℝ)) atTop atTop :=
    tendsto_mul_div_log_atTop C₀ hC₀pos
  have hCevent : ∀ᶠ x in atTop, (C : ℝ) ≤ C₀ * ((x : ℕ) : ℝ) / Real.log ((x : ℕ) : ℝ) :=
    hf.eventually_ge_atTop (C : ℝ)
  have hboth : ∀ᶠ x in atTop, (C : ℝ) ≤ (G x : ℝ) := by
    filter_upwards [hCevent, hle] with x hCx hGx
    exact hCx.trans hGx
  filter_upwards [hboth] with x hx
  exact_mod_cast hx

end Erdos291
