import Erdos291.BadSet
import Erdos291.GcdOneWeak
import Erdos291.SecondMoment
import Erdos291.MertensUpper
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Lemmas
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős #291 — the involution symmetry `r ↦ p - 1 - r` and the orbit decomposition

For an odd prime `p`, the involution `r ↦ p - 1 - r` pairs the bad set `E p ∩ [1, p - 2]`,
leaving only the midpoint `m := (p - 1) / 2` fixed.  Hence, writing

  * `T p := E p ∩ [1, m - 1]` for a choice of representatives of the *extra* symmetric pairs
    (the "lower half", characterized by `2 * r < p - 1`),
  * `w p := 1_{m ∈ E p}` for the midpoint indicator (so `w p ≤ 1`),

and recalling Wolstenholme's digit `p - 1 ∈ E p`, we get the exact identity

  `|E p| = 1 + w p + 2 * |T p|`.

Dividing by `p - 1` and summing over the primes gives (for odd primes `p ≥ 3`)

  `S x = Σ_{3 ≤ p ≤ x} 1/(p - 1) + Σ_{3 ≤ p ≤ x} w_p/(p - 1) + 2 · Aextra x`,

where `Aextra x := Σ_{p ≤ x} |T_p|/(p - 1)`.  (The prime `p = 2` is exceptional: `E 2 = ∅`,
`w 2 = 0` and `T 2 = ∅`, but `1/(2 - 1) = 1`; it is therefore excluded from the `1/(p - 1)`
sum, which is why the sum here runs over `3 ≤ p`.)

The first two sums are `O(log log x)` (Mertens plus `w_p ≤ 1`), so `HA_arith_weak`
(i.e. `S x = o(log x)`) is equivalent to `Aextra x = o(log x)`.

There are no unproved declarations in this file.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-! ## The orbit data: lower-half representatives, the midpoint indicator, and `Aextra` -/

/-- The lower-half "extra symmetric pair" representatives `T_p = E p ∩ [1, m-1]`, `m=(p-1)/2`.
Equivalently, `r ∈ T p` iff `r ∈ E p` and `2 * r < p - 1`. -/
def T (p : ℕ) : Finset ℕ :=
  (E p).filter fun r => 2 * r < p - 1

/-- The middle-digit indicator `w_p = 1` if `(p-1)/2 ∈ E p` else `0`. -/
def w (p : ℕ) : ℕ :=
  if (p - 1) / 2 ∈ E p then 1 else 0

/-- The extra-orbit count `A_extra(x) = Σ_{p≤x} |T_p|/(p-1)`. -/
noncomputable def Aextra (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)

/-! ## The prime `2` is exceptional -/

/-- `E 2` is empty: the only digit `1` has `(harmonic 1).num = 1`, not divisible by `2`. -/
lemma E_two : E 2 = ∅ := by
  native_decide

/-- `c 2 = 0`. -/
lemma c_two : c 2 = 0 := by
  unfold c
  rw [E_two]
  norm_num

/-- `T 2 = ∅`. -/
lemma T_two : T 2 = ∅ := by
  unfold T
  rw [E_two]
  simp

/-! ## The core decomposition `|E p| = 1 + w p + 2 · |T p|` -/

/-- For an odd prime `p`, `|E p| = 1 + w p + 2 · |T p|`.  The `1` is Wolstenholme's digit
`p - 1`, `w p` is the (possibly present) midpoint `(p - 1)/2`, and the two copies of `T p`
are the lower and upper halves of the involution orbit under `r ↦ p - 1 - r`. -/
theorem E_card_eq_one_add_w_add_two_mul_T_card (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (E p).card = 1 + w p + 2 * (T p).card := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  rcases hodd with ⟨k, rfl⟩
  -- From now on `p = 2 * k + 1`, so `p - 1 = 2 * k` and the midpoint is `k`.
  let upper : Finset ℕ := (E (2 * k + 1)).filter fun r => k < r ∧ r ≤ 2 * k - 1
  let mid : Finset ℕ := (E (2 * k + 1)).filter fun r => r = k
  let top : Finset ℕ := (E (2 * k + 1)).filter fun r => r = 2 * k
  have hE_subset : ∀ r, r ∈ E (2 * k + 1) → r ∈ Finset.Icc 1 (2 * k) := by
    intro r hr
    rw [E] at hr
    rw [Finset.mem_filter] at hr
    have hIcc : 1 ≤ r ∧ r ≤ (2 * k + 1) - 1 := Finset.mem_Icc.mp hr.1
    rw [Finset.mem_Icc]
    omega
  have hmem_symm : ∀ r, r ∈ E (2 * k + 1) → r ∈ Finset.Icc 1 (2 * k - 1) →
      2 * k - r ∈ E (2 * k + 1) := by
    intro r hrE hrIcc
    have h := (mem_E_iff_pm_sub (2 * k + 1) r hrIcc).1 hrE
    have hsub : (2 * k + 1) - 1 - r = 2 * k - r := by omega
    simpa [hsub] using h
  have hrE_of_T : ∀ r, r ∈ T (2 * k + 1) → r ∈ E (2 * k + 1) := by
    intro r hr; dsimp [T] at hr; exact (Finset.mem_filter.mp hr).1
  have hrlt_of_T : ∀ r, r ∈ T (2 * k + 1) → 2 * r < (2 * k + 1) - 1 := by
    intro r hr; dsimp [T] at hr; exact (Finset.mem_filter.mp hr).2
  have hbE_of_upper : ∀ b, b ∈ upper → b ∈ E (2 * k + 1) := by
    intro b hb; dsimp [upper] at hb; exact (Finset.mem_filter.mp hb).1
  have hb_gt_of_upper : ∀ b, b ∈ upper → k < b := by
    intro b hb; dsimp [upper] at hb; exact (Finset.mem_filter.mp hb).2.1
  have hb_le_of_upper : ∀ b, b ∈ upper → b ≤ 2 * k - 1 := by
    intro b hb; dsimp [upper] at hb; exact (Finset.mem_filter.mp hb).2.2
  have hw_eq : w (2 * k + 1) = if k ∈ E (2 * k + 1) then 1 else 0 := by
    unfold w
    simp
  -- Bijection between `T (2k+1)` (lower half) and `upper` (upper half) via `r ↦ 2k - r`.
  have hbij : (T (2 * k + 1)).card = upper.card := by
    refine Finset.card_bij (fun r _ => 2 * k - r) ?_ ?_ ?_
    · intro r hr
      dsimp [upper]
      rw [Finset.mem_filter]
      have hrE : r ∈ E (2 * k + 1) := hrE_of_T r hr
      have hrlt : 2 * r < (2 * k + 1) - 1 := hrlt_of_T r hr
      have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp (hE_subset r hrE)).1
      have hrIcc : r ∈ Finset.Icc 1 (2 * k - 1) := by
        rw [Finset.mem_Icc]
        exact ⟨hr_ge, by omega⟩
      constructor
      · exact hmem_symm r hrE hrIcc
      · constructor <;> omega
    · intro r₁ hr₁ r₂ hr₂ h
      have hlt₁ : 2 * r₁ < (2 * k + 1) - 1 := hrlt_of_T r₁ hr₁
      have hlt₂ : 2 * r₂ < (2 * k + 1) - 1 := hrlt_of_T r₂ hr₂
      omega
    · intro b hb
      refine ⟨2 * k - b, ?_, ?_⟩
      · dsimp [T]
        rw [Finset.mem_filter]
        have hbE : b ∈ E (2 * k + 1) := hbE_of_upper b hb
        have hb_gt : k < b := hb_gt_of_upper b hb
        have hb_le : b ≤ 2 * k - 1 := hb_le_of_upper b hb
        have hbIcc : b ∈ Finset.Icc 1 (2 * k - 1) := by
          rw [Finset.mem_Icc]
          exact ⟨by omega, hb_le⟩
        constructor
        · exact hmem_symm b hbE hbIcc
        · omega
      · have hb_le2 : b ≤ 2 * k := by
          have hle := hb_le_of_upper b hb
          omega
        omega
  have hmid_card : mid.card = w (2 * k + 1) := by
    dsimp [mid]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_ite_eq']
    simp [hw_eq]
  have htop_card : top.card = 1 := by
    dsimp [top]
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_ite_eq']
    have hmem : 2 * k ∈ E (2 * k + 1) := by
      have h := wolstenholme_mem_E (2 * k + 1) hp
      have hsub : (2 * k + 1) - 1 = 2 * k := by omega
      rwa [hsub] at h
    simp [hmem]
  have hdisj1 : Disjoint (T (2 * k + 1)) upper := by
    rw [Finset.disjoint_left]
    intro r hr hu
    have hrlt : 2 * r < (2 * k + 1) - 1 := hrlt_of_T r hr
    have hgt : k < r := hb_gt_of_upper r hu
    omega
  have hdisj2 : Disjoint (T (2 * k + 1) ∪ upper) mid := by
    rw [Finset.disjoint_left]
    intro r hr hm
    have heq : r = k := by
      dsimp [mid] at hm
      exact (Finset.mem_filter.mp hm).2
    rw [Finset.mem_union] at hr
    rcases hr with hl | hu
    · have hrlt : 2 * r < (2 * k + 1) - 1 := hrlt_of_T r hl
      omega
    · have hgt : k < r := hb_gt_of_upper r hu
      omega
  have hdisj3 : Disjoint (T (2 * k + 1) ∪ upper ∪ mid) top := by
    rw [Finset.disjoint_left]
    intro r hr ht
    have heq : r = 2 * k := by
      dsimp [top] at ht
      exact (Finset.mem_filter.mp ht).2
    rw [Finset.mem_union, Finset.mem_union] at hr
    rcases hr with hl | hm
    · rcases hl with hl | hu
      · have hrlt : 2 * r < (2 * k + 1) - 1 := hrlt_of_T r hl
        omega
      · have hle : r ≤ 2 * k - 1 := hb_le_of_upper r hu
        omega
    · have heq2 : r = k := by
        dsimp [mid] at hm
        exact (Finset.mem_filter.mp hm).2
      omega
  have hE_eq : E (2 * k + 1) = T (2 * k + 1) ∪ upper ∪ mid ∪ top := by
    ext r
    dsimp [upper, mid, top, T]
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hrE
      have hIcc : r ∈ Finset.Icc 1 (2 * k) := hE_subset r hrE
      have hle : r ≤ 2 * k := (Finset.mem_Icc.mp hIcc).2
      by_cases hlt : r < k
      · exact Or.inl (Or.inl (Or.inl ⟨hrE, by omega⟩))
      · by_cases heq : r = k
        · exact Or.inl (Or.inr ⟨hrE, heq⟩)
        · have hgt : k < r := by omega
          by_cases heq2 : r = 2 * k
          · exact Or.inr ⟨hrE, heq2⟩
          · have hle2 : r ≤ 2 * k - 1 := by omega
            exact Or.inl (Or.inl (Or.inr ⟨hrE, hgt, hle2⟩))
    · intro h
      rcases h with h | h
      · rcases h with h | h
        · rcases h with h | h
          · exact h.1
          · exact h.1
        · exact h.1
      · exact h.1
  calc
    (E (2 * k + 1)).card = (T (2 * k + 1) ∪ upper ∪ mid ∪ top).card := by
      rw [hE_eq]
    _ = (T (2 * k + 1)).card + upper.card + mid.card + top.card := by
      rw [Finset.card_union_of_disjoint hdisj3]
      rw [Finset.card_union_of_disjoint hdisj2]
      rw [Finset.card_union_of_disjoint hdisj1]
    _ = (T (2 * k + 1)).card + (T (2 * k + 1)).card + w (2 * k + 1) + 1 := by
      rw [← hbij, hmid_card, htop_card]
    _ = 1 + w (2 * k + 1) + 2 * (T (2 * k + 1)).card := by omega

/-- The midpoint indicator is at most one. -/
theorem w_le_one (p : ℕ) : w p ≤ 1 := by
  unfold w
  by_cases h : (p - 1) / 2 ∈ E p <;> simp [h]

/-! ## The density identity `c p = 1/(p-1) + w p/(p-1) + 2|T p|/(p-1)` -/

/-- For an odd prime `p`, the real-cast density identity. -/
theorem c_eq_add_inv_pred_add_w_add_two_mul_T (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (c p : ℝ) = (1 / ((p - 1 : ℕ) : ℝ)) + (w p : ℝ) / ((p - 1 : ℕ) : ℝ)
      + 2 * ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  have hc : (c p : ℝ) = ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    unfold c
    rw [Rat.cast_div]
    norm_num
    rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ p)]
    norm_num
  rw [hc]
  rw [E_card_eq_one_add_w_add_two_mul_T_card p hp]
  push_cast
  simp only [add_div]

/-! ## The summed identity `S x = Σ 1/(p-1) + Σ w_p/(p-1) + 2 · Aextra x` -/

/-- Restricting a prime-indexed sum from `p ≥ 2` to `p ≥ 3` is harmless when the `p = 2`
term vanishes. -/
lemma sum_Icc2_prime_eq_sum_Icc3_prime (f : ℕ → ℝ) (h2 : f 2 = 0) (x : ℕ) :
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, f p) =
      ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, f p := by
  symm
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    constructor
    · rw [Finset.mem_Icc]
      have hpIcc : 3 ≤ p ∧ p ≤ x := Finset.mem_Icc.mp hp.1
      omega
    · exact hp.2
  · intro p hp hnot
    rw [Finset.mem_filter] at hp
    have hpP : Nat.Prime p := hp.2
    have hpIcc : 2 ≤ p ∧ p ≤ x := Finset.mem_Icc.mp hp.1
    have hnot3 : ¬ 3 ≤ p := by
      intro h3
      apply hnot
      rw [Finset.mem_filter]
      exact ⟨by rw [Finset.mem_Icc]; exact ⟨h3, hpIcc.2⟩, hpP⟩
    have hp2 : p = 2 := by omega
    subst p
    exact h2

/-- `S x` equals the same sum restricted to odd primes `p ≥ 3`. -/
lemma S_eq_sum_c_Icc3 (x : ℕ) :
    S x = ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (c p : ℝ) := by
  unfold S
  simpa using sum_Icc2_prime_eq_sum_Icc3_prime (fun p => (c p : ℝ))
    (by simp [c_two] : ((c 2 : ℚ) : ℝ) = 0) x

/-- `Aextra x` equals the same sum restricted to odd primes `p ≥ 3`. -/
lemma Aextra_eq_sum_Icc3 (x : ℕ) :
    Aextra x = ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  unfold Aextra
  have h2 : ((T 2).card : ℝ) / ((2 - 1 : ℕ) : ℝ) = 0 := by
    rw [T_two]
    norm_num
  simpa using sum_Icc2_prime_eq_sum_Icc3_prime
    (fun p => ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) h2 x

/-- The summed decomposition of `S x` over odd primes `p ≥ 3`. -/
theorem S_eq_sum_inv_pred_add_sum_w_add_two_mul_Aextra (x : ℕ) :
    S x = (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
      + (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ))
      + 2 * Aextra x := by
  rw [S_eq_sum_c_Icc3, Aextra_eq_sum_Icc3]
  calc
    (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (c p : ℝ))
        = ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime,
            ((1 / ((p - 1 : ℕ) : ℝ)) + (w p : ℝ) / ((p - 1 : ℕ) : ℝ)
              + 2 * ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
            exact @c_eq_add_inv_pred_add_w_add_two_mul_T p ⟨hpP⟩ hp3
    _ = (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
          + (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ))
          + 2 * (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, ((T p).card : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            congr 1
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            rw [mul_div_assoc]

/-! ## Asymptotic control of the `O(log log x)` pieces -/

/-- `(1 + log log x) / log x → 0` along `ℕ`. -/
lemma one_add_loglog_div_log_tendsto_zero :
    Tendsto (fun x : ℕ => (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℕ => (1 : ℝ) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    have h1' : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    exact (h1'.div_atTop Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    have hlogdiv : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    exact ((hlogdiv.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop)
  simpa [add_div] using h1.add h2

/-- `Σ_{p ≤ x} 1/(p - 1) = o(log x)` (the `O(log log x)` Mertens bound divided by `log x`). -/
lemma sum_inv_pred_div_log_tendsto_zero :
    Tendsto (fun x : ℕ =>
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        / Real.log (x : ℝ)) atTop (𝓝 0) := by
  rcases sum_inv_pred_le_loglog with ⟨C, hCpos, hC⟩
  have hCdiv : Tendsto (fun x : ℕ =>
      C * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ)) atTop (𝓝 0) := by
    have h := one_add_loglog_div_log_tendsto_zero.const_mul C
    simpa [mul_div_assoc] using h
  have hnonneg : ∀ᶠ x : ℕ in atTop, (0 : ℝ) ≤
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hsum : 0 ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)) := by
      refine Finset.sum_nonneg ?_
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
    exact div_nonneg hsum (le_of_lt hlog)
  have hupper : ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
        ≤ C * (1 + Real.log (Real.log (x : ℝ))) / Real.log (x : ℝ) := by
    filter_upwards [hC, eventually_gt_atTop (1 : ℕ)] with x hCx hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
    exact div_le_div_of_nonneg_right hCx (le_of_lt hlog)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hCdiv hnonneg hupper

/-- `Σ_{3 ≤ p ≤ x} 1/(p - 1) ≤ Σ_{p ≤ x} 1/(p - 1)`. -/
lemma sum_inv_pred_Icc3_le_sum_inv_pred_Icc2 (x : ℕ) :
    (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
      ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    constructor
    · rw [Finset.mem_Icc]
      have hpIcc : 3 ≤ p ∧ p ≤ x := Finset.mem_Icc.mp hp.1
      omega
    · exact hp.2
  · intro p _ _
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)

/-- `Σ_{3 ≤ p ≤ x} 1/(p - 1) = o(log x)`. -/
lemma sum_inv_pred_Icc3_div_log_tendsto_zero :
    Tendsto (fun x : ℕ =>
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        / Real.log (x : ℝ)) atTop (𝓝 0) := by
  have hnonneg : ∀ᶠ x : ℕ in atTop, (0 : ℝ) ≤
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hsum : 0 ≤ ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)) := by
      refine Finset.sum_nonneg ?_
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
    exact div_nonneg hsum (le_of_lt hlog)
  have hupper : ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
        ≤ (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
    exact div_le_div_of_nonneg_right (sum_inv_pred_Icc3_le_sum_inv_pred_Icc2 x) (le_of_lt hlog)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    sum_inv_pred_div_log_tendsto_zero hnonneg hupper

/-- The `w`-weighted sum is nonnegative. -/
lemma sum_w_nonneg (x : ℕ) :
    0 ≤ ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  refine Finset.sum_nonneg ?_
  intro p hp
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `Σ w_p/(p - 1) ≤ Σ 1/(p - 1)` over the odd primes (using `w_p ≤ 1`). -/
lemma sum_w_le_sum_inv_pred (x : ℕ) :
    (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ))
      ≤ ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)) := by
  refine Finset.sum_le_sum ?_
  intro p hp
  have hw : (w p : ℝ) ≤ 1 := by exact_mod_cast (w_le_one p)
  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hpos : 0 < ((p - 1 : ℕ) : ℝ) := by
    have : 0 < p - 1 := by omega
    exact_mod_cast this
  exact div_le_div_of_nonneg_right hw (le_of_lt hpos)

/-- `Σ_{3 ≤ p ≤ x} w_p/(p - 1) = o(log x)`. -/
lemma sum_w_div_log_tendsto_zero :
    Tendsto (fun x : ℕ =>
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ))
        / Real.log (x : ℝ)) atTop (𝓝 0) := by
  have hnonneg : ∀ᶠ x : ℕ in atTop, (0 : ℝ) ≤
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
    exact div_nonneg (sum_w_nonneg x) (le_of_lt hlog)
  have hupper : ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ)
        ≤ (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))
    exact div_le_div_of_nonneg_right (sum_w_le_sum_inv_pred x) (le_of_lt hlog)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    sum_inv_pred_Icc3_div_log_tendsto_zero hnonneg hupper

/-! ## The main equivalence `HA_arith_weak ↔ Aextra x = o(log x)` -/

/-- `HA_arith_weak` (`S x = o(log x)`) is equivalent to `Aextra x = o(log x)`, up to the
unconditional `O(log log x)` terms. -/
theorem HA_arith_weak_iff_Aextra_o_log :
    HA_arith_weak ↔ Tendsto (fun x => Aextra x / Real.log (x : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro hS
    have hB : Tendsto (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ))
        atTop (𝓝 0) := sum_inv_pred_Icc3_div_log_tendsto_zero
    have hW : Tendsto (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ))
        atTop (𝓝 0) := sum_w_div_log_tendsto_zero
    have hdiff : Tendsto (fun x : ℕ => S x / Real.log (x : ℝ)
        - (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
        - (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ))
        atTop (𝓝 0) := by
      simpa using (hS.sub hB).sub hW
    have hEq : (fun x : ℕ => S x / Real.log (x : ℝ)
        - (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
        - (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ))
        =ᶠ[atTop] fun x : ℕ => 2 * (Aextra x / Real.log (x : ℝ)) := by
      filter_upwards [] with x
      have hS4 := S_eq_sum_inv_pred_add_sum_w_add_two_mul_Aextra x
      rw [hS4]
      ring_nf
    have htwo : Tendsto (fun x : ℕ => 2 * (Aextra x / Real.log (x : ℝ))) atTop (𝓝 0) :=
      hdiff.congr' hEq
    have hfinal : Tendsto (fun x : ℕ => Aextra x / Real.log (x : ℝ)) atTop (𝓝 0) := by
      have hscaled : Tendsto (fun x : ℕ => (1 / 2 : ℝ) * (2 * (Aextra x / Real.log (x : ℝ))))
          atTop (𝓝 0) := by
        simpa using htwo.const_mul (1 / 2 : ℝ)
      refine hscaled.congr' ?_
      filter_upwards [] with x
      ring
    exact hfinal
  · intro hA
    have hB : Tendsto (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ))
        atTop (𝓝 0) := sum_inv_pred_Icc3_div_log_tendsto_zero
    have hW : Tendsto (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ))
        atTop (𝓝 0) := sum_w_div_log_tendsto_zero
    have htwoA : Tendsto (fun x : ℕ => 2 * (Aextra x / Real.log (x : ℝ))) atTop (𝓝 0) := by
      simpa using hA.const_mul (2 : ℝ)
    have hsum : Tendsto (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
          + (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ)
          + 2 * (Aextra x / Real.log (x : ℝ))) atTop (𝓝 0) := by
      simpa using (hB.add hW).add htwoA
    have hEq : (fun x : ℕ =>
        (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) / Real.log (x : ℝ)
          + (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (w p : ℝ) / ((p - 1 : ℕ) : ℝ)) / Real.log (x : ℝ)
          + 2 * (Aextra x / Real.log (x : ℝ))) =ᶠ[atTop]
        fun x : ℕ => S x / Real.log (x : ℝ) := by
      filter_upwards [] with x
      have hS4 := S_eq_sum_inv_pred_add_sum_w_add_two_mul_Aextra x
      rw [hS4]
      ring_nf
    exact hsum.congr' hEq

end Erdos291
