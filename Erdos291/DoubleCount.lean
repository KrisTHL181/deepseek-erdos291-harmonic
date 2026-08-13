import Erdos291.BadSet
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Prod

/-!
# Erdős #291 — the double-count identity, the parity law, and finite tables

This file establishes three results about the "bad digit" sets `E p` introduced in
`BadSet.lean`:

* `sum_E_card_eq_double_count`: the total number of bad digits over all primes `p ≤ x`
  equals the number of pairs `(r, p)` with `r < p ≤ x` and `p` dividing the numerator of
  `H_r`.  This is the double-counting identity that underlies the analytic step: on the
  left one sums `|E p|` over primes, on the right one counts, for each base-`p` "leading
  digit" `r`, the primes `p` for which `r` is bad.

* `E_card_odd_iff_mid_not_mem`: for an odd prime `p`, the cardinality `|E p|` is odd
  exactly when the middle digit `(p - 1) / 2` is *not* bad.  This is the "Wieferich
  fixed-point" parity law: the involution `r ↦ p - 1 - r` pairs off all of `E p` except
  the Wolstenholme digit `p - 1` and (possibly) the middle digit.

* `E_eleven`, `E_twentynine`, `E_hundred_nine`, `E_thousand_ninety_three`: concrete
  tables, checked by `native_decide`.

The first two are fully proved; the tables are decided by computation.
-/

open scoped BigOperators

namespace Erdos291

/-! ## The bridge: `r ∈ E p` iff `p ∣ (harmonic r).num` -/

/-- Unfolding `E`: `r ∈ E p` iff `r ∈ Icc 1 (p - 1)` and `p` divides the numerator of
`H_r`. -/
lemma mem_E_iff_mem_Icc_and_dvd (p r : ℕ) :
    r ∈ E p ↔ r ∈ Finset.Icc 1 (p - 1) ∧ (p : ℤ) ∣ (harmonic r).num := by
  rw [E, Finset.mem_filter]

/-- For a prime `p` and `1 ≤ r < p`, the bad-digit condition `r ∈ E p` is equivalent to
`p` dividing the numerator of `H_r` (the membership of `r` in `Icc 1 (p - 1)` is
automatic). -/
lemma mem_E_iff_dvd_num (p r : ℕ) (_hp : Nat.Prime p) (h1r : 1 ≤ r) (hrp : r < p) :
    r ∈ E p ↔ (p : ℤ) ∣ (harmonic r).num := by
  rw [mem_E_iff_mem_Icc_and_dvd]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Finset.mem_Icc.mpr ⟨h1r, by omega⟩, h⟩

/-- Every element of `E p` is at least `1`. -/
lemma mem_E_ge_one (p r : ℕ) (h : r ∈ E p) : 1 ≤ r := by
  exact (Finset.mem_Icc.mp ((mem_E_iff_mem_Icc_and_dvd p r).mp h).1).1

/-- Every element of `E p` is at most `p - 1`. -/
lemma mem_E_le_pred (p r : ℕ) (h : r ∈ E p) : r ≤ p - 1 := by
  exact (Finset.mem_Icc.mp ((mem_E_iff_mem_Icc_and_dvd p r).mp h).1).2

/-! ## Theorem 1: the double-count identity -/

/-- The total number of bad digits over all primes `p ≤ x` equals the number of pairs
`(r, p)` with `r < p ≤ x` and `p` dividing the numerator of `H_r`.  The bijection is
`(p, r) ↔ (r, p)` between the two pair sets; the `x = 0` boundary is covered because both
sides are then empty. -/
theorem sum_E_card_eq_double_count (x : ℕ) :
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (E p).card) =
      ∑ r ∈ Finset.Icc 1 (x - 1),
        ((Finset.Ico (r + 1) (x + 1)).filter
          (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)).card := by
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  refine Finset.card_bij (fun a _ => (⟨a.2, a.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_
  · -- membership: `(p, r)` with `p ∈ P` and `r ∈ E p` maps to `(r, p)` with `r ∈ R`,
    -- `p` prime and `p ∣ num H_r`
    intro a ha
    rw [Finset.mem_sigma] at ha ⊢
    rcases ha with ⟨haP, harE⟩
    rw [Finset.mem_filter] at haP
    rcases haP with ⟨haIcc, haPrime⟩
    have h2p : 2 ≤ a.1 := (Finset.mem_Icc.mp haIcc).1
    have hpx : a.1 ≤ x := (Finset.mem_Icc.mp haIcc).2
    have h1r : 1 ≤ a.2 := mem_E_ge_one a.1 a.2 harE
    have hrp : a.2 ≤ a.1 - 1 := mem_E_le_pred a.1 a.2 harE
    have hdvd : (a.1 : ℤ) ∣ (harmonic a.2).num := (mem_E_iff_mem_Icc_and_dvd a.1 a.2).mp harE |>.2
    constructor
    · rw [Finset.mem_Icc]
      constructor
      · exact h1r
      · change a.2 ≤ x - 1
        omega
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Ico]
        constructor
        · change a.2 + 1 ≤ a.1
          omega
        · change a.1 < x + 1
          omega
      · exact ⟨haPrime, hdvd⟩
  · -- injectivity: `(a.2, a.1) = (a.2', a.1')` forces `a = a'`
    intro a₁ ha₁ a₂ ha₂ h
    rcases a₁ with ⟨p₁, r₁⟩
    rcases a₂ with ⟨p₂, r₂⟩
    have hfst : r₁ = r₂ := congrArg Sigma.fst h
    have hsnd : p₁ = p₂ := congrArg Sigma.snd h
    subst r₂
    subst p₂
    rfl
  · -- surjectivity: every `(r, p)` with `r ∈ R`, `p` prime, `r < p ≤ x`, `p ∣ num H_r`
    -- comes from `(p, r)`
    intro b hb
    rw [Finset.mem_sigma] at hb
    rcases hb with ⟨hbR, hbQ⟩
    rw [Finset.mem_filter] at hbQ
    rcases hbQ with ⟨hbIco, hbPred⟩
    have hR1 : 1 ≤ b.1 := (Finset.mem_Icc.mp hbR).1
    have hR2 : b.1 ≤ x - 1 := (Finset.mem_Icc.mp hbR).2
    have hIco1 : b.1 + 1 ≤ b.2 := (Finset.mem_Ico.mp hbIco).1
    have hIco2 : b.2 < x + 1 := (Finset.mem_Ico.mp hbIco).2
    have hbPrime : Nat.Prime b.2 := hbPred.1
    have hbdvd : (b.2 : ℤ) ∣ (harmonic b.1).num := hbPred.2
    have hrE : b.1 ∈ E b.2 :=
      (mem_E_iff_dvd_num b.2 b.1 hbPrime hR1 (by omega)).mpr hbdvd
    refine ⟨(⟨b.2, b.1⟩ : Sigma fun _ : ℕ => ℕ), ?_, ?_⟩
    · rw [Finset.mem_sigma]
      constructor
      · rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨?_, ?_⟩, hbPrime⟩
        · change 2 ≤ b.2
          omega
        · change b.2 ≤ x
          omega
      · exact hrE
    · rfl

/-! ## Theorem 2: the parity law -/

/-- `0` is never a bad digit. -/
lemma zero_not_mem_E (p : ℕ) : 0 ∉ E p := by
  intro h
  exact (Nat.not_succ_le_zero 0 (mem_E_ge_one p 0 h)).elim

/-- For an odd `p`, `p - 1 = 2 * ((p - 1) / 2)`. -/
lemma sub_one_eq_two_mul_div_two_sub_one {p : ℕ} (hodd : Odd p) :
    p - 1 = 2 * ((p - 1) / 2) := by
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  have h1 : 2 * k + 1 - 1 = 2 * k := by omega
  have h2 : (2 * k) / 2 = k := Nat.mul_div_right k (by decide : 0 < 2)
  rw [h1, h2]

/-- Removing the Wolstenholme digit `p - 1`, the remaining bad digits are `2·|T|` (the
pairs `{r, p - 1 - r}` with `r < (p-1)/2`) plus possibly the middle digit `(p-1)/2`. -/
lemma card_erase_pred (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((E p).erase (p - 1)).card =
      2 * ((E p).filter (fun r => r < (p - 1) / 2)).card
        + (if (p - 1) / 2 ∈ E p then 1 else 0) := by
  let mid : ℕ := (p - 1) / 2
  let T : Finset ℕ := (E p).filter (fun r => r < mid)
  let D : Finset (ℕ × Bool) :=
    T.product ({false, true} : Finset Bool)
      ∪ (if mid ∈ E p then ({(0, true)} : Finset (ℕ × Bool)) else ∅)
  let f : ℕ → ℕ × Bool := fun r =>
    if r < mid then (r, false)
    else if r = mid then (0, true)
    else (p - 1 - r, true)
  have hpodd : Odd p := Nat.Prime.odd_of_ne_two (Fact.out : Nat.Prime p) (by omega : p ≠ 2)
  have h2mid : p - 1 = 2 * mid := by
    dsimp [mid]
    exact sub_one_eq_two_mul_div_two_sub_one hpodd
  have hmid_ge : 1 ≤ mid := by omega
  have hmid_le : mid ≤ p - 2 := by omega
  have hmid_lt_pred : mid < p - 1 := by omega
  have hf_lt (a : ℕ) (ha : a < mid) : f a = (a, false) := by
    dsimp [f]
    simp [ha]
  have hf_eq (a : ℕ) (ha : a = mid) : f a = (0, true) := by
    dsimp [f]
    simp [ha]
  have hf_gt (a : ℕ) (hge : mid ≤ a) (hne : a ≠ mid) : f a = (p - 1 - a, true) := by
    dsimp [f]
    have hlt : ¬ a < mid := Nat.not_lt.mpr hge
    simp [hlt, hne]
  have hprodCard : (T.product ({false, true} : Finset Bool)).card = 2 * T.card := by
    calc
      (T.product ({false, true} : Finset Bool)).card
          = T.card * ({false, true} : Finset Bool).card :=
              Finset.card_product T ({false, true} : Finset Bool)
      _ = T.card * 2 := by
          rw [show ({false, true} : Finset Bool).card = 2 by native_decide]
      _ = 2 * T.card := by omega
  have hcardD : D.card = 2 * T.card + (if mid ∈ E p then 1 else 0) := by
    dsimp only [D]
    by_cases hmidE : mid ∈ E p
    · rw [ite_eq_left hmidE]
      rw [ite_eq_left hmidE]
      have hdisj : Disjoint (T.product ({false, true} : Finset Bool))
          ({(0, true)} : Finset (ℕ × Bool)) := by
        rw [Finset.disjoint_left]
        intro b hb hb'
        rw [Finset.mem_singleton] at hb'
        have hbT : b.1 ∈ T := (Finset.mem_product.mp hb).1
        have hb0 : b.1 = 0 := congrArg Prod.fst hb'
        rw [hb0] at hbT
        dsimp [T] at hbT
        exact zero_not_mem_E p (Finset.mem_filter.mp hbT).1
      rw [Finset.card_union_of_disjoint hdisj]
      rw [hprodCard, Finset.card_singleton]
    · rw [ite_eq_right hmidE]
      rw [ite_eq_right hmidE]
      have hdisj : Disjoint (T.product ({false, true} : Finset Bool))
          (∅ : Finset (ℕ × Bool)) := by
        rw [Finset.disjoint_left]
        intro b _ hb
        simp at hb
      rw [Finset.card_union_of_disjoint hdisj]
      rw [hprodCard, Finset.card_empty]
  have hbij : ((E p).erase (p - 1)).card = D.card := by
    refine Finset.card_bij (fun a _ => f a) ?_ ?_ ?_
    · -- membership
      intro a ha
      rw [Finset.mem_erase] at ha
      rcases ha with ⟨hanot, haE⟩
      have h1a : 1 ≤ a := mem_E_ge_one p a haE
      have ha_le_pred : a ≤ p - 1 := mem_E_le_pred p a haE
      have ha_le_p2 : a ≤ p - 2 := by omega
      by_cases hlt : a < mid
      · rw [hf_lt a hlt]
        rw [Finset.mem_union]
        left
        exact Finset.mk_mem_product
          (by dsimp [T]; rw [Finset.mem_filter]; exact ⟨haE, hlt⟩)
          (by simp)
      · by_cases heq : a = mid
        · rw [hf_eq a heq]
          rw [Finset.mem_union]
          right
          simp [show mid ∈ E p by rw [← heq]; exact haE]
        · have hge : mid ≤ a := Nat.le_of_not_gt hlt
          rw [hf_gt a hge heq]
          rw [Finset.mem_union]
          left
          exact Finset.mk_mem_product
            (by
              dsimp [T]
              rw [Finset.mem_filter]
              constructor
              · exact (mem_E_iff_pm_sub p a (by rw [Finset.mem_Icc]; exact ⟨h1a, ha_le_p2⟩)).mp haE
              · rw [h2mid]
                omega)
            (by simp)
    · -- injectivity
      intro a₁ ha₁ a₂ ha₂ h
      have ha₁E : a₁ ∈ E p := (Finset.mem_erase.mp ha₁).2
      have ha₂E : a₂ ∈ E p := (Finset.mem_erase.mp ha₂).2
      have ha₁_le : a₁ ≤ p - 1 := mem_E_le_pred p a₁ ha₁E
      have ha₂_le : a₂ ≤ p - 1 := mem_E_le_pred p a₂ ha₂E
      by_cases hlt₁ : a₁ < mid
      · have hf1 : f a₁ = (a₁, false) := hf_lt a₁ hlt₁
        have hsnd₂ : (f a₂).2 = false := by
          have : (f a₁).2 = (f a₂).2 := congrArg Prod.snd h
          simpa [hf1] using this
        have hlt₂ : a₂ < mid := by
          by_contra hnot
          have hge₂ : mid ≤ a₂ := Nat.le_of_not_gt hnot
          by_cases heq₂ : a₂ = mid
          · have : (f a₂).2 = true := by rw [hf_eq a₂ heq₂]
            cases (this.symm.trans hsnd₂)
          · have : (f a₂).2 = true := by rw [hf_gt a₂ hge₂ heq₂]
            cases (this.symm.trans hsnd₂)
        have hf2 : f a₂ = (a₂, false) := hf_lt a₂ hlt₂
        have hEq : (a₁, false) = (a₂, false) := by simpa [hf1, hf2] using h
        exact congrArg Prod.fst hEq
      · have hge₁ : mid ≤ a₁ := Nat.le_of_not_gt hlt₁
        have hsnd₁ : (f a₁).2 = true := by
          by_cases heq₁ : a₁ = mid
          · rw [hf_eq a₁ heq₁]
          · rw [hf_gt a₁ hge₁ heq₁]
        have hsnd₂ : (f a₂).2 = true := by
          have : (f a₂).2 = (f a₁).2 := congrArg Prod.snd h.symm
          simpa [hsnd₁] using this
        have hge₂ : mid ≤ a₂ := by
          by_contra hlt₂
          have hf2 : (f a₂).2 = false := by rw [hf_lt a₂ (Nat.lt_of_not_ge hlt₂)]
          cases (hf2.symm.trans hsnd₂)
        by_cases heq₁ : a₁ = mid
        · by_cases heq₂ : a₂ = mid
          · omega
          · have hf1 : f a₁ = (0, true) := hf_eq a₁ heq₁
            have hf2 : f a₂ = (p - 1 - a₂, true) := hf_gt a₂ hge₂ heq₂
            have hEq : (0, true) = (p - 1 - a₂, true) := by simpa [hf1, hf2] using h
            have h0 : p - 1 - a₂ = 0 := (congrArg Prod.fst hEq).symm
            rw [Finset.mem_erase] at ha₂
            exact (ha₂.1 (by omega : a₂ = p - 1)).elim
        · by_cases heq₂ : a₂ = mid
          · have hf1 : f a₁ = (p - 1 - a₁, true) := hf_gt a₁ hge₁ heq₁
            have hf2 : f a₂ = (0, true) := hf_eq a₂ heq₂
            have hEq : (p - 1 - a₁, true) = (0, true) := by simpa [hf1, hf2] using h
            have h0 : p - 1 - a₁ = 0 := congrArg Prod.fst hEq
            rw [Finset.mem_erase] at ha₁
            exact (ha₁.1 (by omega : a₁ = p - 1)).elim
          · have hf1 : f a₁ = (p - 1 - a₁, true) := hf_gt a₁ hge₁ heq₁
            have hf2 : f a₂ = (p - 1 - a₂, true) := hf_gt a₂ hge₂ heq₂
            have hEq : (p - 1 - a₁, true) = (p - 1 - a₂, true) := by simpa [hf1, hf2] using h
            have hp : p - 1 - a₁ = p - 1 - a₂ := congrArg Prod.fst hEq
            omega
    · -- surjectivity
      intro b hb
      rw [Finset.mem_union] at hb
      rcases hb with hbT | hbmid
      · have hbT_mem : b.1 ∈ T := (Finset.mem_product.mp hbT).1
        dsimp [T] at hbT_mem
        have hbT' : b.1 ∈ E p ∧ b.1 < mid := Finset.mem_filter.mp hbT_mem
        have hrE : b.1 ∈ E p := hbT'.1
        have hrlt : b.1 < mid := hbT'.2
        by_cases hflag : b.2 = true
        · refine ⟨p - 1 - b.1, ?_, ?_⟩
          · rw [Finset.mem_erase]
            constructor
            · have h1b : 1 ≤ b.1 := mem_E_ge_one p b.1 hrE
              omega
            · have hIcc : b.1 ∈ Finset.Icc 1 (p - 2) := by
                rw [Finset.mem_Icc]
                exact ⟨mem_E_ge_one p b.1 hrE, by omega⟩
              exact (mem_E_iff_pm_sub p b.1 hIcc).mp hrE
          · rw [hf_gt (p - 1 - b.1) (by omega) (by omega)]
            ext
            · omega
            · simp [hflag]
        · have hflag' : b.2 = false := by
            cases hb2 : b.2 with
            | false => rfl
            | true => exact (hflag hb2).elim
          refine ⟨b.1, ?_, ?_⟩
          · rw [Finset.mem_erase]
            constructor
            · have h1b : 1 ≤ b.1 := mem_E_ge_one p b.1 hrE
              omega
            · exact hrE
          · rw [hf_lt b.1 hrlt]
            ext
            · rfl
            · exact hflag'.symm
      · by_cases hmidE : mid ∈ E p
        · rw [ite_eq_left hmidE] at hbmid
          rw [Finset.mem_singleton] at hbmid
          subst b
          refine ⟨mid, ?_, ?_⟩
          · rw [Finset.mem_erase]
            constructor
            · omega
            · exact hmidE
          · exact hf_eq mid rfl
        · rw [ite_eq_right hmidE] at hbmid
          simp at hbmid
  simpa [mid, T] using hbij.trans hcardD

/-- `|E p| = 2·|{r < (p-1)/2 : r ∈ E p}| + (1 or 2 according as the middle digit is bad)`.
-/
lemma E_card_eq (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (E p).card = 2 * ((E p).filter (fun r => r < (p - 1) / 2)).card
        + (if (p - 1) / 2 ∈ E p then 2 else 1) := by
  have hmem : p - 1 ∈ E p := wolstenholme_mem_E p hp
  have hE : (E p).card = ((E p).erase (p - 1)).card + 1 :=
    (Finset.card_erase_add_one hmem).symm
  rw [hE, card_erase_pred p hp]
  by_cases hmid : (p - 1) / 2 ∈ E p <;> simp [hmid]

/-- For an odd prime `p`, `|E p|` is odd exactly when the middle digit `(p - 1) / 2` is
**not** bad. -/
theorem E_card_odd_iff_mid_not_mem (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    Odd ((E p).card) ↔ (p - 1) / 2 ∉ E p := by
  have hcard := E_card_eq p hp
  by_cases hmid : (p - 1) / 2 ∈ E p
  · have hEven : Even ((E p).card) := by
      rw [hcard, ite_eq_left hmid]
      refine ⟨((E p).filter (fun r => r < (p - 1) / 2)).card + 1, by omega⟩
    have hnotOdd : ¬ Odd ((E p).card) := (Nat.not_odd_iff_even).2 hEven
    constructor
    · intro hOdd
      exact (hnotOdd hOdd).elim
    · intro hnotmem
      exact (hnotmem hmid).elim
  · have hOdd : Odd ((E p).card) := by
      rw [hcard, ite_eq_right hmid]
      refine ⟨((E p).filter (fun r => r < (p - 1) / 2)).card, rfl⟩
    constructor
    · intro _
      exact hmid
    · intro _
      exact hOdd

/-! ## Finite tables -/

lemma E_eleven : E 11 = {3, 7, 10} := by
  native_decide

lemma E_twentynine : E 29 = {13, 15, 28} := by
  native_decide

lemma E_hundred_nine : E 109 = {25, 31, 44, 64, 77, 83, 108} := by
  native_decide

lemma E_thousand_ninety_three : E 1093 = {273, 546, 819, 1092} := by
  native_decide

end Erdos291
