import Erdos291.BulkRemoval
import Erdos291.DyadicBlocks
import Erdos291.PairGCD
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The middle block contribution `Wmid` and the exact decomposition `W = Wtail + Wmid`

We split the dyadic block contribution `W R x` according to the size of the prime `p`
relative to `r²`.  The tail `p > r²` is already controlled uniformly by
`Wtail_uniformly_tends_to_zero`.  This file isolates the remaining piece

  `Wmid R x = Σ_{R ≤ r < 2R} Σ_{p ≤ x, 2r+1 < p ≤ r², p prime, p ∣ num H_r} 1/(p-1)`

and proves the exact identity `W R x = Wtail R x + Wmid R x`.

Consequently, once one proves that `Wmid R x` tends to zero uniformly in `x` as `R → ∞`,
the uniform vanishing of `W R x` follows by adding the already-established tail bound.
-/

open scoped BigOperators

namespace Erdos291

/-- The middle part of the dyadic block `R ≤ r < 2R`: bad primes `p` with
`2r + 1 < p ≤ r²`. -/
noncomputable def Wmid (R x : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico R (2 * R),
    ∑ p ∈ (Finset.Icc 2 x).filter
        (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧
          Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
      (1 / ((p - 1 : ℕ) : ℝ))

/-! ## Pair finsets used for the rearrangement -/

private def primeSet (x : ℕ) : Finset ℕ :=
  (Finset.Icc 2 x).filter Nat.Prime

private def block (R : ℕ) : Finset ℕ :=
  Finset.Ico R (2 * R)

private def pairUniv (R x : ℕ) : Finset (ℕ × ℕ) :=
  (primeSet x).product (block R)

private noncomputable def weight (p : ℕ) : ℝ :=
  1 / ((p - 1 : ℕ) : ℝ)

private def tailCond (pr : ℕ × ℕ) : Prop :=
  pr.2 ^ 2 < pr.1 ∧ (pr.1 : ℤ) ∣ (harmonic pr.2).num

private def midCond (pr : ℕ × ℕ) : Prop :=
  2 * pr.2 + 1 < pr.1 ∧ pr.1 ≤ pr.2 ^ 2 ∧ (pr.1 : ℤ) ∣ (harmonic pr.2).num

private def Wpairs (R x : ℕ) : Finset (ℕ × ℕ) :=
  (pairUniv R x).filter fun pr => pr.2 ∈ T pr.1

private def WtailPairs (R x : ℕ) : Finset (ℕ × ℕ) :=
  (pairUniv R x).filter fun pr => pr.2 ^ 2 < pr.1 ∧ (pr.1 : ℤ) ∣ (harmonic pr.2).num

private def WmidPairs (R x : ℕ) : Finset (ℕ × ℕ) :=
  (pairUniv R x).filter fun pr =>
    2 * pr.2 + 1 < pr.1 ∧ pr.1 ≤ pr.2 ^ 2 ∧ (pr.1 : ℤ) ∣ (harmonic pr.2).num

private lemma one_le_of_mem_block {R r : ℕ} (hr : r ∈ block R) : 1 ≤ r := by
  unfold block at hr
  have hrI := Finset.mem_Ico.mp hr
  omega

private lemma prime_of_mem_primeSet {x p : ℕ} (hp : p ∈ primeSet x) : Nat.Prime p := by
  unfold primeSet at hp
  exact (Finset.mem_filter.mp hp).2

private lemma two_le_of_mem_primeSet {x p : ℕ} (hp : p ∈ primeSet x) : 2 ≤ p := by
  unfold primeSet at hp
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1

private lemma harmonic_one_num : (harmonic 1).num = 1 := by
  native_decide

private lemma harmonic_two_num : (harmonic 2).num = 3 := by
  native_decide

/-! ## The two pair conditions are exactly the two halves of `r ∈ T p` -/

private lemma tailCond_implies_mem_T {R x p r : ℕ}
    (hpr : (p, r) ∈ pairUniv R x) (htail : tailCond (p, r)) : r ∈ T p := by
  rcases htail with ⟨hgt, hdvd⟩
  have hprP : p ∈ primeSet x := (Finset.mem_product.mp hpr).1
  have hprB : r ∈ block R := (Finset.mem_product.mp hpr).2
  have hpPrime : Nat.Prime p := prime_of_mem_primeSet hprP
  have hp2 : 2 ≤ p := two_le_of_mem_primeSet hprP
  have h1r : 1 ≤ r := one_le_of_mem_block hprB
  by_cases hr1 : r = 1
  · subst r
    rw [harmonic_one_num] at hdvd
    have hnat : p ∣ (1 : ℤ).natAbs :=
      (Int.ofNat_dvd_left (n := p) (z := (1 : ℤ))).mp hdvd
    have hp_le : p ≤ (1 : ℤ).natAbs :=
      Nat.le_of_dvd (by norm_num : 0 < (1 : ℤ).natAbs) hnat
    norm_num at hp_le
    omega
  · by_cases hr2 : r = 2
    · subst r
      rw [harmonic_two_num] at hdvd
      have hp5 : 5 ≤ p := by
        have h : 4 < p := by simpa using hgt
        omega
      have hnat : p ∣ (3 : ℤ).natAbs :=
        (Int.ofNat_dvd_left (n := p) (z := (3 : ℤ))).mp hdvd
      have hp_le : p ≤ (3 : ℤ).natAbs :=
        Nat.le_of_dvd (by norm_num : 0 < (3 : ℤ).natAbs) hnat
      norm_num at hp_le
      omega
    · have h3r : 3 ≤ r := by omega
      have hsq : 2 * r + 1 ≤ r ^ 2 := by
        nlinarith
      have h2rp : 2 * r + 1 < p := lt_of_le_of_lt hsq hgt
      have hrp : r < p := by omega
      have h2lt : 2 * r < p - 1 := by omega
      have hrE : r ∈ E p :=
        (mem_E_iff_dvd_num p r hpPrime h1r hrp).mpr hdvd
      exact Finset.mem_filter.mpr ⟨hrE, h2lt⟩

private lemma midCond_implies_mem_T {R x p r : ℕ}
    (hpr : (p, r) ∈ pairUniv R x) (hmid : midCond (p, r)) : r ∈ T p := by
  rcases hmid with ⟨h2rp, _hle, hdvd⟩
  have hprP : p ∈ primeSet x := (Finset.mem_product.mp hpr).1
  have hprB : r ∈ block R := (Finset.mem_product.mp hpr).2
  have hpPrime : Nat.Prime p := prime_of_mem_primeSet hprP
  have h1r : 1 ≤ r := one_le_of_mem_block hprB
  have hrp : r < p := by omega
  have h2lt : 2 * r < p - 1 := by omega
  have hrE : r ∈ E p :=
    (mem_E_iff_dvd_num p r hpPrime h1r hrp).mpr hdvd
  exact Finset.mem_filter.mpr ⟨hrE, h2lt⟩

private lemma mem_T_iff_tail_or_mid {R x : ℕ} {pr : ℕ × ℕ}
    (hpr : pr ∈ pairUniv R x) :
    pr.2 ∈ T pr.1 ↔ tailCond pr ∨ midCond pr := by
  constructor
  · intro hrT
    have hprP : pr.1 ∈ primeSet x := (Finset.mem_product.mp hpr).1
    have hprB : pr.2 ∈ block R := (Finset.mem_product.mp hpr).2
    have hpPrime : Nat.Prime pr.1 := prime_of_mem_primeSet hprP
    have h1r : 1 ≤ pr.2 := one_le_of_mem_block hprB
    have hrE : pr.2 ∈ E pr.1 := (Finset.mem_filter.mp hrT).1
    have h2lt : 2 * pr.2 < pr.1 - 1 := (Finset.mem_filter.mp hrT).2
    have h2rp : 2 * pr.2 + 1 < pr.1 := by omega
    have hrp : pr.2 < pr.1 := by omega
    have hdvd : (pr.1 : ℤ) ∣ (harmonic pr.2).num :=
      (mem_E_iff_dvd_num pr.1 pr.2 hpPrime h1r hrp).mp hrE
    by_cases htail : pr.2 ^ 2 < pr.1
    · exact Or.inl ⟨htail, hdvd⟩
    · exact Or.inr ⟨h2rp, le_of_not_gt htail, hdvd⟩
  · intro h
    rcases h with htail | hmid
    · exact tailCond_implies_mem_T hpr htail
    · exact midCond_implies_mem_T hpr hmid

private lemma Wpairs_eq_union (R x : ℕ) :
    Wpairs R x = WtailPairs R x ∪ WmidPairs R x := by
  classical
  ext pr
  by_cases hpr : pr ∈ pairUniv R x
  · simp [Wpairs, WtailPairs, WmidPairs, Finset.mem_union, Finset.mem_filter, hpr,
      mem_T_iff_tail_or_mid hpr, tailCond, midCond]
  · simp [Wpairs, WtailPairs, WmidPairs, Finset.mem_union, Finset.mem_filter, hpr]

private lemma WtailPairs_disjoint_WmidPairs (R x : ℕ) :
    Disjoint (WtailPairs R x) (WmidPairs R x) := by
  classical
  rw [Finset.disjoint_left]
  intro pr htail hmid
  unfold WtailPairs at htail
  unfold WmidPairs at hmid
  rcases (Finset.mem_filter.mp htail).2 with ⟨hgt, _⟩
  rcases (Finset.mem_filter.mp hmid).2 with ⟨_, hle, _⟩
  omega

/-! ## The three pair-sum representations -/

private lemma W_eq_sum_Wpairs (R x : ℕ) :
    W R x = ∑ pr ∈ Wpairs R x, weight pr.1 := by
  let P : Finset ℕ := primeSet x
  let B : Finset ℕ := block R
  calc
    W R x = ∑ p ∈ P, ∑ r ∈ (T p).filter (fun r => R ≤ r ∧ r < 2 * R), weight p := by
      simp [W, P, primeSet, weight]
    _ = ∑ a ∈ P.sigma (fun p => (T p).filter (fun r => R ≤ r ∧ r < 2 * R)), weight a.1 := by
      rw [Finset.sum_sigma']
    _ = ∑ pr ∈ Wpairs R x, weight pr.1 := by
      refine Finset.sum_bij (fun a _ => (a.1, a.2)) ?_ ?_ ?_ ?_
      · intro a ha
        have haP : a.1 ∈ P := (Finset.mem_sigma.mp ha).1
        have har : a.2 ∈ (T a.1).filter (fun r => R ≤ r ∧ r < 2 * R) :=
          (Finset.mem_sigma.mp ha).2
        have harT : a.2 ∈ T a.1 := (Finset.mem_filter.mp har).1
        have harB : a.2 ∈ B := by
          have hblock := (Finset.mem_filter.mp har).2
          exact Finset.mem_Ico.mpr hblock
        have hpair : (a.1, a.2) ∈ pairUniv R x := by
          exact Finset.mem_product.mpr ⟨by simpa [P] using haP, by simpa [B] using harB⟩
        exact Finset.mem_filter.mpr ⟨hpair, harT⟩
      · intro a₁ _ a₂ _ h
        cases a₁ with
        | mk p₁ r₁ =>
          cases a₂ with
          | mk p₂ r₂ =>
            cases h
            rfl
      · intro b hb
        have hbP : b.1 ∈ P := by
          have hm := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
          exact hm.1
        have hbB : b.2 ∈ B := by
          have hm := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
          exact hm.2
        have hbT : b.2 ∈ T b.1 := (Finset.mem_filter.mp hb).2
        refine ⟨⟨b.1, b.2⟩, ?_, rfl⟩
        rw [Finset.mem_sigma]
        constructor
        · exact hbP
        · exact Finset.mem_filter.mpr ⟨hbT, Finset.mem_Ico.mp hbB⟩
      · intro a ha
        rfl

private lemma Wtail_eq_sum_tailPairs (R x : ℕ) :
    Wtail R x = ∑ pr ∈ WtailPairs R x, weight pr.1 := by
  let P : Finset ℕ := primeSet x
  let B : Finset ℕ := block R
  calc
    Wtail R x = ∑ r ∈ B,
        ∑ p ∈ (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
            (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num), weight p := by
      simp [Wtail, B, block, weight]
    _ = ∑ a ∈ B.sigma (fun r =>
        (Finset.Ico (r ^ 2 + 1) (x + 1)).filter
          (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)), weight a.2 := by
      rw [Finset.sum_sigma']
    _ = ∑ pr ∈ WtailPairs R x, weight pr.1 := by
      refine Finset.sum_bij (fun a _ => (a.2, a.1)) ?_ ?_ ?_ ?_
      · intro a ha
        have har : a.1 ∈ B := (Finset.mem_sigma.mp ha).1
        have hap : a.2 ∈ (Finset.Ico (a.1 ^ 2 + 1) (x + 1)).filter
            (fun p => Nat.Prime p ∧ (p : ℤ) ∣ (harmonic a.1).num) :=
          (Finset.mem_sigma.mp ha).2
        have hpIco := Finset.mem_Ico.mp (Finset.mem_filter.mp hap).1
        have hpPrime : Nat.Prime a.2 := (Finset.mem_filter.mp hap).2.1
        have hdvd : (a.2 : ℤ) ∣ (harmonic a.1).num := (Finset.mem_filter.mp hap).2.2
        have hplo : a.1 ^ 2 + 1 ≤ a.2 := hpIco.1
        have hphi : a.2 < x + 1 := hpIco.2
        have hpP : a.2 ∈ P := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, by omega⟩, hpPrime⟩
        have hpair : (a.2, a.1) ∈ pairUniv R x := by
          exact Finset.mem_product.mpr ⟨by simpa [P] using hpP, by simpa [B] using har⟩
        have hgt : a.1 ^ 2 < a.2 := by omega
        exact Finset.mem_filter.mpr ⟨hpair, hgt, hdvd⟩
      · intro a₁ _ a₂ _ h
        cases a₁ with
        | mk r₁ p₁ =>
          cases a₂ with
          | mk r₂ p₂ =>
            cases h
            rfl
      · intro b hb
        have hbP : b.1 ∈ P := by
          have hm := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
          exact hm.1
        have hbB : b.2 ∈ B := by
          have hm := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
          exact hm.2
        have hbF := (Finset.mem_filter.mp hb).2
        rcases hbF with ⟨hgt, hdvd⟩
        have hbIcc : b.1 ∈ Finset.Icc 2 x := (Finset.mem_filter.mp hbP).1
        have hb_le_x : b.1 ≤ x := (Finset.mem_Icc.mp hbIcc).2
        have hplo : b.2 ^ 2 + 1 ≤ b.1 := by omega
        have hphi : b.1 < x + 1 := by omega
        refine ⟨⟨b.2, b.1⟩, ?_, rfl⟩
        rw [Finset.mem_sigma]
        constructor
        · exact hbB
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨hplo, hphi⟩,
              (prime_of_mem_primeSet hbP), hdvd⟩
      · intro a ha
        rfl

private lemma Wmid_eq_sum_midPairs (R x : ℕ) :
    Wmid R x = ∑ pr ∈ WmidPairs R x, weight pr.1 := by
  let P : Finset ℕ := primeSet x
  let B : Finset ℕ := block R
  calc
    Wmid R x = ∑ r ∈ B,
        ∑ p ∈ (Finset.Icc 2 x).filter
            (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num),
          weight p := by
      simp [Wmid, B, block, weight]
    _ = ∑ a ∈ B.sigma (fun r =>
        (Finset.Icc 2 x).filter
          (fun p => 2 * r + 1 < p ∧ p ≤ r ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic r).num)),
        weight a.2 := by
      rw [Finset.sum_sigma']
    _ = ∑ pr ∈ WmidPairs R x, weight pr.1 := by
      refine Finset.sum_bij (fun a _ => (a.2, a.1)) ?_ ?_ ?_ ?_
      · intro a ha
        have har : a.1 ∈ B := (Finset.mem_sigma.mp ha).1
        have hap : a.2 ∈ (Finset.Icc 2 x).filter
            (fun p => 2 * a.1 + 1 < p ∧ p ≤ a.1 ^ 2 ∧ Nat.Prime p ∧ (p : ℤ) ∣ (harmonic a.1).num) :=
          (Finset.mem_sigma.mp ha).2
        have hF := Finset.mem_filter.mp hap
        have hpIcc : a.2 ∈ Finset.Icc 2 x := hF.1
        have h2 : 2 * a.1 + 1 < a.2 := hF.2.1
        have hle : a.2 ≤ a.1 ^ 2 := hF.2.2.1
        have hpPrime : Nat.Prime a.2 := hF.2.2.2.1
        have hdvd : (a.2 : ℤ) ∣ (harmonic a.1).num := hF.2.2.2.2
        have hpP : a.2 ∈ P := by
          exact Finset.mem_filter.mpr ⟨hpIcc, hpPrime⟩
        have hpair : (a.2, a.1) ∈ pairUniv R x := by
          exact Finset.mem_product.mpr ⟨by simpa [P] using hpP, by simpa [B] using har⟩
        exact Finset.mem_filter.mpr ⟨hpair, h2, hle, hdvd⟩
      · intro a₁ _ a₂ _ h
        cases a₁ with
        | mk r₁ p₁ =>
          cases a₂ with
          | mk r₂ p₂ =>
            cases h
            rfl
      · intro b hb
        have hbP : b.1 ∈ P := by
          have hm := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
          exact hm.1
        have hbB : b.2 ∈ B := by
          have hm := Finset.mem_product.mp (Finset.mem_filter.mp hb).1
          exact hm.2
        have hbF := (Finset.mem_filter.mp hb).2
        rcases hbF with ⟨h2, hle, hdvd⟩
        have hbIcc : b.1 ∈ Finset.Icc 2 x := (Finset.mem_filter.mp hbP).1
        refine ⟨⟨b.2, b.1⟩, ?_, rfl⟩
        rw [Finset.mem_sigma]
        constructor
        · exact hbB
        · exact Finset.mem_filter.mpr
            ⟨hbIcc, by simpa using h2, by simpa using hle,
              (prime_of_mem_primeSet hbP), hdvd⟩
      · intro a ha
        rfl

/-! ## The exact decomposition -/

/-- The exact decomposition `W R x = Wtail R x + Wmid R x`. -/
theorem W_eq_Wtail_add_Wmid (R x : ℕ) :
    W R x = Wtail R x + Wmid R x := by
  rw [W_eq_sum_Wpairs R x, Wpairs_eq_union R x]
  rw [Finset.sum_union (WtailPairs_disjoint_WmidPairs R x)]
  rw [Wtail_eq_sum_tailPairs R x, Wmid_eq_sum_midPairs R x]

/-- The middle contribution is nonnegative. -/
lemma Wmid_nonneg (R x : ℕ) : 0 ≤ Wmid R x := by
  unfold Wmid
  exact Finset.sum_nonneg (by
    intro r hr
    exact Finset.sum_nonneg (by
      intro p hp
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg _)))

/-- Uniform vanishing of `Wmid` implies uniform vanishing of `W`. -/
theorem W_uniformly_tends_to_zero_of_Wmid_uniformly_tends_to_zero
    (h : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, Wmid R x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ x : ℕ, W R x ≤ ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  rcases Wtail_uniformly_tends_to_zero (ε / 2) hε2 with ⟨Rtail, hRtail⟩
  rcases h (ε / 2) hε2 with ⟨Rmid, hRmid⟩
  refine ⟨max Rtail Rmid, ?_⟩
  intro R hR x
  have htail : Wtail R x ≤ ε / 2 := hRtail R (le_trans (le_max_left Rtail Rmid) hR) x
  have hmid : Wmid R x ≤ ε / 2 := hRmid R (le_trans (le_max_right Rtail Rmid) hR) x
  rw [W_eq_Wtail_add_Wmid R x]
  linarith

end Erdos291
