import Erdos291.GapCoprime
import Erdos291.GapResultant
import Erdos291.GcdOne
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Topology.Instances.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Lemmas

set_option linter.style.haveILetI false

/-!
# Erdős #291 — the bad-digit density `c p` tends to zero along the primes

For each fixed pair `1 ≤ d < e` the deep result `resultant_Qd_ne_zero` (in
`Erdos291.GapCoprime`) shows the integer `N_{d,e} = |resultant (Qd d) (Qd e)|` is nonzero, and
`resultant_eq_zero_of_triple_bad` shows any prime `p` realizing a triple `r, r+d, r+e ∈ E p`
divides it.  Multiplying these over all pairs `1 ≤ d < e ≤ D` gives a fixed nonzero integer
`Nall D`; any prime not dividing `Nall D` then has *no* three bad digits of span `≤ D`.
Partitioning `[1, p - 1]` into blocks of length `D` then bounds `|E p|` by
`2 * ((p - 1) / D + 1)`, hence `c p ≤ 2 / D + 2 / (p - 1)` for all primes outside the finite
exceptional set.  Letting `D` tend to infinity yields `c p → 0` along the primes.

This file formalizes the ε-N limit `exists_P_forall_c_lt` together with the `Tendsto` capstone
`badDensity_tendsto_zero`; the easy nonnegativity `c_nonneg` is reused from `Erdos291.GcdOne`.
-/

open scoped BigOperators Topology
open Filter

namespace Erdos291

/-! ## The finite product `Nall D` of exceptional integers -/

/-- The finite set of distance pairs `1 ≤ d < e ≤ D`. -/
def pairs (D : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter (fun de => de.1 < de.2)

/-- The exceptional integer attached to the distance pair `(d, e)`: the absolute value of the
resultant of the distance polynomials `Qd d` and `Qd e`.  Any prime realizing the triple pattern
`r, r+d, r+e ∈ E p` divides it, and it is nonzero for `1 ≤ d`, `1 ≤ e`, `d ≠ e`. -/
noncomputable def Nde (d e : ℕ) : ℕ :=
  (Polynomial.resultant (Qd d) (Qd e)).natAbs

/-- `Nall D = ∏_{1 ≤ d < e ≤ D} N_{d,e}` is the fixed nonzero integer that every prime with a
bad-triple of span `≤ D` must divide. -/
noncomputable def Nall (D : ℕ) : ℕ :=
  ∏ de ∈ pairs D, Nde de.1 de.2

/-- `NoTripleWithin S D` asserts that `S` contains no three (ordered) elements `r₁ < r₂ < r₃`
with span `r₃ - r₁ ≤ D`. -/
def NoTripleWithin (S : Finset ℕ) (D : ℕ) : Prop :=
  ∀ ⦃r₁ r₂ r₃⦄, r₁ ∈ S → r₂ ∈ S → r₃ ∈ S → r₁ < r₂ → r₂ < r₃ → r₃ - r₁ ≤ D → False

/-- `Nde d e` is nonzero for `1 ≤ d`, `1 ≤ e`, `d ≠ e`. -/
lemma Nde_ne_zero (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) (hde : d ≠ e) : Nde d e ≠ 0 := by
  unfold Nde
  intro h
  exact resultant_Qd_ne_zero d e hd he hde (Int.natAbs_eq_zero.mp h)

/-- A prime realizing the triple pattern `r, r+d, r+e ∈ E p` (with all three in range) divides
`Nde d e`. -/
lemma Nde_dvd_of_triple (p d e r : ℕ) [Fact p.Prime]
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (hr : r ∈ E p) (hradd : r + d ∈ E p) (hre : r + e ∈ E p)
    (hle : r + max d e ≤ p - 1) :
    p ∣ Nde d e := by
  unfold Nde
  have hz : ((Polynomial.resultant (Qd d) (Qd e) : ℤ) : ZMod p) = 0 :=
    resultant_eq_zero_of_triple_bad p d e r hd he hr hradd hre hle
  have hdvdZ : (p : ℤ) ∣ (Polynomial.resultant (Qd d) (Qd e) : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.resultant (Qd d) (Qd e)) p).mp hz
  exact (Int.natCast_dvd (m := p) (n := Polynomial.resultant (Qd d) (Qd e))).mp hdvdZ

/-- The product `Nall D` is nonzero. -/
lemma Nall_ne_zero (D : ℕ) : Nall D ≠ 0 := by
  unfold Nall
  rw [Finset.prod_ne_zero_iff]
  intro de hde
  have hmem := Finset.mem_filter.mp hde
  have hprod := Finset.mem_product.mp hmem.1
  have h1 : 1 ≤ de.1 := (Finset.mem_Icc.mp hprod.1).1
  have h2 : 1 ≤ de.2 := (Finset.mem_Icc.mp hprod.2).1
  have hne : de.1 ≠ de.2 := ne_of_lt hmem.2
  exact Nde_ne_zero de.1 de.2 h1 h2 hne

/-- Each factor `Nde d e` divides the product `Nall D`. -/
lemma Nde_dvd_Nall (D : ℕ) {d e : ℕ} (h : (d, e) ∈ pairs D) : Nde d e ∣ Nall D := by
  simpa [Nall] using (Finset.dvd_prod_of_mem (fun de : ℕ × ℕ => Nde de.1 de.2) h)

/-! ## Proposition 1: no three bad digits of span `≤ D` for `p ∤ Nall D` -/

/-- If the prime `p` does not divide `Nall D`, then `E p` has no three elements of span `≤ D`. -/
lemma no_triple_of_not_dvd_Nall (p D : ℕ) [Fact p.Prime] (h : ¬ p ∣ Nall D) :
    NoTripleWithin (E p) D := by
  intro r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23 hspan
  let d : ℕ := r₂ - r₁
  let e : ℕ := r₃ - r₁
  have hd_ge : 1 ≤ d := by dsimp [d]; omega
  have he_ge : 1 ≤ e := by dsimp [d, e]; omega
  have hde_lt : d < e := by dsimp [d, e]; omega
  have heD : e ≤ D := by simpa [e] using hspan
  have hdD : d ≤ D := le_trans (le_of_lt hde_lt) heD
  have hpair : (d, e) ∈ pairs D := by
    rw [pairs, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨hd_ge, hdD⟩
    · rw [Finset.mem_Icc]; exact ⟨he_ge, heD⟩
    · exact hde_lt
  have hrd : r₁ + d = r₂ := by dsimp [d]; omega
  have hre : r₁ + e = r₃ := by dsimp [d, e]; omega
  have hmax : max d e = e := by
    apply max_eq_right
    exact le_of_lt hde_lt
  have hle : r₁ + max d e ≤ p - 1 := by
    rw [hmax]
    dsimp [e]
    have hr₃le : r₃ ≤ p - 1 := by
      unfold E at hr₃
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hr₃).1).2
    omega
  have hdvd_Nde : p ∣ Nde d e :=
    Nde_dvd_of_triple p d e r₁ hd_ge he_ge hr₁
      (by simpa [hrd] using hr₂) (by simpa [hre] using hr₃) hle
  exact h (dvd_trans hdvd_Nde (Nde_dvd_Nall D hpair))

/-! ## Combinatorial Lemma B: block partition -/

/-- Two elements `r < s` of a common length-`D` block have span `s - r ≤ D`. -/
private lemma block_span_le (D i : ℕ) {r s : ℕ} (hrs : r < s) (hr : r ∈ block D i) (hs : s ∈ block D i) :
    s - r ≤ D := by
  rw [block] at hr hs
  have hle_r : i * D + 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hle_s : s ≤ (i + 1) * D := (Finset.mem_Icc.mp hs).2
  have hexpand : (i + 1) * D = i * D + D := by rw [Nat.add_mul, Nat.one_mul]
  rw [hexpand] at hle_s
  omega

/-- If `S` has no three elements of span `≤ D`, then each length-`D` block contains at most
two elements of `S`. -/
lemma block_card_le_two (S : Finset ℕ) (D i : ℕ) (h : NoTripleWithin S D) :
    (S ∩ block D i).card ≤ 2 := by
  by_contra hnot
  have hgt : 2 < (S ∩ block D i).card := by omega
  rcases Finset.two_lt_card.mp hgt with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have haS : a ∈ S := (Finset.mem_inter.mp ha).1
  have hbS : b ∈ S := (Finset.mem_inter.mp hb).1
  have hcS : c ∈ S := (Finset.mem_inter.mp hc).1
  have haB : a ∈ block D i := (Finset.mem_inter.mp ha).2
  have hbB : b ∈ block D i := (Finset.mem_inter.mp hb).2
  have hcB : c ∈ block D i := (Finset.mem_inter.mp hc).2
  have hord : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨ (b < a ∧ a < c) ∨
      (b < c ∧ c < a) ∨ (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by omega
  rcases hord with h1 | h2 | h3 | h4 | h5 | h6
  · exact h haS hbS hcS h1.1 h1.2 (block_span_le D i (lt_trans h1.1 h1.2) haB hcB)
  · exact h haS hcS hbS h2.1 h2.2 (block_span_le D i (lt_trans h2.1 h2.2) haB hbB)
  · exact h hbS haS hcS h3.1 h3.2 (block_span_le D i (lt_trans h3.1 h3.2) hbB hcB)
  · exact h hbS hcS haS h4.1 h4.2 (block_span_le D i (lt_trans h4.1 h4.2) hbB haB)
  · exact h hcS haS hbS h5.1 h5.2 (block_span_le D i (lt_trans h5.1 h5.2) hcB hbB)
  · exact h hcS hbS haS h6.1 h6.2 (block_span_le D i (lt_trans h6.1 h6.2) hcB haB)

/-- Covering `[1, n]` by `n / D + 1` blocks of length `D` bounds `|S|` by `2 * (n / D + 1)` when
`S` has no three elements of span `≤ D`. -/
lemma card_le_two_mul_div_add_two_of_no_triple (S : Finset ℕ) (D n : ℕ) (hD : 0 < D)
    (hS : S ⊆ Finset.Icc 1 n) (h : NoTripleWithin S D) :
    S.card ≤ 2 * (n / D + 1) := by
  classical
  have hD1 : 1 ≤ D := by omega
  have hsum := sum_block_card_eq_card S n D hD1 hS
  have hblock : ∀ i ∈ Finset.range (n / D + 1), (S ∩ block D i).card ≤ 2 := by
    intro i hi
    exact block_card_le_two S D i h
  calc
    S.card = ∑ i ∈ Finset.range (n / D + 1), (S.filter fun r => r ∈ block D i).card := hsum.symm
    _ = ∑ i ∈ Finset.range (n / D + 1), (S ∩ block D i).card := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finset.filter_mem_eq_inter]
    _ ≤ ∑ _i ∈ Finset.range (n / D + 1), 2 := Finset.sum_le_sum hblock
    _ = 2 * (n / D + 1) := by
        rw [Finset.sum_const, Finset.card_range]
        simp [mul_comm]

/-! ## Application to the bad set `E p` -/

/-- For a prime `p` not dividing `Nall D`, the bad set has at most `2 * ((p - 1) / D + 1)`
elements. -/
lemma E_card_le_two_mul_div_add_two (p D : ℕ) [Fact p.Prime] (hD : 0 < D) (h : ¬ p ∣ Nall D) :
    (E p).card ≤ 2 * ((p - 1) / D + 1) := by
  have hS : E p ⊆ Finset.Icc 1 (p - 1) := by
    rw [E]
    exact Finset.filter_subset _ _
  exact card_le_two_mul_div_add_two_of_no_triple (E p) D (p - 1) hD hS
    (no_triple_of_not_dvd_Nall p D h)

/-- The corresponding density bound for non-exceptional primes. -/
lemma c_le (p D : ℕ) [Fact p.Prime] (hD : 0 < D) (h : ¬ p ∣ Nall D) :
    (c p : ℝ) ≤ 2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ) := by
  have hp : Nat.Prime p := Fact.out
  have hcard := E_card_le_two_mul_div_add_two p D hD h
  have hn_pos : 0 < (p - 1 : ℕ) := by
    have hp2 : 2 ≤ p := hp.two_le
    omega
  have hn_posR : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hn_pos
  have hn_ne : ((p - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hn_posR
  have hD_posR : 0 < (D : ℝ) := by exact_mod_cast hD
  have hD_ne : (D : ℝ) ≠ 0 := ne_of_gt hD_posR
  have hc : (c p : ℝ) = ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    unfold c
    push_cast
    rw [Nat.cast_sub hp.one_le]
    norm_num
  rw [hc]
  have hcardR : ((E p).card : ℝ) ≤ 2 * (((p - 1) / D + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hdivD : (((p - 1) / D : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) / (D : ℝ) := Nat.cast_div_le
  have hnat_le : (((p - 1) / D + 1 : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) / (D : ℝ) + 1 := by
    have h1 : (((p - 1) / D + 1 : ℕ) : ℝ) = (((p - 1) / D : ℕ) : ℝ) + 1 := by norm_num
    rw [h1]
    linarith [hdivD]
  calc
    ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
        (2 * (((p - 1) / D + 1 : ℕ) : ℝ)) / ((p - 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hcardR (le_of_lt hn_posR)
    _ ≤ (2 * (((p - 1 : ℕ) : ℝ) / (D : ℝ) + 1)) / ((p - 1 : ℕ) : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hn_posR)
        exact mul_le_mul_of_nonneg_left hnat_le (by norm_num)
    _ = 2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ) := by
        field_simp [hn_ne, hD_ne]

/-! ## The limit argument -/

/-- For `0 < ε` and `0 < x`, if `4 / ε < x` then `2 / x < ε / 2`. -/
private lemma two_div_lt_of_four_div_lt {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) (h : 4 / ε < x) :
    2 / x < ε / 2 := by
  have hpos : 0 < ε / (2 * x) := div_pos hε (by positivity)
  have hmul : (4 / ε) * (ε / (2 * x)) < x * (ε / (2 * x)) :=
    mul_lt_mul_of_pos_right h hpos
  have hleft : (4 / ε) * (ε / (2 * x)) = 2 / x := by
    field_simp [hε.ne', hx.ne']
    ring
  have hright : x * (ε / (2 * x)) = ε / 2 := by
    field_simp [hε.ne', hx.ne']
  rwa [hleft, hright] at hmul

/-- **The ε-N theorem.** For every `ε > 0` there is a threshold `P` such that every prime
`p ≥ P` has density `c p < ε`. -/
theorem exists_P_forall_c_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, Nat.Prime p → P ≤ p → (c p : ℝ) < ε := by
  obtain ⟨D, hDgt⟩ := exists_nat_gt (4 / ε)
  have hDpos : 0 < D := by
    have hpos : 0 < 4 / ε := div_pos (by norm_num) hε
    have hDreal : 0 < (D : ℝ) := lt_of_le_of_lt (le_of_lt hpos) hDgt
    exact_mod_cast hDreal
  have htwo_div_D : 2 / (D : ℝ) < ε / 2 :=
    two_div_lt_of_four_div_lt hε (by exact_mod_cast hDpos) hDgt
  obtain ⟨P, hPgt⟩ := exists_nat_gt (max ((Nall D : ℝ)) (1 + 4 / ε))
  refine ⟨P, ?_⟩
  intro p hp hpP
  have hPgtNall : (Nall D : ℝ) < (P : ℝ) := by
    have : (Nall D : ℝ) ≤ max ((Nall D : ℝ)) (1 + 4 / ε) := le_max_left _ _
    exact lt_of_le_of_lt this hPgt
  have hPgtNall_nat : Nall D < P := by exact_mod_cast hPgtNall
  have hPgtone : 1 + 4 / ε < (P : ℝ) := by
    have : 1 + 4 / ε ≤ max ((Nall D : ℝ)) (1 + 4 / ε) := le_max_right _ _
    exact lt_of_le_of_lt this hPgt
  have hnotdvd : ¬ p ∣ Nall D := by
    intro hdvd
    have hle : p ≤ Nall D := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nall_ne_zero D)) hdvd
    have hlt : Nall D < p := lt_of_lt_of_le hPgtNall_nat hpP
    omega
  have hc_le : (c p : ℝ) ≤ 2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ) := by
    letI : Fact p.Prime := ⟨hp⟩
    exact c_le p D hDpos hnotdvd
  have hpm_pos : 0 < ((p - 1 : ℕ) : ℝ) := by
    have hp2 : 2 ≤ p := hp.two_le
    have h : 0 < p - 1 := by omega
    exact_mod_cast h
  have hpm_gt : 4 / ε < ((p - 1 : ℕ) : ℝ) := by
    have hpr : 1 + 4 / ε < (p : ℝ) :=
      lt_of_lt_of_le hPgtone (by exact_mod_cast hpP)
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_le]
      norm_num
    rw [hcast]
    linarith
  have htwo_div_pm : 2 / ((p - 1 : ℕ) : ℝ) < ε / 2 :=
    two_div_lt_of_four_div_lt hε hpm_pos hpm_gt
  have hsum : 2 / (D : ℝ) + 2 / ((p - 1 : ℕ) : ℝ) < ε := by
    linarith [htwo_div_D, htwo_div_pm]
  exact lt_of_le_of_lt hc_le hsum

/-- **The capstone.** The bad-digit density `c p` tends to `0` along the primes. -/
theorem badDensity_tendsto_zero :
    Tendsto (fun p : {p : ℕ // Nat.Prime p} => (c p.1 : ℝ)) atTop (𝓝 0) := by
  letI : Nonempty {p : ℕ // Nat.Prime p} := ⟨⟨2, Nat.prime_two⟩⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := exists_P_forall_c_lt ε hε
  obtain ⟨P₀, hP₀le, hP₀prime⟩ := Nat.exists_infinite_primes P
  refine ⟨⟨P₀, hP₀prime⟩, ?_⟩
  intro n hn
  have hn' : P₀ ≤ n.1 := hn
  have hle : P ≤ n.1 := le_trans hP₀le hn'
  have hlt : (c n.1 : ℝ) < ε := hP n.1 n.2 hle
  have hnonneg : 0 ≤ (c n.1 : ℝ) := c_nonneg n.1
  have hdist : dist ((c n.1 : ℝ)) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    exact hlt
  exact hdist

end Erdos291
