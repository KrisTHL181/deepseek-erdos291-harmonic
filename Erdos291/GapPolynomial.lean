import Erdos291.Basic
import Erdos291.BadSet
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Erdős #291 — the "distance polynomial" for the bad set `E p`

For a prime `p` and `1 ≤ d < p` we study the degree-`d` monic polynomial

    `P p d = ∏_{j=1}^d (X + j)`   over `ZMod p`

and its formal derivative `Q p d = (P p d)'`.  The two main results, both
unconditional and elementary, are:

* **Theorem A** (`eval_Q_eq_zero_of_mem_E_add`): if `r, r + d ∈ E p` (with
  `r + d ≤ p - 1`) then `Q p d` vanishes at `r` mod `p`.  In other words the
  "distance" between two bad digits is a root of the distance polynomial.

* **Theorem B** (`E_add_count_le_pred`): for each `d` there are at most `d - 1`
  bad digits `r` with `r + d` also bad, i.e. `#{r | r, r + d ∈ E p} ≤ d - 1`.
  For `d = 1` this recovers the fact (`not_mem_E_succ`) that no two bad digits
  are adjacent.

The key algebraic input is the derivative-of-a-product identity, which expresses
`Q p d` as the sum over `i` of the product of all linear factors except the
`i`-th one.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

/-- The degree-`d` monic polynomial `∏_{j=1}^d (X + j)` over `ZMod p`. -/
noncomputable def P (p d : ℕ) : Polynomial (ZMod p) :=
  ∏ i ∈ Finset.Icc 1 d, (Polynomial.X + Polynomial.C (i : ZMod p))

/-- The formal derivative `(P p d)'` of the distance polynomial. -/
noncomputable def Q (p d : ℕ) : Polynomial (ZMod p) :=
  Polynomial.derivative (P p d)

/-! ## Elementary splitting and reindexing lemmas -/

/-- Split an `Icc` sum at `r`: `∑_{j=1}^{r+d} f j = ∑_{j=1}^r f j + ∑_{j=r+1}^{r+d} f j`. -/
lemma sum_Icc_split_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (r d : ℕ) :
    (∑ j ∈ Finset.Icc 1 r, f j) + (∑ j ∈ Finset.Icc (r + 1) (r + d), f j) =
      ∑ j ∈ Finset.Icc 1 (r + d), f j := by
  rw [← Finset.Ico_add_one_right_eq_Icc (1) r,
    ← Finset.Ico_add_one_right_eq_Icc (r + 1) (r + d),
    ← Finset.Ico_add_one_right_eq_Icc (1) (r + d)]
  exact Finset.sum_Ico_consecutive f (by omega : 1 ≤ r + 1) (by omega : r + 1 ≤ r + d + 1)

/-- For units `a i`, the "derivative sum" `∑_i ∏_{j≠i} a_j` equals
`(∏_j a_j) * (∑_i a_i⁻¹)`. -/
lemma sum_prod_erase_eq_mul_inv {ι K : Type*} [Field K] [DecidableEq ι]
    (s : Finset ι) (a : ι → K) (ha : ∀ i ∈ s, IsUnit (a i)) :
    (∑ i ∈ s, ∏ j ∈ s.erase i, a j) = (∏ j ∈ s, a j) * (∑ i ∈ s, (a i)⁻¹) := by
  rw [mul_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_ne : a i ≠ 0 := (ha i hi).ne_zero
  symm
  calc
    (a i)⁻¹ * (∏ j ∈ s, a j) = (a i)⁻¹ * (a i * ∏ j ∈ s.erase i, a j) := by
      rw [← Finset.mul_prod_erase s a hi]
    _ = ((a i)⁻¹ * a i) * (∏ j ∈ s.erase i, a j) := by rw [mul_assoc]
    _ = (∏ j ∈ s.erase i, a j) := by rw [inv_mul_cancel₀ hi_ne, one_mul]

/-! ## Degree of `P` and `Q` -/

/-- `P p d` is monic. -/
lemma P_monic (p d : ℕ) : (P p d).Monic := by
  rw [P]
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_add_C (i : ZMod p)

/-- `P p d` has degree `d`. -/
lemma P_natDegree (p d : ℕ) [Nontrivial (ZMod p)] : (P p d).natDegree = d := by
  rw [P]
  have hmonic : ∀ i ∈ Finset.Icc 1 d, Monic (Polynomial.X + Polynomial.C (i : ZMod p)) := by
    intro i hi
    exact Polynomial.monic_X_add_C (i : ZMod p)
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc 1 d)
    (fun i => Polynomial.X + Polynomial.C (i : ZMod p)) hmonic]
  simp only [Polynomial.natDegree_X_add_C]
  rw [← Finset.card_eq_sum_ones, Nat.card_Icc]
  omega

/-- The coefficient of `Q p d` at `d - 1` is `(coeff (P p d) d) * d`. -/
lemma Q_coeff_pred (p d : ℕ) (hd : 1 ≤ d) :
    coeff (Q p d) (d - 1) = coeff (P p d) d * (d : ZMod p) := by
  rw [Q, Polynomial.coeff_derivative]
  rw [show (d - 1) + 1 = d by omega]
  congr 1
  have h1 : (1 : ZMod p) = Nat.cast (1 : ℕ) := by simp
  rw [h1, ← Nat.cast_add]
  congr 1
  omega

/-- The leading coefficient of `Q p d` is `d` (as an element of `ZMod p`). -/
lemma Q_coeff_pred' (p d : ℕ) [Fact p.Prime] (hd : 1 ≤ d) :
    coeff (Q p d) (d - 1) = (d : ZMod p) := by
  rw [Q_coeff_pred p d hd]
  have hcoeff1 : coeff (P p d) d = 1 := by
    have h : coeff (P p d) ((P p d).natDegree) = 1 := by
      rw [Polynomial.coeff_natDegree]
      exact P_monic p d
    simpa [P_natDegree p d] using h
  rw [hcoeff1, one_mul]

/-- `Q p d` is nonzero as long as `1 ≤ d < p`. -/
lemma Q_ne_zero (p d : ℕ) [Fact p.Prime] (hd : 1 ≤ d) (hdlt : d < p) : Q p d ≠ 0 := by
  have hcoeff : coeff (Q p d) (d - 1) = (d : ZMod p) := Q_coeff_pred' p d hd
  have hd_ne : (d : ZMod p) ≠ 0 := by
    intro h0
    have hpdvd : p ∣ d := (ZMod.natCast_eq_zero_iff d p).mp h0
    exact (not_lt_of_ge (Nat.le_of_dvd hd hpdvd)) hdlt
  intro hQzero
  apply hd_ne
  rw [← hcoeff, hQzero, Polynomial.coeff_zero]

/-- `Q p d` has degree exactly `d - 1` (provided `1 ≤ d < p`). -/
lemma Q_natDegree (p d : ℕ) [Fact p.Prime] (hd : 1 ≤ d) (hdlt : d < p) :
    (Q p d).natDegree = d - 1 := by
  have hPdeg : (P p d).natDegree = d := P_natDegree p d
  have hd_ne : (d : ZMod p) ≠ 0 := by
    intro h0
    have hpdvd : p ∣ d := (ZMod.natCast_eq_zero_iff d p).mp h0
    exact (not_lt_of_ge (Nat.le_of_dvd hd hpdvd)) hdlt
  have hle : (Q p d).natDegree ≤ d - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [Q, Polynomial.coeff_derivative]
    have hgt : d < n + 1 := by omega
    have hcoeff0 : coeff (P p d) (n + 1) = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mp (le_of_eq hPdeg) (n + 1) hgt
    rw [hcoeff0]
    simp
  have hge : d - 1 ≤ (Q p d).natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    rw [Q_coeff_pred' p d hd]
    exact hd_ne
  exact le_antisymm hle hge

/-! ## Evaluation of `Q p d` -/

/-- Evaluating `Q p d` at `r` gives `∑_i ∏_{j≠i} (r + j)`. -/
lemma eval_Q_eq_sum_prod_erase (p d r : ℕ) :
    Polynomial.eval (r : ZMod p) (Q p d) =
      ∑ i ∈ Finset.Icc 1 d, ∏ j ∈ (Finset.Icc 1 d).erase i, ((r + j : ℕ) : ZMod p) := by
  rw [Q, P, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.derivative_X_add_C,
    Polynomial.eval_one, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_add]

/-! ## Theorem A: the distance polynomial identity -/

/-- **Theorem A.** If `r` and `r + d` are both bad digits (with `r + d ≤ p - 1`), then the
distance polynomial `Q p d` vanishes at `r`: `(Q p d).eval r = 0`. -/
theorem eval_Q_eq_zero_of_mem_E_add (p d r : ℕ) [Fact p.Prime]
    (hd : 1 ≤ d) (hr : r ∈ E p) (hradd : r + d ∈ E p) (hle : r + d ≤ p - 1) :
    Polynomial.eval (r : ZMod p) (Q p d) = 0 := by
  have hprime : Nat.Prime p := Fact.out
  have hrIcc : r ∈ Finset.Icc 1 (p - 1) := by
    unfold E at hr
    exact (Finset.mem_filter.mp hr).1
  have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
  have hradd_lt_p : r + d < p := by omega
  have hr_lt_p : r < p := by omega
  -- Both `r` and `r + d` are bad, so their harmonic sums vanish mod `p`.
  have hdvd_r : (p : ℤ) ∣ (harmonic r).num := by
    unfold E at hr
    exact (Finset.mem_filter.mp hr).2
  have hdvd_rd : (p : ℤ) ∣ (harmonic (r + d)).num := by
    unfold E at hradd
    exact (Finset.mem_filter.mp hradd).2
  have hsum_r : (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) = 0 :=
    (num_dvd_iff_sum_inv_zero p r hr_lt_p).mp hdvd_r
  have hsum_rd : (∑ j ∈ Finset.Icc 1 (r + d), ((j : ZMod p)⁻¹)) = 0 :=
    (num_dvd_iff_sum_inv_zero p (r + d) hradd_lt_p).mp hdvd_rd
  -- Subtracting, the middle block `∑_{j=r+1}^{r+d} j⁻¹` also vanishes.
  have hsum_mid : (∑ j ∈ Finset.Icc (r + 1) (r + d), ((j : ZMod p)⁻¹)) = 0 := by
    have hsplit := sum_Icc_split_add (fun j => ((j : ZMod p)⁻¹)) r d
    have h : (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) +
        (∑ j ∈ Finset.Icc (r + 1) (r + d), ((j : ZMod p)⁻¹)) = 0 :=
      hsplit.trans hsum_rd
    rw [hsum_r] at h
    simpa using h
  -- Reindex `j = r + i` to get `∑_{i=1}^d (r+i)⁻¹ = 0`.
  have hsum_re : (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ZMod p)⁻¹)) = 0 := by
    have hreindex : (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ZMod p)⁻¹)) =
        (∑ j ∈ Finset.Icc (r + 1) (r + d), ((j : ZMod p)⁻¹)) := by
      refine Finset.sum_bij (fun i hi => r + i) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_Icc]
        have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        omega
      · intro j hj
        have hj' : r + 1 ≤ j ∧ j ≤ r + d := Finset.mem_Icc.mp hj
        refine ⟨j - r, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      · intro i hi
        rfl
    rw [hreindex, hsum_mid]
  -- Each `r + i` is a unit mod `p`.
  have hunits : ∀ i ∈ Finset.Icc 1 d, IsUnit (((r + i : ℕ) : ZMod p)) := by
    intro i hi
    have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
    have hri_ge : 1 ≤ r + i := by omega
    have hri_le : r + i ≤ p - 1 := by omega
    have hri_lt : r + i < p := by omega
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hprime]
    intro hdvd
    exact (not_lt_of_ge (Nat.le_of_dvd hri_ge hdvd)) hri_lt
  rw [eval_Q_eq_sum_prod_erase]
  rw [sum_prod_erase_eq_mul_inv (Finset.Icc 1 d) (fun i => (((r + i : ℕ) : ZMod p))) hunits]
  rw [hsum_re]
  simp

/-! ## Theorem B: pairwise spacing bound -/

/-- Casting a natural to `ZMod p` is injective on the bad set `E p`. -/
lemma natCast_injOn_E (p : ℕ) [Fact p.Prime] :
    Set.InjOn (fun r : ℕ => (r : ZMod p)) (E p) := by
  intro r1 hr1 r2 hr2 h
  have hprime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hprime.pos
  have hr1Icc : r1 ∈ Finset.Icc 1 (p - 1) := by
    unfold E at hr1
    exact (Finset.mem_filter.mp hr1).1
  have hr2Icc : r2 ∈ Finset.Icc 1 (p - 1) := by
    unfold E at hr2
    exact (Finset.mem_filter.mp hr2).1
  have hr1_le : r1 ≤ p - 1 := (Finset.mem_Icc.mp hr1Icc).2
  have hr2_le : r2 ≤ p - 1 := (Finset.mem_Icc.mp hr2Icc).2
  have hr1_lt : r1 < p := by omega
  have hr2_lt : r2 < p := by omega
  have hmod : r1 % p = r2 % p := (ZMod.natCast_eq_natCast_iff' r1 r2 p).mp h
  rwa [Nat.mod_eq_of_lt hr1_lt, Nat.mod_eq_of_lt hr2_lt] at hmod

/-- **Theorem B.** For each `1 ≤ d < p`, the number of `r ∈ E p` with `r + d ∈ E p` is at most
`d - 1`.  In particular (`d = 1`) no two bad digits are adjacent. -/
theorem E_add_count_le_pred (p d : ℕ) [Fact p.Prime] (hd : 1 ≤ d) (hdlt : d < p) :
    ((E p).filter fun r => r + d ∈ E p).card ≤ d - 1 := by
  have hQne : Q p d ≠ 0 := Q_ne_zero p d hd hdlt
  have hQdeg : (Q p d).natDegree = d - 1 := Q_natDegree p d hd hdlt
  -- The map `r ↦ (r : ZMod p)` is injective on the filter.
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) ((E p).filter fun r => r + d ∈ E p) := by
    intro r1 hr1 r2 hr2 h
    have hr1E : r1 ∈ E p := (Finset.mem_filter.mp hr1).1
    have hr2E : r2 ∈ E p := (Finset.mem_filter.mp hr2).1
    exact (natCast_injOn_E p) hr1E hr2E h
  -- Every element of the filter maps to a root of `Q p d` (Theorem A).
  have hsubset : (((E p).filter fun r => r + d ∈ E p).image (fun r : ℕ => (r : ZMod p))).val
      ⊆ (Q p d).roots := by
    intro x hx
    have hx' : x ∈ (Finset.image (fun r : ℕ => (r : ZMod p)) ((E p).filter fun r => r + d ∈ E p)) := hx
    rcases (Finset.mem_image.mp hx') with ⟨r, hr_filter, hcast⟩
    rw [← hcast]
    have hrE : r ∈ E p := (Finset.mem_filter.mp hr_filter).1
    have hraddE : r + d ∈ E p := (Finset.mem_filter.mp hr_filter).2
    have hradd_le : r + d ≤ p - 1 := by
      have hIcc : r + d ∈ Finset.Icc 1 (p - 1) := by
        unfold E at hraddE
        exact (Finset.mem_filter.mp hraddE).1
      exact (Finset.mem_Icc.mp hIcc).2
    rw [Polynomial.mem_roots hQne]
    exact eval_Q_eq_zero_of_mem_E_add p d r hd hrE hraddE hradd_le
  have hcard_le : (((E p).filter fun r => r + d ∈ E p).image (fun r : ℕ => (r : ZMod p))).card
      ≤ d - 1 := by
    have h := Polynomial.card_le_degree_of_subset_roots (p := Q p d)
      (Z := ((E p).filter fun r => r + d ∈ E p).image (fun r : ℕ => (r : ZMod p))) hsubset
    rwa [hQdeg] at h
  have hcard_image : (((E p).filter fun r => r + d ∈ E p).image (fun r : ℕ => (r : ZMod p))).card =
      ((E p).filter fun r => r + d ∈ E p).card := Finset.card_image_of_injOn hinj
  rwa [← hcard_image]

end Erdos291
