import Erdos291.GapResultant
import Erdos291.BadSetGrowth
import Erdos291.GapPolynomial
import Erdos291.BadSet
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Rat.Lemmas

/-!
# Erdős #291 — coprimality of the distance polynomials `Qd d`, `Qd e`

For each fixed pair of distances `d ≠ e`, only finitely many primes can realize a triple
bad-position pattern `r, r + d, r + e ∈ E p`: by `resultant_eq_zero_of_triple_bad` (in
`Erdos291/GapResultant.lean`) such a prime must divide the fixed integer
`resultant (Qd d) (Qd e)`, so it suffices to show that resultant is nonzero, i.e. that the
integer polynomials `Qd d` and `Qd e` are coprime over `ℚ`.

The coprimality proof splits into three steps.  Working over `ℚ` we set
`QdQ d = (Qd d).map (Int.castRingHom ℚ)` and `RdQ d e = ∏_{j=d+1}^e (X + j)`:

* **Step 1** (`PdQ_separable`, `isCoprime_PdQ_QdQ`): `Pd d = ∏_{i=1}^d (X + i)` is squarefree
  (separable), hence coprime to its derivative `Qd d`.
* **Step 2** (`isCoprime_QdQ_of_isCoprime_deriv_RdQ`): from `P_e = P_d · R` and the product
  rule, coprimality of `Qd d` with `Qd e` reduces to coprimality with `(RdQ d e).derivative`.
* **Step 3** (`isCoprime_QdQ_deriv_RdQ`, Rolle): `Qd d` and `(RdQ d e).derivative` have
  disjoint real roots, hence are coprime.

Steps 1 and 2 are purely algebraic; Step 3 uses Rolle's theorem: `Pd d` has the simple real
roots `-1, …, -d`, so `Qd d` has a root in each gap `(-(i+1), -i)` for `i = 1, …, d-1`; these
`d - 1` distinct roots account for the full degree `d - 1`, hence every root of `Qd d` lies in
`(-d, -1)`.  Likewise every root of `(RdQ d e).derivative` lies in `(-e, -(d+1))`; the two
intervals are disjoint because `d < e` gives `-(d+1) < -d`.  We carry out this argument over
`ℝ` (as `derivative_PR_roots_subset_Ioo`) and transport coprimality back to `ℚ` with
`Polynomial.isCoprime_map`.

Finally `resultant_Qd_ne_zero` combines the three steps with the resultant bridge
`resultant_Qd_ne_zero_of_isCoprime`, giving the capstone: for `d ≠ e` the integer
`resultant (Qd d) (Qd e)` is nonzero, so only finitely many primes are exceptional.

The file also records the easy *sparsity* consequence for each fixed `p`: the set of `r` with
`r, r + d, r + e ∈ E p` has cardinal at most `d - 1`.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

/-! ## The trivial triple-pattern sparsity bound -/

/-- **Triple-pattern sparsity.** For any prime `p` and `1 ≤ d`, the number of bad digits `r`
for which both `r + d` and `r + e` are again bad is at most `d - 1` (the pattern
`{r, r + d, r + e} ⊆ E p` forces `r` into the pairwise-spacing set of `GapPolynomial`). -/
theorem triple_bad_count_le_pred (p d e : ℕ) [Fact p.Prime] (hd : 1 ≤ d) :
    (((E p).filter fun r => r + d ∈ E p).filter fun r => r + e ∈ E p).card ≤ d - 1 := by
  have hsub : (((E p).filter fun r => r + d ∈ E p).filter fun r => r + e ∈ E p) ⊆
      (E p).filter fun r => r + d ∈ E p :=
    Finset.filter_subset (s := (E p).filter fun r => r + d ∈ E p) (p := fun r => r + e ∈ E p)
  exact (Finset.card_le_card hsub).trans (E_add_count_le_pred_all p d hd)

/-! ## The distance polynomials over `ℚ` -/

/-- The map `ℤ → ℚ` used to transport the integer distance polynomials to a field. -/
private lemma intCastRingHom_Rat_injective : Function.Injective (Int.castRingHom ℚ) := by
  intro x y h
  have h' : (x : ℚ) = (y : ℚ) := by simpa using h
  exact Int.cast_injective h'

/-- `Pd d = ∏_{i=1}^d (X + i)` mapped to `ℚ`. -/
noncomputable def PdQ (d : ℕ) : Polynomial ℚ :=
  (Pd d).map (Int.castRingHom ℚ)

/-- `Qd d = (Pd d)'` mapped to `ℚ`. -/
noncomputable def QdQ (d : ℕ) : Polynomial ℚ :=
  (Qd d).map (Int.castRingHom ℚ)

/-- The "tail" polynomial `R = ∏_{j=d+1}^e (X + j)` over `ℚ`, so that `Pd e = Pd d · RdQ d e`. -/
noncomputable def RdQ (d e : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.Icc (d + 1) e, (Polynomial.X + Polynomial.C (j : ℚ))

/-- `PdQ d` as an explicit product of linear factors. -/
lemma PdQ_eq (d : ℕ) :
    PdQ d = ∏ i ∈ Finset.Icc 1 d, (Polynomial.X + Polynomial.C (i : ℚ)) := by
  rw [PdQ, Pd, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- `QdQ d` is the derivative of `PdQ d`. -/
lemma QdQ_deriv (d : ℕ) : QdQ d = Polynomial.derivative (PdQ d) := by
  rw [QdQ, Qd, PdQ]
  rw [Polynomial.derivative_map]

/-- Splitting the product `∏_{j=1}^e f j` at `d`: `(∏_{1}^d) * (∏_{d+1}^e) = ∏_{1}^e`. -/
lemma prod_Icc_mul_Icc_eq_Icc {M : Type*} [CommMonoid M] (f : ℕ → M) (d e : ℕ) (hde : d ≤ e) :
    (∏ j ∈ Finset.Icc 1 d, f j) * (∏ j ∈ Finset.Icc (d + 1) e, f j) =
      ∏ j ∈ Finset.Icc 1 e, f j := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 d, ← Finset.Ico_add_one_right_eq_Icc (d + 1) e,
    ← Finset.Ico_add_one_right_eq_Icc 1 e]
  exact Finset.prod_Ico_consecutive f (by omega : 1 ≤ d + 1) (by omega : d + 1 ≤ e + 1)

/-- For `d ≤ e`, `Pd e = Pd d · RdQ d e`. -/
lemma PdQ_mul_RdQ (d e : ℕ) (hde : d ≤ e) : PdQ e = PdQ d * RdQ d e := by
  rw [PdQ_eq e, PdQ_eq d, RdQ]
  exact (prod_Icc_mul_Icc_eq_Icc (fun j : ℕ => (Polynomial.X + Polynomial.C (j : ℚ))) d e hde).symm

/-! ## Step 1: `Pd d` is separable -/

/-- **Step 1.** `Pd d = ∏_{i=1}^d (X + i)` is separable over `ℚ` (squarefree): its distinct
linear factors are pairwise coprime, so it is coprime to its derivative. -/
lemma PdQ_separable (d : ℕ) : (PdQ d).Separable := by
  rw [PdQ_eq]
  have hprod : (∏ i ∈ Finset.Icc 1 d, (Polynomial.X + Polynomial.C (i : ℚ))) =
      ∏ i ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (-(i : ℚ))) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [sub_eq_add_neg, neg_neg]
  rw [hprod]
  apply (separable_prod_X_sub_C_iff' (ι := ℕ) (F := ℚ)
    (f := fun i : ℕ => -(i : ℚ)) (s := Finset.Icc 1 d)).2
  intro x hx y hy hxy
  have hxy' : (x : ℚ) = (y : ℚ) := by
    simpa using congrArg (fun z : ℚ => -z) hxy
  exact_mod_cast hxy'

/-- `PdQ d` is coprime to its derivative `QdQ d` (Step 1, restated). -/
lemma isCoprime_PdQ_QdQ (d : ℕ) : IsCoprime (PdQ d) (QdQ d) := by
  simpa [Separable, ← QdQ_deriv] using (PdQ_separable d)

/-! ## Step 2: reduce `gcd(Qd d, Qd e)` to `gcd(Qd d, R')` -/

/-- A small forward-version of `IsCoprime.of_mul_add_right_right`: adding a multiple of `x`
to `y` preserves coprimality with `x`. -/
private lemma isCoprime_add_mul_right_right {R : Type*} [CommRing R] {x y z : R}
    (h : IsCoprime x y) : IsCoprime x (z * x + y) := by
  rcases h with ⟨a, b, hab⟩
  refine ⟨a - b * z, b, ?_⟩
  calc
    (a - b * z) * x + b * (z * x + y) = (a * x - (b * z) * x) + (b * (z * x) + b * y) := by
      ring
    _ = a * x + b * y := by ring
    _ = 1 := hab

/-- **Step 2.**  If `Qd d` is coprime to `(RdQ d e).derivative` (and `d ≤ e`), then it is
coprime to `Qd e`: from `P_e = P_d · R` and the product rule,
`P_e' = P_d' R + P_d R'`, so after subtracting the multiple `R · P_d'` of `P_d'` the gcd
reduces to `gcd(P_d', P_d R')`, and Step 1 removes the `P_d` factor. -/
lemma isCoprime_QdQ_of_isCoprime_deriv_RdQ (d e : ℕ) (hde : d ≤ e) :
    IsCoprime (QdQ d) ((RdQ d e).derivative) → IsCoprime (QdQ d) (QdQ e) := by
  intro hR
  have h1 : IsCoprime (PdQ d) (QdQ d) := isCoprime_PdQ_QdQ d
  have h1' : IsCoprime (QdQ d) (PdQ d) := h1.symm
  have h2 : IsCoprime (QdQ d) (PdQ d * (RdQ d e).derivative) := h1'.mul_right hR
  have hQe : QdQ e = (RdQ d e) * (QdQ d) + PdQ d * ((RdQ d e).derivative) := by
    rw [QdQ_deriv]
    rw [PdQ_mul_RdQ d e hde]
    rw [Polynomial.derivative_mul]
    rw [← QdQ_deriv]
    ring
  have h3 : IsCoprime (QdQ d) ((RdQ d e) * (QdQ d) + PdQ d * ((RdQ d e).derivative)) :=
    isCoprime_add_mul_right_right h2
  simpa [hQe] using h3

/-! ## Step 3 (Rolle's theorem) over `ℝ` -/

/-- The generic product `∏_{i=a}^b (X + i)` over `ℝ` (roots at `-a, …, -b`). -/
noncomputable def PR (a b : ℕ) : Polynomial ℝ :=
  ∏ i ∈ Finset.Icc a b, (Polynomial.X + Polynomial.C (i : ℝ))

/-- `PR a b` is monic. -/
lemma PR_monic (a b : ℕ) : (PR a b).Monic := by
  rw [PR]
  exact Polynomial.monic_prod_of_monic (Finset.Icc a b)
    (fun i => Polynomial.X + Polynomial.C (i : ℝ)) (fun i hi => Polynomial.monic_X_add_C (i : ℝ))

/-- `PR a b` has degree `b + 1 - a`. -/
lemma PR_natDegree (a b : ℕ) : (PR a b).natDegree = b + 1 - a := by
  rw [PR]
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc a b)
    (fun i => Polynomial.X + Polynomial.C (i : ℝ)) (fun i hi => Polynomial.monic_X_add_C (i : ℝ))]
  simp only [Polynomial.natDegree_X_add_C]
  rw [← Finset.card_eq_sum_ones]
  exact Nat.card_Icc a b

/-- `-(i : ℝ)` is a root of `PR a b` for `i ∈ [a, b]`. -/
lemma PR_eval_neg (a b i : ℕ) (hi : i ∈ Finset.Icc a b) : (PR a b).eval (-(i : ℝ)) = 0 := by
  rw [PR, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- **Rolle's theorem for polynomials.** Between two real roots `a < b` of `p` there is a real
root of its derivative. -/
lemma exists_deriv_root_between (p : ℝ[X]) {a b : ℝ} (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c : ℝ, a < c ∧ c < b ∧ (p.derivative).eval c = 0 := by
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_zero hab p.continuousOn (ha.trans hb.symm)
  refine ⟨c, hc.1, hc.2, ?_⟩
  simpa [Polynomial.deriv] using hc'

/-- For `i ∈ [a, b-1]`, the derivative of `PR a b` has a root in the gap `(-(i+1), -i)`. -/
lemma exists_deriv_root_in_gap (a b i : ℕ) (ha : 1 ≤ a) (hi : i ∈ Finset.Icc a (b - 1)) :
    ∃ c : ℝ, -((i + 1 : ℕ) : ℝ) < c ∧ c < -(i : ℝ) ∧ (Polynomial.derivative (PR a b)).eval c = 0 := by
  have hi1 : i + 1 ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    have h1 : a ≤ i := (Finset.mem_Icc.mp hi).1
    have h2 : i ≤ b - 1 := (Finset.mem_Icc.mp hi).2
    omega
  have hi0 : i ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    have h1 : a ≤ i := (Finset.mem_Icc.mp hi).1
    have h2 : i ≤ b - 1 := (Finset.mem_Icc.mp hi).2
    omega
  have hlt : -((i + 1 : ℕ) : ℝ) < -(i : ℝ) := by
    have h : (i : ℝ) < ((i + 1 : ℕ) : ℝ) := by norm_num
    exact neg_lt_neg h
  exact exists_deriv_root_between (PR a b) hlt (PR_eval_neg a b (i + 1) hi1) (PR_eval_neg a b i hi0)

/-- A chosen root of `(PR a b)'` in the gap indexed by `i ∈ [a, b-1]` (for `1 ≤ a`). -/
noncomputable def gapRoot (a b : ℕ) (ha : 1 ≤ a) (i : ℕ) (hi : i ∈ Finset.Icc a (b - 1)) : ℝ :=
  Classical.choose (exists_deriv_root_in_gap a b i ha hi)

/-- The chosen gap root lies in the open gap and is a root of `(PR a b)'`. -/
lemma gapRoot_spec (a b : ℕ) (ha : 1 ≤ a) (i : ℕ) (hi : i ∈ Finset.Icc a (b - 1)) :
    -((i + 1 : ℕ) : ℝ) < gapRoot a b ha i hi ∧ gapRoot a b ha i hi < -(i : ℝ) ∧
      (Polynomial.derivative (PR a b)).eval (gapRoot a b ha i hi) = 0 :=
  Classical.choose_spec (exists_deriv_root_in_gap a b i ha hi)

/-- Distinct gaps have distinct chosen roots: if `i < j` then `gapRoot i ≠ gapRoot j`. -/
lemma gapRoot_ne_of_lt (a b : ℕ) (ha : 1 ≤ a) {i j : ℕ} (hi : i ∈ Finset.Icc a (b - 1))
    (hj : j ∈ Finset.Icc a (b - 1)) (hij : i < j) : gapRoot a b ha i hi ≠ gapRoot a b ha j hj := by
  have hspec_i := gapRoot_spec a b ha i hi
  have hspec_j := gapRoot_spec a b ha j hj
  intro h
  have hnat : i + 1 ≤ j := by omega
  have hcast : ((i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hnat
  have hbound : -(j : ℝ) ≤ -((i + 1 : ℕ) : ℝ) := neg_le_neg hcast
  have hchain : gapRoot a b ha j hj < gapRoot a b ha j hj := by
    calc
      gapRoot a b ha j hj < -(j : ℝ) := hspec_j.2.1
      _ ≤ -((i + 1 : ℕ) : ℝ) := hbound
      _ < gapRoot a b ha i hi := hspec_i.1
      _ = gapRoot a b ha j hj := h
  exact (lt_irrefl (gapRoot a b ha j hj)) hchain

/-- The gap-root function is injective on `[a, b-1]`. -/
lemma gapRoot_injective (a b : ℕ) (ha : 1 ≤ a) :
    Function.Injective (fun i : {i // i ∈ Finset.Icc a (b - 1)} => gapRoot a b ha i.1 i.2) := by
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have hlt : i.1 < j.1 ∨ j.1 < i.1 := by omega
  rcases hlt with hlt | hlt
  · exact (gapRoot_ne_of_lt a b ha i.2 j.2 hlt) hij
  · exact (gapRoot_ne_of_lt a b ha j.2 i.2 hlt) hij.symm

/-- The finite set of one gap-root per gap of `PR a b` (for `1 ≤ a`). -/
noncomputable def gapRoots (a b : ℕ) (ha : 1 ≤ a) : Finset ℝ :=
  (Finset.Icc a (b - 1)).attach.image (fun i : {i // i ∈ Finset.Icc a (b - 1)} => gapRoot a b ha i.1 i.2)

/-- There are `b - a` distinct gap roots (for `1 ≤ a ≤ b`). -/
lemma gapRoots_card (a b : ℕ) (hab : a ≤ b) (ha : 1 ≤ a) : (gapRoots a b ha).card = b - a := by
  rw [gapRoots]
  rw [Finset.card_image_of_injective (Finset.Icc a (b - 1)).attach (gapRoot_injective a b ha)]
  rw [Finset.card_attach]
  rw [Nat.card_Icc]
  omega

/-- Every gap root lies in `(-b, -a)`. -/
lemma gapRoots_mem_Ioo (a b : ℕ) (ha : 1 ≤ a) {y : ℝ} (hy : y ∈ gapRoots a b ha) :
    -(b : ℝ) < y ∧ y < -(a : ℝ) := by
  rcases Finset.mem_image.mp hy with ⟨i, hi, hy_eq⟩
  have hspec := gapRoot_spec a b ha i.1 i.2
  constructor
  · rw [← hy_eq]
    have hlo : i.1 + 1 ≤ b := by
      have h1 : a ≤ i.1 := (Finset.mem_Icc.mp i.2).1
      have h2 : i.1 ≤ b - 1 := (Finset.mem_Icc.mp i.2).2
      omega
    have hcast : ((i.1 + 1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast hlo
    exact lt_of_le_of_lt (neg_le_neg hcast) hspec.1
  · rw [← hy_eq]
    have hge : a ≤ i.1 := (Finset.mem_Icc.mp i.2).1
    have hcast : (a : ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast hge
    exact lt_of_lt_of_le hspec.2.1 (neg_le_neg hcast)

/-- `(PR a b)'` is nonzero when `a ≤ b` (it is the derivative of a monic polynomial of positive
degree over the characteristic-zero field `ℝ`). -/
lemma derivative_PR_ne_zero (a b : ℕ) (hab : a ≤ b) : Polynomial.derivative (PR a b) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero, PR_natDegree]
  omega

/-- `(PR a b)'` has degree `b - a`. -/
lemma derivative_PR_natDegree (a b : ℕ) : (Polynomial.derivative (PR a b)).natDegree = b - a := by
  rw [Polynomial.natDegree_derivative, PR_natDegree]
  omega

/-- Every gap root is a root of `(PR a b)'`. -/
lemma gapRoots_subset_roots (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    gapRoots a b ha ⊆ (Polynomial.derivative (PR a b)).roots.toFinset := by
  intro y hy
  rw [Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (derivative_PR_ne_zero a b hab)]
  rcases Finset.mem_image.mp hy with ⟨i, hi, hy_eq⟩
  have hspec := gapRoot_spec a b ha i.1 i.2
  rw [← hy_eq]
  exact hspec.2.2

/-- `(PR a b)'` has exactly `b - a` roots (counted with multiplicity), all real. -/
lemma derivative_PR_roots_card (a b : ℕ) (hab : a ≤ b) (ha : 1 ≤ a) :
    (Polynomial.derivative (PR a b)).roots.card = b - a := by
  apply le_antisymm
  · have h := Polynomial.card_roots' (Polynomial.derivative (PR a b))
    rwa [derivative_PR_natDegree] at h
  · rw [← gapRoots_card a b hab ha]
    calc
      (gapRoots a b ha).card ≤ (Polynomial.derivative (PR a b)).roots.toFinset.card :=
        Finset.card_le_card (gapRoots_subset_roots a b ha hab)
      _ ≤ (Polynomial.derivative (PR a b)).roots.card := Multiset.toFinset_card_le _

/-- `(PR a b)'` splits over `ℝ` into linear factors. -/
lemma derivative_PR_splits (a b : ℕ) (hab : a ≤ b) (ha : 1 ≤ a) :
    (Polynomial.derivative (PR a b)).Splits := by
  exact Polynomial.splits_iff_card_roots.mpr (by
    rw [derivative_PR_roots_card a b hab ha, derivative_PR_natDegree a b])

/-- **Rolle step.** Every root of `(PR a b)'` lies in the open interval `(-b, -a)` (for
`1 ≤ a ≤ b`). -/
lemma derivative_PR_roots_subset_Ioo (a b : ℕ) (hab : a ≤ b) (ha : 1 ≤ a) (x : ℝ)
    (hx : (Polynomial.derivative (PR a b)).IsRoot x) :
    -(b : ℝ) < x ∧ x < -(a : ℝ) := by
  have htoFinset_eq : (Polynomial.derivative (PR a b)).roots.toFinset = gapRoots a b ha := by
    have hcard : (Polynomial.derivative (PR a b)).roots.toFinset.card ≤ (gapRoots a b ha).card := by
      calc
        (Polynomial.derivative (PR a b)).roots.toFinset.card
            ≤ (Polynomial.derivative (PR a b)).roots.card := Multiset.toFinset_card_le _
        _ = b - a := derivative_PR_roots_card a b hab ha
        _ = (gapRoots a b ha).card := (gapRoots_card a b hab ha).symm
    exact (Finset.eq_of_subset_of_card_le (gapRoots_subset_roots a b ha hab) hcard).symm
  have hx_toFinset : x ∈ (Polynomial.derivative (PR a b)).roots.toFinset := by
    rw [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (derivative_PR_ne_zero a b hab)]
    exact hx
  have hxS : x ∈ gapRoots a b ha := htoFinset_eq ▸ hx_toFinset
  exact gapRoots_mem_Ioo a b ha hxS

/-- Two split polynomials over `ℝ` with no common root are coprime. -/
lemma isCoprime_of_splits_no_common_root {f g : ℝ[X]} (hf : f.Splits) (hf0 : f ≠ 0)
    (hfg : ∀ x : ℝ, f.IsRoot x → ¬ g.IsRoot x) : IsCoprime f g := by
  rw [← EuclideanDomain.gcd_isUnit_iff]
  by_contra hnot
  have hsplit_gcd : (EuclideanDomain.gcd f g).Splits :=
    Polynomial.Splits.of_dvd hf hf0 (EuclideanDomain.gcd_dvd_left f g)
  have hgcd_ne : EuclideanDomain.gcd f g ≠ 0 := by
    intro hz
    have hf0' : f = 0 := by
      rw [← zero_dvd_iff]
      simpa [hz] using (EuclideanDomain.gcd_dvd_left f g)
    exact hf0 hf0'
  have hdeg_ne : (EuclideanDomain.gcd f g).degree ≠ 0 := by
    intro hdeg0
    have hunit : IsUnit (EuclideanDomain.gcd f g) := by
      rw [Polynomial.isUnit_iff_degree_eq_zero]
      exact hdeg0
    exact hnot hunit
  obtain ⟨a, ha⟩ := hsplit_gcd.exists_eval_eq_zero hdeg_ne
  have ha_root : (EuclideanDomain.gcd f g).IsRoot a := by
    simpa [Polynomial.IsRoot] using ha
  have hcommon := (Polynomial.isRoot_gcd_iff_isRoot_left_right (f := f) (g := g)).mp ha_root
  exact hfg a hcommon.1 hcommon.2

/-! ## Step 3: transporting the Rolle result to `ℚ` -/

/-- `Pd d` mapped to `ℝ` is `PR 1 d`. -/
lemma Pd_map_R (d : ℕ) : (Pd d).map (Int.castRingHom ℝ) = PR 1 d := by
  rw [Pd, PR, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- `QdR d`, the derivative of `PR 1 d` over `ℝ`, equals `QdQ d` mapped to `ℝ`. -/
lemma QdR_map (d : ℕ) : Polynomial.derivative (PR 1 d) = (QdQ d).map (algebraMap ℚ ℝ) := by
  rw [QdQ, Qd]
  rw [Polynomial.map_map]
  have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ :=
    RingHom.eq_intCast' ((algebraMap ℚ ℝ).comp (Int.castRingHom ℚ))
  rw [hcomp]
  rw [← Polynomial.derivative_map, Pd_map_R]

/-- `RdR d e`, the product `∏_{j=d+1}^e (X+j)` over `ℝ`, equals `RdQ d e` mapped to `ℝ`. -/
lemma RdR_map (d e : ℕ) : PR (d + 1) e = (RdQ d e).map (algebraMap ℚ ℝ) := by
  rw [PR, RdQ, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp

/-- **Step 3 (Rolle).** For `1 ≤ d < e`, `Qd d` and `(∏_{j=d+1}^e (X+j))'` have disjoint real
roots, hence are coprime over `ℚ`. -/
lemma isCoprime_QdQ_deriv_RdQ (d e : ℕ) (hd : 1 ≤ d) (hde : d < e) :
    IsCoprime (QdQ d) ((RdQ d e).derivative) := by
  have hR : IsCoprime ((QdQ d).map (algebraMap ℚ ℝ)) (((RdQ d e).derivative).map (algebraMap ℚ ℝ)) := by
    rw [← QdR_map, ← Polynomial.derivative_map, ← RdR_map]
    refine isCoprime_of_splits_no_common_root ?_ ?_ ?_
    · exact derivative_PR_splits 1 d hd (by omega : 1 ≤ 1)
    · exact derivative_PR_ne_zero 1 d hd
    · intro x hx hx'
      have hxIoo := derivative_PR_roots_subset_Ioo 1 d hd (by omega : 1 ≤ 1) x hx
      have hx'Ioo := derivative_PR_roots_subset_Ioo (d + 1) e (by omega : d + 1 ≤ e) (by omega : 1 ≤ d + 1) x hx'
      have hlt_d : -((d + 1 : ℕ) : ℝ) < -(d : ℝ) := by
        have : (d : ℝ) < ((d + 1 : ℕ) : ℝ) := by norm_num
        exact neg_lt_neg this
      nlinarith [hxIoo.1, hx'Ioo.2, hlt_d]
  exact (Polynomial.isCoprime_map (f := algebraMap ℚ ℝ) (p := QdQ d) (q := (RdQ d e).derivative)).mp hR

/-! ## The resultant bridge and the capstone -/

/-- **Resultant bridge.**  If the distance polynomials `QdQ d` and `QdQ e` are coprime over
`ℚ`, then the integer resultant `resultant (Qd d) (Qd e)` is nonzero.  (Over a field, a zero
resultant means a common root, hence non-coprimality, by `resultant_eq_zero_iff`; the
resultant commutes with the injective map `ℤ → ℚ` by `resultant_map_map`.) -/
theorem resultant_Qd_ne_zero_of_isCoprime (d e : ℕ) (hcop : IsCoprime (QdQ d) (QdQ e)) :
    Polynomial.resultant (Qd d) (Qd e) ≠ 0 := by
  have hresQ : Polynomial.resultant (QdQ d) (QdQ e) ≠ 0 := by
    intro h0
    have h := (Polynomial.resultant_eq_zero_iff (f := QdQ d) (g := QdQ e)).mp h0
    exact h.2 hcop
  have hdegd : (QdQ d).natDegree = (Qd d).natDegree :=
    Polynomial.natDegree_map_eq_of_injective intCastRingHom_Rat_injective (Qd d)
  have hdege : (QdQ e).natDegree = (Qd e).natDegree :=
    Polynomial.natDegree_map_eq_of_injective intCastRingHom_Rat_injective (Qd e)
  have hmap : (Int.castRingHom ℚ) (Polynomial.resultant (Qd d) (Qd e)) =
      Polynomial.resultant (QdQ d) (QdQ e) := by
    change (Int.castRingHom ℚ) (Polynomial.resultant (Qd d) (Qd e)
        (Qd d).natDegree (Qd e).natDegree) =
      Polynomial.resultant (QdQ d) (QdQ e) (QdQ d).natDegree (QdQ e).natDegree
    rw [hdegd, hdege]
    rw [QdQ, QdQ]
    exact (Polynomial.resultant_map_map (φ := Int.castRingHom ℚ) (f := Qd d) (g := Qd e)
      (m := (Qd d).natDegree) (n := (Qd e).natDegree)).symm
  have hφ : (Int.castRingHom ℚ) (Polynomial.resultant (Qd d) (Qd e)) ≠ 0 := by
    rw [hmap]
    exact hresQ
  intro hz
  apply hφ
  rw [hz, map_zero]

/-- **The capstone.** For distances `d ≠ e` (both at least `1`), the integer polynomials
`Qd d` and `Qd e` are coprime, i.e. `resultant (Qd d) (Qd e) ≠ 0`.  Hence (with
`resultant_eq_zero_of_triple_bad`) only finitely many primes realize a triple bad-position
pattern `r, r + d, r + e ∈ E p`. -/
theorem resultant_Qd_ne_zero (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) (hde : d ≠ e) :
    Polynomial.resultant (Qd d) (Qd e) ≠ 0 := by
  by_cases hde' : d < e
  · have hRolle : IsCoprime (QdQ d) ((RdQ d e).derivative) := isCoprime_QdQ_deriv_RdQ d e hd hde'
    have hcop : IsCoprime (QdQ d) (QdQ e) :=
      isCoprime_QdQ_of_isCoprime_deriv_RdQ d e (le_of_lt hde') hRolle
    exact resultant_Qd_ne_zero_of_isCoprime d e hcop
  · have hed : e < d := by omega
    have hRolle : IsCoprime (QdQ e) ((RdQ e d).derivative) := isCoprime_QdQ_deriv_RdQ e d he hed
    have hcop_e : IsCoprime (QdQ e) (QdQ d) :=
      isCoprime_QdQ_of_isCoprime_deriv_RdQ e d (le_of_lt hed) hRolle
    exact resultant_Qd_ne_zero_of_isCoprime d e hcop_e.symm

/-- **Finite exceptional primes.** For fixed distances `d ≠ e` (both `≥ 1`), there is a
nonzero integer `N` (the absolute value of `resultant (Qd d) (Qd e)`) such that every prime
`p` realizing a triple bad-position pattern `r, r + d, r + e ∈ E p` divides `N`.  Hence only
finitely many primes admit the fixed local pattern. -/
theorem finite_exceptional_primes (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e) (hde : d ≠ e) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∀ p : ℕ, Nat.Prime p →
        (∃ r : ℕ, r ∈ E p ∧ r + d ∈ E p ∧ r + e ∈ E p) → p ∣ N := by
  refine ⟨(Polynomial.resultant (Qd d) (Qd e)).natAbs, ?_, ?_⟩
  · have hres : Polynomial.resultant (Qd d) (Qd e) ≠ 0 :=
      resultant_Qd_ne_zero d e hd he hde
    intro hN
    exact hres (Int.natAbs_eq_zero.mp hN)
  · intro p hp ⟨r, hr, hradd, hre⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hle : r + max d e ≤ p - 1 := by
      by_cases hdle : d ≤ e
      · have hre_le : r + e ≤ p - 1 := by
          unfold E at hre
          exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hre).1).2
        simpa [max_eq_right hdle] using hre_le
      · have hde_le : e ≤ d := le_of_not_ge hdle
        have hradd_le : r + d ≤ p - 1 := by
          unfold E at hradd
          exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hradd).1).2
        simpa [max_eq_left hde_le] using hradd_le
    have hz : ((Polynomial.resultant (Qd d) (Qd e) : ℤ) : ZMod p) = 0 :=
      resultant_eq_zero_of_triple_bad p d e r hd he hr hradd hre hle
    have hdvdZ : (p : ℤ) ∣ (Polynomial.resultant (Qd d) (Qd e) : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (Polynomial.resultant (Qd d) (Qd e)) p).mp hz
    exact (Int.natCast_dvd (m := p) (n := Polynomial.resultant (Qd d) (Qd e))).mp hdvdZ

end Erdos291
