import Erdos291.GapPolynomial
import Erdos291.BadSet
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod

/-!
# Erdős #291 — unconditional growth of the bad set `E p`

For a prime `p`, the bad set `E p ⊆ {1, …, p - 1}` is known (from
`Erdos291/GapPolynomial.lean`) to satisfy the pairwise-spacing bound

  `#{r ∈ E p | r + d ∈ E p} ≤ d - 1` for every `1 ≤ d < p`.

In this file we run the standard *block + Cauchy–Schwarz* argument on top of that bound
and conclude that `|E p|` is at most `≪ p^(2/3)`.  Concretely, we prove the exact cubic
bound `|E p|³ ≤ 64 p²` (unconditionally, for any prime `p`).

The argument is split into a general combinatorial lemma (valid for any finite `S ⊆ [1, n]`
with the same spacing property) and its instantiation to `S = E p`, `n = p - 1`:

1. Fix a block length `D ≥ 1` and split `[1, n]` into `⌈n / D⌉ + 1` consecutive blocks of
   length `D`; let `n_i` be the number of `S`-elements in block `i` and `M` the number of
   blocks.
2. **Upper bound on in-block pairs.** Pairs of distinct elements of `S` lying in one block
   are at distance `< D`, so their number is at most the number of `(r, r + d)` with
   `1 ≤ d < D` and `r, r + d ∈ S`, which by the spacing bound is `≤ Σ_{d=1}^{D-1} (d-1)`.
3. **Lower bound by Cauchy–Schwarz.** With `Σ n_i = N` and `M` blocks,
   `Σ n_i² ≥ N² / M`, i.e. `Σ n_i(n_i - 1) ≥ N²/M - N`.
4. Combining gives `N² ≤ M (N + D²)` with `M ≤ n/D + 1`; the choice `D = ⌊√N⌋ + 1`
   then yields `N³ ≤ 64 n²`.
-/

open scoped BigOperators

namespace Erdos291

/-- The `i`-th block of length `D`: the consecutive integers `i*D + 1, …, (i+1)*D`. -/
def block (D i : ℕ) : Finset ℕ := Finset.Icc (i * D + 1) ((i + 1) * D)

/-- For `1 ≤ r` and `1 ≤ D`, `r` lies in block `i` exactly when `(r - 1) / D = i`. -/
lemma mem_block_iff (D i r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r) :
    r ∈ block D i ↔ (r - 1) / D = i := by
  rw [block, Finset.mem_Icc]
  constructor
  · intro h
    have h1 : i * D ≤ r - 1 := by omega
    have h2 : r - 1 < (i + 1) * D := by
      have hlt : r - 1 < r := by omega
      have hle : r ≤ (i + 1) * D := by omega
      omega
    exact Nat.div_eq_of_lt_le h1 h2
  · intro h
    have hle : i * D ≤ r - 1 := by
      simpa [h] using Nat.div_mul_le_self (r - 1) D
    have hlt' : r - 1 < D * (i + 1) := by
      simpa [h] using Nat.lt_mul_div_succ (r - 1) hD
    have hlt : r - 1 < (i + 1) * D := by rwa [Nat.mul_comm] at hlt'
    omega

/-- Two (distinct) elements of one block are at distance `< D`. -/
lemma dist_lt_of_mem_block (D i r s : ℕ) (_hD : 1 ≤ D) (hrs : r < s)
    (hr : r ∈ block D i) (hs : s ∈ block D i) : s - r < D := by
  have hle_r : i * D + 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hle_s : s ≤ (i + 1) * D := (Finset.mem_Icc.mp hs).2
  have hexpand : (i + 1) * D = i * D + D := by rw [Nat.add_mul, Nat.one_mul]
  rw [hexpand] at hle_s
  omega

/-- Distinct blocks are disjoint. -/
lemma block_disjoint (D : ℕ) (hD : 1 ≤ D) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (block D i) (block D j) := by
  rw [Finset.disjoint_left]
  intro r hri hrj
  have hr_pos : 1 ≤ r := by
    have h : i * D + 1 ≤ r := (Finset.mem_Icc.mp hri).1
    omega
  have hi : (r - 1) / D = i := (mem_block_iff D i r hD hr_pos).1 hri
  have hj : (r - 1) / D = j := (mem_block_iff D j r hD hr_pos).1 hrj
  exact hij (hi.symm.trans hj)

/-- The intersections of `S` with distinct blocks are disjoint. -/
lemma badBlock_disjoint (S : Finset ℕ) (D : ℕ) (hD : 1 ≤ D) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (S.filter fun r => r ∈ block D i) (S.filter fun r => r ∈ block D j) := by
  rw [Finset.disjoint_left]
  intro r hri hrj
  exact Finset.disjoint_left.mp (block_disjoint D hD hij) (Finset.mem_filter.mp hri).2
    (Finset.mem_filter.mp hrj).2

/-! ## Counting pairs by distance -/

/-- Ordered pairs `(r, r + d)` with `r, r + d ∈ S` and `0 < d < D` (recorded "upwards"). -/
def upPairs (S : Finset ℕ) (D : ℕ) : Finset (ℕ × ℕ) :=
  (S.product S).filter fun p => p.1 < p.2 ∧ p.2 - p.1 < D

/-- Ordered pairs `(r, r + d)` with `r, r + d ∈ S` and `0 < d < D` (recorded "downwards"). -/
def downPairs (S : Finset ℕ) (D : ℕ) : Finset (ℕ × ℕ) :=
  (S.product S).filter fun p => p.2 < p.1 ∧ p.1 - p.2 < D

/-- For fixed `d ∈ [1, D - 1]`, the pairs in `upPairs` at distance `d` biject with
`{r ∈ S | r + d ∈ S}`. -/
lemma upPairs_fiber_card_eq (S : Finset ℕ) (D d : ℕ) (hd : d ∈ Finset.Icc 1 (D - 1)) :
    ((upPairs S D).filter fun p => p.2 - p.1 = d).card = (S.filter fun r => r + d ∈ S).card := by
  classical
  have hd_ge : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd_le : d ≤ D - 1 := (Finset.mem_Icc.mp hd).2
  have hdlt : d < D := by omega
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    have hfilter := Finset.mem_filter.mp hp
    have hpd : p.2 - p.1 = d := hfilter.2
    have hpup := Finset.mem_filter.mp hfilter.1
    have hprod := Finset.mem_product.mp hpup.1
    have hplt : p.1 < p.2 := hpup.2.1
    rw [Finset.mem_filter]
    refine ⟨hprod.1, ?_⟩
    have hp2eq : p.2 = p.1 + d := by omega
    simpa [hp2eq] using hprod.2
  · intro p₁ hp₁ p₂ hp₂ h
    have hd1 : p₁.2 - p₁.1 = d := (Finset.mem_filter.mp hp₁).2
    have hd2 : p₂.2 - p₂.1 = d := (Finset.mem_filter.mp hp₂).2
    have hlt1 : p₁.1 < p₁.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₁).1).2.1
    have hlt2 : p₂.1 < p₂.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp₂).1).2.1
    apply Prod.ext
    · exact h
    · omega
  · intro r hr
    have hrf := Finset.mem_filter.mp hr
    refine ⟨(r, r + d), ?_, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · rw [upPairs, Finset.mem_filter]
      constructor
      · exact Finset.mk_mem_product hrf.1 hrf.2
      · constructor <;> (dsimp; omega)
    · omega

/-- `upPairs` has cardinality `Σ_{d=1}^{D-1} #{r ∈ S | r + d ∈ S}`. -/
lemma upPairs_card_eq (S : Finset ℕ) (D : ℕ) :
    (upPairs S D).card = ∑ d ∈ Finset.Icc 1 (D - 1), (S.filter fun r => r + d ∈ S).card := by
  classical
  have hmap : Set.MapsTo (fun p : ℕ × ℕ => p.2 - p.1) (upPairs S D) (Finset.Icc 1 (D - 1)) := by
    intro p hp
    change p.2 - p.1 ∈ Finset.Icc 1 (D - 1)
    rw [Finset.mem_Icc]
    have hp' : p.1 < p.2 ∧ p.2 - p.1 < D := (Finset.mem_filter.mp hp).2
    constructor <;> omega
  calc
    (upPairs S D).card
        = ∑ d ∈ Finset.Icc 1 (D - 1), ((upPairs S D).filter fun p => p.2 - p.1 = d).card := by
          exact Finset.card_eq_sum_card_fiberwise (s := upPairs S D) (t := Finset.Icc 1 (D - 1))
            (f := fun p : ℕ × ℕ => p.2 - p.1) hmap
    _ = ∑ d ∈ Finset.Icc 1 (D - 1), (S.filter fun r => r + d ∈ S).card := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          exact upPairs_fiber_card_eq S D d hd

/-- `downPairs` has the same cardinality as `upPairs` (swap the two coordinates). -/
lemma downPairs_card_eq (S : Finset ℕ) (D : ℕ) :
    (downPairs S D).card = (upPairs S D).card := by
  classical
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    rw [downPairs, Finset.mem_filter] at hp
    rcases hp with ⟨hprod, h⟩
    have hpc := Finset.mem_product.mp hprod
    rw [upPairs, Finset.mem_filter]
    constructor
    · exact Finset.mk_mem_product hpc.2 hpc.1
    · exact h
  · intro p₁ hp₁ p₂ hp₂ h
    have h₁ : p₁.2 = p₂.2 := by
      simpa using congrArg Prod.fst h
    have h₂ : p₁.1 = p₂.1 := by
      simpa using congrArg Prod.snd h
    exact Prod.ext h₂ h₁
  · intro q hq
    rw [upPairs, Finset.mem_filter] at hq
    rcases hq with ⟨hprod, h⟩
    have hqc := Finset.mem_product.mp hprod
    refine ⟨(q.2, q.1), ?_, rfl⟩
    rw [downPairs, Finset.mem_filter]
    constructor
    · exact Finset.mk_mem_product hqc.2 hqc.1
    · exact h

/-! ## The block decomposition -/

/-- The off-diagonal pairs `(a, b) ∈ S × S` (`a ≠ b`) that lie in a common block. -/
def sameBlockOffDiag (S : Finset ℕ) (n D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n / D + 1)).biUnion fun i => (S.filter fun r => r ∈ block D i).offDiag

/-- The block decomposition counts every element of `S ⊆ [1, n]` exactly once. -/
lemma sum_block_card_eq_card (S : Finset ℕ) (n D : ℕ) (hD : 1 ≤ D)
    (hS : S ⊆ Finset.Icc 1 n) :
    (∑ i ∈ Finset.range (n / D + 1), (S.filter fun r => r ∈ block D i).card) = S.card := by
  classical
  have hmap : Set.MapsTo (fun r : ℕ => (r - 1) / D) S (Finset.range (n / D + 1)) := by
    intro r hr
    change (r - 1) / D ∈ Finset.range (n / D + 1)
    rw [Finset.mem_range]
    have hrIcc : r ∈ Finset.Icc 1 n := hS hr
    have hr_le : r ≤ n := (Finset.mem_Icc.mp hrIcc).2
    apply (Nat.div_lt_iff_lt_mul hD).mpr
    have hn : n < (n / D + 1) * D := by
      rw [Nat.mul_comm]
      exact Nat.lt_mul_div_succ n hD
    omega
  have hfiber := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.range (n / D + 1))
    (f := fun r : ℕ => (r - 1) / D) hmap
  rw [hfiber]
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.card_bij (fun r _ => r) ?_ ?_ ?_
  · intro r hr
    have hr' : r ∈ S ∧ r ∈ block D i := Finset.mem_filter.mp hr
    rw [Finset.mem_filter]
    refine ⟨hr'.1, ?_⟩
    have hrIcc : r ∈ Finset.Icc 1 n := hS hr'.1
    have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
    exact (mem_block_iff D i r hD hr_ge).1 hr'.2
  · intro r₁ hr₁ r₂ hr₂ h
    exact h
  · intro r hr
    have hr' : r ∈ S ∧ (r - 1) / D = i := Finset.mem_filter.mp hr
    refine ⟨r, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨hr'.1, ?_⟩
    have hrIcc : r ∈ Finset.Icc 1 n := hS hr'.1
    have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
    exact (mem_block_iff D i r hD hr_ge).2 hr'.2

/-- The cardinality of `sameBlockOffDiag` is `Σ_i (n_i² - n_i)`. -/
lemma sameBlockOffDiag_card (S : Finset ℕ) (n D : ℕ) (hD : 1 ≤ D) (_hS : S ⊆ Finset.Icc 1 n) :
    (sameBlockOffDiag S n D).card = ∑ i ∈ Finset.range (n / D + 1),
      ((S.filter fun r => r ∈ block D i).card ^ 2 - (S.filter fun r => r ∈ block D i).card) := by
  classical
  calc
    (sameBlockOffDiag S n D).card
        = ∑ i ∈ Finset.range (n / D + 1), ((S.filter fun r => r ∈ block D i).offDiag).card := by
          rw [sameBlockOffDiag]
          refine Finset.card_biUnion ?_
          intro i hi j hj hij
          change Disjoint ((S.filter fun r => r ∈ block D i).offDiag)
            ((S.filter fun r => r ∈ block D j).offDiag)
          rw [Finset.disjoint_left]
          intro p hpi hpj
          have hp1i : p.1 ∈ S.filter fun r => r ∈ block D i := (Finset.mem_offDiag.mp hpi).1
          have hp1j : p.1 ∈ S.filter fun r => r ∈ block D j := (Finset.mem_offDiag.mp hpj).1
          exact Finset.disjoint_left.mp (badBlock_disjoint S D hD hij) hp1i hp1j
    _ = ∑ i ∈ Finset.range (n / D + 1),
          ((S.filter fun r => r ∈ block D i).card ^ 2 - (S.filter fun r => r ∈ block D i).card) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [pow_two, Finset.offDiag_card]

/-- Same-block off-diagonal pairs are "close" pairs: they belong to `upPairs ∪ downPairs`. -/
lemma sameBlockOffDiag_subset (S : Finset ℕ) (n D : ℕ) (hD : 1 ≤ D) (_hS : S ⊆ Finset.Icc 1 n) :
    sameBlockOffDiag S n D ⊆ upPairs S D ∪ downPairs S D := by
  intro p hp
  rw [sameBlockOffDiag, Finset.mem_biUnion] at hp
  rcases hp with ⟨i, hi, hpi⟩
  rw [Finset.mem_offDiag] at hpi
  rcases hpi with ⟨hp1i, hp2i, hne⟩
  have hp1b : p.1 ∈ block D i := (Finset.mem_filter.mp hp1i).2
  have hp2b : p.2 ∈ block D i := (Finset.mem_filter.mp hp2i).2
  by_cases hlt : p.1 < p.2
  · rw [Finset.mem_union]
    left
    rw [upPairs, Finset.mem_filter]
    constructor
    · exact Finset.mk_mem_product (Finset.mem_filter.mp hp1i).1 (Finset.mem_filter.mp hp2i).1
    · exact ⟨hlt, dist_lt_of_mem_block D i p.1 p.2 hD hlt hp1b hp2b⟩
  · rw [Finset.mem_union]
    right
    have hgt : p.2 < p.1 := by omega
    rw [downPairs, Finset.mem_filter]
    constructor
    · exact Finset.mk_mem_product (Finset.mem_filter.mp hp1i).1 (Finset.mem_filter.mp hp2i).1
    · exact ⟨hgt, dist_lt_of_mem_block D i p.2 p.1 hD hgt hp2b hp1b⟩

/-! ## The general spacing-to-growth lemma -/

/-- **Block inequality.** If `S ⊆ [1, n]` satisfies the spacing condition, then for any block
length `D ≥ 1`, `|S|² ≤ (n / D + 1) · (|S| + D²)`. -/
lemma card_sq_le_of_spacing (S : Finset ℕ) (n D : ℕ) (hD : 1 ≤ D)
    (hS : S ⊆ Finset.Icc 1 n)
    (hsp : ∀ d, 1 ≤ d → (S.filter fun r => r + d ∈ S).card ≤ d - 1) :
    ((S.card : ℝ) ^ 2) ≤ ((n / D + 1 : ℕ) : ℝ) * (((S.card : ℝ)) + (D : ℝ) ^ 2) := by
  classical
  let B : ℕ → Finset ℕ := fun i => S.filter fun r => r ∈ block D i
  let I : Finset ℕ := Finset.range (n / D + 1)
  let N : ℝ := S.card
  let M : ℝ := (n / D + 1 : ℕ)
  let sumSq : ℝ := ∑ i ∈ I, ((B i).card : ℝ) ^ 2
  -- (1) partition: Σ n_i = |S|
  have hsum : (∑ i ∈ I, (B i).card) = S.card := by
    simpa [I, B] using sum_block_card_eq_card S n D hD hS
  -- (2) Σ n_i² = |sameBlockOffDiag| + |S|
  have hsq : (∑ i ∈ I, (B i).card ^ 2) = (sameBlockOffDiag S n D).card + S.card := by
    have hoff := sameBlockOffDiag_card S n D hD hS
    calc
      (∑ i ∈ I, (B i).card ^ 2)
          = ∑ i ∈ I, (((B i).card ^ 2 - (B i).card) + (B i).card) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [pow_two] using
                (Nat.sub_add_cancel (Nat.le_mul_self ((B i).card))).symm
      _ = (∑ i ∈ I, ((B i).card ^ 2 - (B i).card)) + (∑ i ∈ I, (B i).card) := by
              rw [Finset.sum_add_distrib]
      _ = (sameBlockOffDiag S n D).card + S.card := by rw [hoff, hsum]
  -- (3) same-block off-diagonal pairs ⊆ upPairs ∪ downPairs
  have hsubset : sameBlockOffDiag S n D ⊆ upPairs S D ∪ downPairs S D :=
    sameBlockOffDiag_subset S n D hD hS
  have hup : (upPairs S D).card = ∑ d ∈ Finset.Icc 1 (D - 1), (S.filter fun r => r + d ∈ S).card :=
    upPairs_card_eq S D
  have hdown : (downPairs S D).card = ∑ d ∈ Finset.Icc 1 (D - 1), (S.filter fun r => r + d ∈ S).card := by
    rw [downPairs_card_eq S D, upPairs_card_eq S D]
  -- (4) Q ≤ Σ (d - 1)
  have hQ_le : (∑ d ∈ Finset.Icc 1 (D - 1), (S.filter fun r => r + d ∈ S).card) ≤
      ∑ d ∈ Finset.Icc 1 (D - 1), (d - 1) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    exact hsp d (Finset.mem_Icc.mp hd).1
  -- (5) Σ_{d=1}^{D-1} (d-1) = (D-1)(D-2)/2
  have hsumrange : (∑ d ∈ Finset.Icc 1 (D - 1), (d - 1)) = (D - 1) * (D - 2) / 2 := by
    calc
      (∑ d ∈ Finset.Icc 1 (D - 1), (d - 1)) = ∑ e ∈ Finset.range (D - 1), e := by
        refine Finset.sum_bij (fun d hd => d - 1) ?_ ?_ ?_ ?_
        · intro d hd
          rw [Finset.mem_range]
          have hd' : 1 ≤ d ∧ d ≤ D - 1 := Finset.mem_Icc.mp hd
          omega
        · intro d₁ hd₁ d₂ hd₂ h
          have hd₁' : 1 ≤ d₁ ∧ d₁ ≤ D - 1 := Finset.mem_Icc.mp hd₁
          have hd₂' : 1 ≤ d₂ ∧ d₂ ≤ D - 1 := Finset.mem_Icc.mp hd₂
          omega
        · intro e he
          have he' : e < D - 1 := Finset.mem_range.mp he
          refine ⟨e + 1, ?_, ?_⟩
          · rw [Finset.mem_Icc]; omega
          · omega
        · intro d hd
          rfl
      _ = (D - 1) * (D - 2) / 2 := by
          simpa [show (D - 1) - 1 = D - 2 by omega] using Finset.sum_range_id (D - 1)
  -- (6) ℕ chain: |sameBlockOffDiag| ≤ (D-1)(D-2)
  have hchain : (sameBlockOffDiag S n D).card ≤ (D - 1) * (D - 2) := by
    calc
      (sameBlockOffDiag S n D).card ≤ (upPairs S D ∪ downPairs S D).card :=
        Finset.card_le_card hsubset
      _ = (upPairs S D).card + (downPairs S D).card := by
          apply Finset.card_union_of_disjoint
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          rw [upPairs, Finset.mem_filter] at hp1
          rw [downPairs, Finset.mem_filter] at hp2
          have hlt : p.1 < p.2 := hp1.2.1
          have hgt : p.2 < p.1 := hp2.2.1
          omega
      _ = 2 * (∑ d ∈ Finset.Icc 1 (D - 1), (S.filter fun r => r + d ∈ S).card) := by
          rw [hup, hdown]
          omega
      _ ≤ 2 * (∑ d ∈ Finset.Icc 1 (D - 1), (d - 1)) := Nat.mul_le_mul_left 2 hQ_le
      _ = 2 * ((D - 1) * (D - 2) / 2) := by rw [hsumrange]
      _ ≤ (D - 1) * (D - 2) := by
          rw [Nat.mul_comm]
          exact Nat.div_mul_le_self ((D - 1) * (D - 2)) 2
  -- (7) upper bound on Σ n_i² in ℕ
  have hnat : (∑ i ∈ I, (B i).card ^ 2) ≤ S.card + (D - 1) * (D - 2) := by
    rw [hsq]
    omega
  -- cast to ℝ: sumSq ≤ N + ((D-1)(D-2) : ℕ : ℝ)
  have hupper : sumSq ≤ N + (((D - 1) * (D - 2) : ℕ) : ℝ) := by
    have hnatR : ((∑ i ∈ I, (B i).card ^ 2 : ℕ) : ℝ) ≤ ((S.card + (D - 1) * (D - 2) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have h1 : ((∑ i ∈ I, (B i).card ^ 2 : ℕ) : ℝ) = sumSq := by
      simp [sumSq, Nat.cast_sum, Nat.cast_pow]
    have h2 : ((S.card + (D - 1) * (D - 2) : ℕ) : ℝ) = N + (((D - 1) * (D - 2) : ℕ) : ℝ) := by
      simp [N, Nat.cast_add, Nat.cast_mul]
    rwa [h1, h2] at hnatR
  -- (8) Cauchy–Schwarz: N² ≤ M · sumSq
  have hcauchy : N ^ 2 ≤ M * sumSq := by
    have hsumR : (∑ i ∈ I, ((B i).card : ℝ)) = N := by
      have h : (∑ i ∈ I, ((B i).card : ℝ)) = (S.card : ℝ) := by
        exact_mod_cast hsum
      simpa [N] using h
    have h := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i : ℕ => ((B i).card : ℝ))
    rw [hsumR] at h
    have hcardI : (I.card : ℝ) = M := by
      simp [I, M]
    rw [hcardI] at h
    simpa [sumSq] using h
  -- (9) ((D-1)(D-2) : ℕ : ℝ) ≤ D²
  have hsub : (((D - 1) * (D - 2) : ℕ) : ℝ) ≤ (D : ℝ) ^ 2 := by
    have h1 : ((D - 1 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : (D - 1) ≤ D)
    have h2 : ((D - 2 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : (D - 2) ≤ D)
    have h1n : 0 ≤ ((D - 1 : ℕ) : ℝ) := by positivity
    have h2n : 0 ≤ ((D - 2 : ℕ) : ℝ) := by positivity
    have hbn : 0 ≤ (D : ℝ) := by positivity
    have hprod : ((D - 1 : ℕ) : ℝ) * ((D - 2 : ℕ) : ℝ) ≤ (D : ℝ) * (D : ℝ) :=
      mul_le_mul h1 h2 h2n hbn
    simpa [Nat.cast_mul, pow_two] using hprod
  -- combine
  have hfinal : N ^ 2 ≤ M * (N + (D : ℝ) ^ 2) := by
    have hsqsum : sumSq ≤ N + (D : ℝ) ^ 2 := by nlinarith [hupper, hsub]
    have hmul : M * sumSq ≤ M * (N + (D : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsqsum (by positivity)
    nlinarith [hcauchy, hmul]
  simpa [N, M] using hfinal

/-- **The general spacing-to-growth theorem.** If `S ⊆ [1, n]` satisfies the spacing condition
`#{r ∈ S | r + d ∈ S} ≤ d - 1` for every `d ≥ 1`, then `|S|³ ≤ 64 n²`. -/
theorem card_cube_le_of_spacing (S : Finset ℕ) (n : ℕ)
    (hS : S ⊆ Finset.Icc 1 n)
    (hsp : ∀ d, 1 ≤ d → (S.filter fun r => r + d ∈ S).card ≤ d - 1) :
    ((S.card : ℝ) ^ 3) ≤ 64 * ((n : ℝ) ^ 2) := by
  classical
  let N0 : ℕ := S.card
  let N : ℝ := S.card
  let D0 : ℕ := Nat.sqrt N0 + 1
  let D : ℝ := D0
  let M0 : ℕ := n / D0 + 1
  let M : ℝ := M0
  by_cases hN0 : N0 = 0
  · have hN0R : (S.card : ℝ) = 0 := by exact_mod_cast hN0
    rw [hN0R]
    nlinarith [sq_nonneg (n : ℝ)]
  · have hN0pos : 1 ≤ N0 := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hN0)
    have hNpos : 0 < N := by
      have h : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
      simpa [N] using h
    have hD_ge1 : 1 ≤ D0 := by omega
    have hposD0 : 0 < D0 := hD_ge1
    have hDpos : 0 < D := by
      have h : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast hposD0
      simpa [D] using h
    have hDne : (D : ℝ) ≠ 0 := ne_of_gt hDpos
    -- F1: N ≤ D²
    have hF1 : N ≤ D ^ 2 := by
      have hF1_nat : N0 ≤ D0 ^ 2 := by
        simpa [D0, Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt' N0).le
      have h : (N0 : ℝ) ≤ (D0 ^ 2 : ℕ) := by exact_mod_cast hF1_nat
      simpa [N, D, D0, Nat.cast_pow] using h
    -- F2: D² ≤ 4N
    have hF2 : D ^ 2 ≤ 4 * N := by
      have hF2_nat : D0 ^ 2 ≤ 4 * N0 := by
        have hs : (Nat.sqrt N0) ^ 2 ≤ N0 := Nat.sqrt_le' N0
        have hD0_le : D0 ≤ 2 * Nat.sqrt N0 := by
          have h1sqrt : 1 ≤ Nat.sqrt N0 := Nat.le_sqrt.mpr (by simpa using hN0pos)
          dsimp [D0]
          omega
        have hmul : D0 * D0 ≤ (2 * Nat.sqrt N0) * (2 * Nat.sqrt N0) :=
          Nat.mul_self_le_mul_self hD0_le
        nlinarith [hmul, hs]
      have h : (D0 ^ 2 : ℕ) ≤ (4 * N0 : ℕ) := hF2_nat
      have h' : ((D0 ^ 2 : ℕ) : ℝ) ≤ ((4 * N0 : ℕ) : ℝ) := by exact_mod_cast h
      simpa [D, N, Nat.cast_pow, Nat.cast_mul] using h'
    -- block inequality
    have hblock : N ^ 2 ≤ M * (N + D ^ 2) := by
      simpa [N, M, D, D0, M0] using card_sq_le_of_spacing S n D0 hD_ge1 hS hsp
    by_cases hnD : D0 ≤ n
    · -- subcase D0 ≤ n
      have hM_le : M ≤ 2 * ((n / D0 : ℕ) : ℝ) := by
        have h1le : 1 ≤ n / D0 := (Nat.le_div_iff_mul_le hposD0).mpr (by simpa using hnD)
        have hM0 : M0 ≤ 2 * (n / D0) := by omega
        have hcast : (M0 : ℝ) ≤ 2 * ((n / D0 : ℕ) : ℝ) := by exact_mod_cast hM0
        simpa [M] using hcast
      have hdivmul : ((n / D0 : ℕ) : ℝ) * D ≤ (n : ℝ) := by
        have hnatR : (((n / D0) * D0 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (Nat.div_mul_le_self n D0)
        simpa [D, Nat.cast_mul] using hnatR
      have hN2_le : N ^ 2 ≤ 4 * (n : ℝ) * D := by
        have h1 : M * (N + D ^ 2) ≤ (2 * ((n / D0 : ℕ) : ℝ)) * (N + D ^ 2) :=
          mul_le_mul_of_nonneg_right hM_le (by positivity)
        have h2 : (2 * ((n / D0 : ℕ) : ℝ)) * (N + D ^ 2) ≤ 4 * (n : ℝ) * D := by
          have hA : 2 * ((n / D0 : ℕ) : ℝ) * (N + D ^ 2) ≤ 4 * ((n / D0 : ℕ) : ℝ) * D ^ 2 := by
            nlinarith [hF1, (by positivity : 0 ≤ ((n / D0 : ℕ) : ℝ))]
          have hB : 4 * ((n / D0 : ℕ) : ℝ) * D ^ 2 ≤ 4 * (n : ℝ) * D := by
            have hqD : ((n / D0 : ℕ) : ℝ) * D ≤ (n : ℝ) := hdivmul
            have hqD_D : ((n / D0 : ℕ) : ℝ) * D * D ≤ (n : ℝ) * D :=
              mul_le_mul_of_nonneg_right hqD (by positivity)
            nlinarith [hqD_D]
          nlinarith [hA, hB]
        nlinarith [hblock, h1, h2]
      have hN4 : N ^ 4 ≤ 64 * (n : ℝ) ^ 2 * N := by
        have hsq : (N ^ 2) ^ 2 ≤ (4 * (n : ℝ) * D) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg N) hN2_le 2
        have hD2 : D ^ 2 ≤ 4 * N := hF2
        nlinarith [hsq, hD2, sq_nonneg (n : ℝ), sq_nonneg D]
      have hN3 : N ^ 3 ≤ 64 * (n : ℝ) ^ 2 := by
        have hN4' : N * N ^ 3 ≤ N * (64 * (n : ℝ) ^ 2) := by
          convert hN4 using 1 <;> ring
        exact (mul_le_mul_iff_of_pos_left hNpos).mp hN4'
      simpa [N] using hN3
    · -- subcase n < D0
      have hn_lt : n < D0 := Nat.lt_of_not_ge hnD
      have hM_eq : M = 1 := by
        have hdiv : n / D0 = 0 := Nat.div_eq_of_lt hn_lt
        dsimp [M, M0]
        rw [hdiv]
        norm_num
      have hN_le_n : N ≤ (n : ℝ) := by
        have hcard : N0 ≤ n := by
          calc
            N0 = S.card := rfl
            _ ≤ (Finset.Icc 1 n).card := Finset.card_le_card hS
            _ = n := by rw [Nat.card_Icc]; omega
        have h : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
        simpa [N] using h
      have hN2_le_5N : N ^ 2 ≤ 5 * N := by
        have h : N + D ^ 2 ≤ 5 * N := by nlinarith [hF2]
        nlinarith [hblock, hM_eq, h]
      have hN_le_5 : N ≤ 5 := by
        have h : N * N ≤ N * 5 := by nlinarith [hN2_le_5N]
        exact (mul_le_mul_iff_of_pos_left hNpos).mp h
      have hN3 : N ^ 3 ≤ 64 * (n : ℝ) ^ 2 := by
        have hN2_le_n2 : N ^ 2 ≤ (n : ℝ) ^ 2 := by
          simpa [pow_two] using mul_self_le_mul_self (by positivity : 0 ≤ N) hN_le_n
        have h1 : N * N ^ 2 ≤ N * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hN2_le_n2 (by positivity)
        have h2 : N * (n : ℝ) ^ 2 ≤ 5 * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hN_le_5 (sq_nonneg (n : ℝ))
        have h3 : 5 * (n : ℝ) ^ 2 ≤ 64 * (n : ℝ) ^ 2 := by nlinarith [sq_nonneg (n : ℝ)]
        nlinarith [h1, h2, h3]
      simpa [N] using hN3

/-! ## Application to the bad set `E p` -/

/-- The spacing bound `#{r ∈ E p | r + d ∈ E p} ≤ d - 1` for *all* `d ≥ 1` (the version in
`GapPolynomial.lean` only assumes `d < p`; for `d ≥ p` the filter is empty). -/
theorem E_add_count_le_pred_all (p d : ℕ) [Fact p.Prime] (hd : 1 ≤ d) :
    ((E p).filter fun r => r + d ∈ E p).card ≤ d - 1 := by
  by_cases hdlt : d < p
  · exact E_add_count_le_pred p d hd hdlt
  · have hempty : ((E p).filter fun r => r + d ∈ E p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hr' : r + d ∈ E p := (Finset.mem_filter.mp hr).2
      have hIcc : r + d ∈ Finset.Icc 1 (p - 1) := by
        unfold E at hr'
        exact (Finset.mem_filter.mp hr').1
      have hle : r + d ≤ p - 1 := (Finset.mem_Icc.mp hIcc).2
      omega
    rw [hempty]
    simp

/-- **Unconditional growth of the bad set.** For any prime `p`, `|E p|³ ≤ 64 p²`, i.e.
`|E p| ≪ p^(2/3)`. -/
theorem E_card_cube_le (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((E p).card : ℝ) ^ 3 ≤ 64 * ((p : ℝ) ^ 2) := by
  have hspacing : ∀ d, 1 ≤ d → ((E p).filter fun r => r + d ∈ E p).card ≤ d - 1 := by
    intro d hd
    exact E_add_count_le_pred_all p d hd
  have hS : E p ⊆ Finset.Icc 1 (p - 1) := by
    rw [E]
    exact Finset.filter_subset _ _
  have hcard := card_cube_le_of_spacing (E p) (p - 1) hS hspacing
  have hle : ((p - 1 : ℕ) : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
    have h : ((p - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : (p - 1) ≤ p)
    have hn : 0 ≤ ((p - 1 : ℕ) : ℝ) := by positivity
    simpa [pow_two] using mul_self_le_mul_self hn h
  have h64 : 64 * (((p - 1 : ℕ) : ℝ) ^ 2) ≤ 64 * ((p : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hle (by norm_num)
  nlinarith [hcard, h64]

end Erdos291
