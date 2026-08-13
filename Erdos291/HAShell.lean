import Erdos291.GcdOne

/-!
# Erdős #291 — the dyadic "shell" hypothesis

This file removes the analytic hypotheses (`HA_dist`, `HA_arith`, Mertens, `x · P(x) → ∞`)
from the `gcd = 1` direction entirely, replacing them by a single *shell* hypothesis.

The key observation is that the count `G x` is *monotone*, so the number of good `n` in a
dyadic shell `(X, 2X]` is the honest (non-truncated) difference

    `deltaG X = G (2X) - G X`.

If for infinitely many `X` this shell count is at least `κ · X · ∏_{p ≤ 2X} (1 - c p)`, then
— because `c p < 1` for every prime (so the product is strictly positive) and because
`deltaG X` is a nonnegative *integer* — each such shell contains at least one good `n`.
As these shells are dyadic (so `X → ∞` along an infinite set), this yields infinitely many
good `n`, i.e. `gcd (a n) (L n) = 1` infinitely often.

There are no unproved declarations in this file.
-/

open scoped BigOperators

namespace Erdos291

/-- The number of good `n` in the dyadic shell `(X, 2X]`. Truncated `Nat` subtraction is
honest because `G` is monotone (see `G_mono`). -/
def deltaG (X : ℕ) : ℕ := G (2 * X) - G X

/-- `HA_shell`: for infinitely many `X`, the shell `(X, 2X]` contains at least
`κ · X · ∏_{p ≤ 2X} (1 - c p)` good integers. -/
def HA_shell : Prop :=
  ∃ κ : ℝ, 0 < κ ∧
    Set.Infinite { X : ℕ |
      (κ * (X : ℝ) *
        (∏ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime, (1 - (c p : ℝ))))
          ≤ (deltaG X : ℝ) }

/-! ## Unboundedness of infinite subsets of `ℕ` -/

/-- An infinite subset of `ℕ` is unbounded: it contains an element exceeding any fixed
bound. (Mathlib also has `Set.Infinite.exists_gt`; this specialisation only needs the
`exists_notMem_finset` primitive.) -/
lemma exists_nat_gt_of_infinite {s : Set ℕ} (hs : s.Infinite) (N : ℕ) :
    ∃ n ∈ s, N < n := by
  rcases hs.exists_notMem_finset (Finset.range (N + 1)) with ⟨n, hn, hnnot⟩
  refine ⟨n, hn, ?_⟩
  have hnot_lt : ¬ n < N + 1 := fun h => hnnot (Finset.mem_range.mpr h)
  omega

/-- If a set of naturals contains an element exceeding every bound, it is infinite. -/
lemma infinite_of_forall_exists_nat_gt {s : Set ℕ} (h : ∀ N, ∃ n ∈ s, N < n) : s.Infinite := by
  intro hfin
  let M : ℕ := hfin.toFinset.sup id
  rcases h (M + 1) with ⟨n, hns, hMn⟩
  have hnt : n ∈ hfin.toFinset := by
    rw [← Finset.mem_coe, hfin.coe_toFinset]
    exact hns
  have hnle : n ≤ M := Finset.le_sup (s := hfin.toFinset) (f := id) hnt
  omega

/-! ## `G` is monotone, and the shell count is an honest difference -/

/-- `G` is monotone: `G x ≤ G y` for `x ≤ y`. -/
lemma G_mono : Monotone G := by
  intro x y hxy
  unfold G
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  rcases hn with ⟨hnIcc, hgood⟩
  constructor
  · rw [Finset.mem_Icc]
    have hn' : 1 ≤ n ∧ n ≤ x := Finset.mem_Icc.mp hnIcc
    exact ⟨hn'.1, le_trans hn'.2 hxy⟩
  · exact hgood

/-- `Icc 1 (2X)` splits as the disjoint union `Icc 1 X ⊔ Icc (X + 1) (2X)`. -/
lemma Icc_one_two_mul_eq_union (X : ℕ) :
    Finset.Icc 1 (2 * X) = Finset.Icc 1 X ∪ Finset.Icc (X + 1) (2 * X) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_union]
  omega

/-- The two parts of the dyadic partition are disjoint. -/
lemma Icc_one_disjoint_Icc_succ (X : ℕ) :
    Disjoint (Finset.Icc 1 X) (Finset.Icc (X + 1) (2 * X)) := by
  rw [Finset.disjoint_left]
  intro n hn1
  rw [Finset.mem_Icc] at hn1
  intro hn2
  rw [Finset.mem_Icc] at hn2
  omega

/-- `G (2X) = G X + #{n ∈ (X, 2X] : gcd (a n) (L n) = 1}`. -/
lemma G_two_mul_eq (X : ℕ) :
    G (2 * X) = G X +
        ((Finset.Icc (X + 1) (2 * X)).filter (fun n => Nat.gcd (a n) (L n) = 1)).card := by
  unfold G
  have hdisj : Disjoint
      ((Finset.Icc 1 X).filter (fun n => Nat.gcd (a n) (L n) = 1))
      ((Finset.Icc (X + 1) (2 * X)).filter (fun n => Nat.gcd (a n) (L n) = 1)) :=
    Finset.disjoint_filter_filter (Icc_one_disjoint_Icc_succ X)
  have hunion : (Finset.Icc 1 (2 * X)).filter (fun n => Nat.gcd (a n) (L n) = 1) =
      (Finset.Icc 1 X).filter (fun n => Nat.gcd (a n) (L n) = 1) ∪
        (Finset.Icc (X + 1) (2 * X)).filter (fun n => Nat.gcd (a n) (L n) = 1) := by
    rw [← Finset.filter_union, Icc_one_two_mul_eq_union X]
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- The shell count `deltaG X` equals the number of good `n` in the shell `(X, 2X]`. -/
lemma shell_count_identity (X : ℕ) :
    deltaG X = ((Finset.Icc (X + 1) (2 * X)).filter (fun n => Nat.gcd (a n) (L n) = 1)).card := by
  unfold deltaG
  rw [G_two_mul_eq X]
  rw [Nat.add_sub_cancel_left]

/-! ## A positive shell count forces a good `n` -/

/-- If the shell `(X, 2X]` contains at least one good integer, then it contains some `n`
with `X < n ≤ 2X` and `gcd (a n) (L n) = 1`. -/
lemma exists_good_of_deltaG_pos (X : ℕ) (h : 1 ≤ deltaG X) :
    ∃ n, X < n ∧ n ≤ 2 * X ∧ Nat.gcd (a n) (L n) = 1 := by
  have hpos : 0 < deltaG X := by omega
  rw [shell_count_identity X] at hpos
  rcases Finset.card_pos.mp hpos with ⟨n, hn⟩
  have hnIcc : n ∈ Finset.Icc (X + 1) (2 * X) := (Finset.mem_filter.mp hn).1
  have hgood : Nat.gcd (a n) (L n) = 1 := (Finset.mem_filter.mp hn).2
  have hlo : X + 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
  have hhi : n ≤ 2 * X := (Finset.mem_Icc.mp hnIcc).2
  refine ⟨n, by omega, hhi, hgood⟩

/-! ## Positivity of the product `∏_{p ≤ 2X} (1 - c p)` -/

/-- For every prime `p`, `1 - c p > 0` (since `c p < 1`), so the product over primes
`p ≤ 2X` is strictly positive. -/
lemma prod_one_sub_c_pos (X : ℕ) :
    0 < ∏ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime, (1 - (c p : ℝ)) := by
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : 2 ≤ p := by
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hc : (c p : ℝ) < 1 := c_lt_one p hp2
  linarith

/-- For `κ > 0` and `X > 0`, the lower bound `κ · X · ∏_{p ≤ 2X} (1 - c p)` is positive. -/
lemma kappa_mul_prod_pos (κ : ℝ) (hκ : 0 < κ) (X : ℕ) (hX : 0 < X) :
    0 < κ * (X : ℝ) *
        (∏ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime, (1 - (c p : ℝ))) := by
  have hXr : (0 : ℝ) < (X : ℝ) := Nat.cast_pos.mpr hX
  have hP : 0 < ∏ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime, (1 - (c p : ℝ)) :=
    prod_one_sub_c_pos X
  exact mul_pos (mul_pos hκ hXr) hP

/-- If a shell lower bound is a positive real, then `deltaG X ≥ 1` (it is a nonnegative
integer bounded below by a positive real). -/
lemma deltaG_pos_of_lower_bound (X : ℕ) {r : ℝ} (hr : 0 < r) (hle : r ≤ (deltaG X : ℝ)) :
    1 ≤ deltaG X := by
  have hdgt : 0 < (deltaG X : ℝ) := lt_of_lt_of_le hr hle
  have hdpos : 0 < deltaG X := Nat.cast_pos.mp hdgt
  omega

/-! ## The main theorem -/

/-- `HA_shell` alone (no `HA_arith`, no `HA_dist`, no Mertens, no `x·P(x) → ∞`)
forces infinitely many `n` with `gcd (a n) (L n) = 1`. -/
theorem HA_shell_implies_infinite (hshell : HA_shell) :
    Set.Infinite { n : ℕ | Nat.gcd (a n) (L n) = 1 } := by
  rcases hshell with ⟨κ, hκpos, hSinf⟩
  let P : ℕ → ℝ := fun X =>
    ∏ p ∈ (Finset.Icc 2 (2 * X)).filter Nat.Prime, (1 - (c p : ℝ))
  have hSinf' : Set.Infinite { X : ℕ | κ * (X : ℝ) * P X ≤ (deltaG X : ℝ) } := by
    exact hSinf
  -- Discard the `X = 0` case (there `κ · X · P(2X) = 0`, so positivity fails).
  have hSdiff : Set.Infinite
      ({ X : ℕ | κ * (X : ℝ) * P X ≤ (deltaG X : ℝ) } \ ({0} : Set ℕ)) :=
    hSinf'.sdiff (Set.finite_singleton 0)
  apply infinite_of_forall_exists_nat_gt
  intro N
  rcases exists_nat_gt_of_infinite hSdiff N with ⟨X, hX, hNX⟩
  rcases hX with ⟨hXS, hXnot0⟩
  have hXne : X ≠ 0 := by
    intro hz
    exact hXnot0 hz
  have hXpos : 0 < X := Nat.pos_of_ne_zero hXne
  have hineq : κ * (X : ℝ) * P X ≤ (deltaG X : ℝ) := hXS
  have hprodpos : 0 < κ * (X : ℝ) * P X := by
    dsimp [P]
    exact kappa_mul_prod_pos κ hκpos X hXpos
  have hdelta : 1 ≤ deltaG X := deltaG_pos_of_lower_bound X hprodpos hineq
  rcases exists_good_of_deltaG_pos X hdelta with ⟨n, hXn, _, hgood⟩
  exact ⟨n, hgood, by omega⟩

end Erdos291
