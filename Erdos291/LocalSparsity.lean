import Erdos291.BadDensity

set_option linter.style.haveILetI false

/-!
# Erdős #291 — Lemma 7: local sparsity of the bad set

This module supplies the thin public wrapper statements used by the lemma document.
All the substantive work lives in `Erdos291.BadDensity`: the finite exceptional
product `Nall D`, the predicate `NoTripleWithin`, and the block-partition bound
`card_le_two_mul_div_add_two_of_no_triple`.  Here we only repackage those facts
under the exact theorem names requested by the proof plan.
-/

namespace Erdos291

/-- **Lemma 7A.** There is a nonzero integer `N` such that for every prime `p` not
dividing `N`, the bad set `E p` contains no three elements `r₁ < r₂ < r₃` with span
`r₃ - r₁ ≤ D`. -/
theorem exists_no_small_span_triple (D : ℕ) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∀ p : ℕ, Nat.Prime p → ¬ p ∣ N →
        ∀ r₁ r₂ r₃ : ℕ,
          r₁ ∈ E p → r₂ ∈ E p → r₃ ∈ E p →
          r₁ < r₂ → r₂ < r₃ → r₃ - r₁ ≤ D → False := by
  refine ⟨Nall D, Nall_ne_zero D, ?_⟩
  intro p hp hnot r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23 hspan
  letI : Fact p.Prime := ⟨hp⟩
  exact no_triple_of_not_dvd_Nall p D hnot hr₁ hr₂ hr₃ h12 h23 hspan

/-- **Lemma 7B.** If `E p` has no three elements of span `≤ D`, then its cardinality is
at most `2 * ((p - 1) / D + 1)`.  The hypotheses `N` and `hN` are carried for the
combined form below. -/
theorem E_card_le_two_mul_div_add_one
    (D p N : ℕ) (hD : 1 ≤ D) (hp : Nat.Prime p) (hN : N ≠ 0)
    (hgood : ∀ r₁ r₂ r₃ : ℕ,
      r₁ ∈ E p → r₂ ∈ E p → r₃ ∈ E p →
      r₁ < r₂ → r₂ < r₃ → r₃ - r₁ ≤ D → False) :
    (E p).card ≤ 2 * ((p - 1) / D + 1) := by
  have := hp
  have := hN
  have hDpos : 0 < D := by omega
  have hS : E p ⊆ Finset.Icc 1 (p - 1) := by
    rw [E]
    exact Finset.filter_subset _ _
  have hNo : NoTripleWithin (E p) D := by
    intro r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23 hspan
    exact hgood r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23 hspan
  exact card_le_two_mul_div_add_two_of_no_triple (E p) D (p - 1) hDpos hS hNo

/-- **Lemma 7 combined.** For every `D ≥ 1` there is a nonzero integer `N` such that
every prime `p` not dividing `N` satisfies `|E p| ≤ 2 * ((p - 1) / D + 1)`. -/
theorem exists_N_card_le_two_mul_div_add_one (D : ℕ) (hD : 1 ≤ D) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∀ p : ℕ, Nat.Prime p → ¬ p ∣ N →
        (E p).card ≤ 2 * ((p - 1) / D + 1) := by
  refine ⟨Nall D, Nall_ne_zero D, ?_⟩
  intro p hp hnot
  letI : Fact p.Prime := ⟨hp⟩
  exact E_card_le_two_mul_div_add_one D p (Nall D) hD hp (Nall_ne_zero D)
    (by simpa [NoTripleWithin] using no_triple_of_not_dvd_Nall p D hnot)

end Erdos291
