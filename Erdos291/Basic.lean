import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Erdős problem #291 — basic definitions

We formalize the two objects at the heart of Erdős #291:

* `L n = Nat.lcmUpto n` is the lcm `lcm(1, 2, …, n)` (already in Mathlib).
* `a n` is the integer defined by `∑_{k=1}^n L n / k`, so that the harmonic number
  satisfies `H_n = a_n / L_n`.

These match the statements in the `formal-conjectures` repository
(`FormalConjectures/ErdosProblems/291.lean`).
-/

open scoped BigOperators

namespace Erdos291

/-- `L n` is the least common multiple of `1, 2, …, n`. -/
abbrev L (n : ℕ) : ℕ := Nat.lcmUpto n

/-- `a n` is the integer numerator of the harmonic number `H_n` when written over the
common denominator `L n`, i.e. `a n = ∑_{k=1}^n L n / k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, L n / k

@[simp] lemma L_ne_zero (n : ℕ) : L n ≠ 0 := Nat.lcmUpto_ne_zero n

@[simp] lemma L_pos (n : ℕ) : 0 < L n := Nat.lcmUpto_pos n

/-- Every `k` with `1 ≤ k ≤ n` divides `L n`. -/
lemma dvd_L_of_mem_Icc (n k : ℕ) (hk : k ∈ Finset.Icc 1 n) : k ∣ L n :=
  Finset.dvd_lcm hk

end Erdos291
