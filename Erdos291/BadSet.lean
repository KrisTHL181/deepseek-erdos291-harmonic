import Erdos291.Basic
import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Erdős #291 — the "bad set" and the count `G`

For each prime `p`, the set `E p` collects the *bad* base-`p` digits `r ∈ [1, p - 1]`,
i.e. those for which `p` divides the numerator of the harmonic number `H_r` in lowest
terms. Writing the harmonic number `H_r = a_r / L_r` as a reduced fraction, this is
exactly the condition that the leading base-`p` digit `r` makes the harmonic sum
`∑_{j=1}^r j⁻¹` vanish mod `p` (the characterization proved in `Characterization.lean`),
but here we deliberately avoid any prime assumption and any `ZMod` inverses: the
condition is expressed purely in terms of `Rat.num (harmonic r)`.

The count `G x` records how many `n ≤ x` have `gcd (a n) (L n) = 1`, and `c p` is the
density `|E p| / (p - 1)` of bad digits modulo `p`.
-/

open scoped BigOperators

namespace Erdos291

/-- The "bad" digits modulo `p`: `r ∈ [1, p - 1]` such that `p` divides the numerator
of the harmonic number `H_r` (in lowest terms). Defined for every `p` with no prime
assumption. -/
def E (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).filter fun r => (p : ℤ) ∣ (harmonic r).num

/-- `G x` is the number of `n` with `1 ≤ n ≤ x` such that `gcd (a n) (L n) = 1`. -/
def G (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter fun n => Nat.gcd (a n) (L n) = 1).card

/-- The density `|E p| / (p - 1)` of bad digits modulo `p`. -/
def c (p : ℕ) : ℚ := ((E p).card : ℚ) / ((p - 1) : ℚ)

end Erdos291
