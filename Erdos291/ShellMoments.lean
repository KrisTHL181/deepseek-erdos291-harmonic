import Erdos291.BadSet
import Erdos291.Bonferroni
import Erdos291.HAShell
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

/-!
# Erdős #291 — shell factorial moments and the Fubini double-count

For a dyadic shell `Ω_X = (X, 2X]`, this file introduces the "bad prime" predicate
`badPrime p n` (meaning `p ∣ gcd (a n) (L n)`), the set `badPrimes X` of primes `p ≤ 2X`,
and the random-variable `Y X n = #{p ∈ badPrimes X : badPrime p n}` counting the bad primes
of `n`.  It then defines the normalized factorial moments `mu X j`, the local shell density
`beta p X`, and the expected count `lambda X = ∑_p beta p X`.

The two load-bearing results are:

* `mu_one_eq_lambda`: the first moment `mu X 1` equals the sum of local densities
  `lambda X`, by a pure `Finset` double count (no independence assumption).
* `mu_eq_factorialMoment_div`: `mu X j` is exactly `(1 / X)` times Bonferroni's
  `factorialMoment`, via the finite witness `badWitness X`.  This is the bridge that lets a later
  module feed the shell moments into `bonferroni_lower`.

All moments are normalized by `1 / (X : ℝ)`; for `X = 0` this is `0`, which is harmless,
so every theorem is stated for all `X` with no positivity hypothesis.
-/

open scoped BigOperators

namespace Erdos291

/-- `p` is a "bad prime" for `n` if `p ∣ gcd (a n) (L n)`.  Marked `reducible` so that the
decidable-instance for divisibility on `ℕ` is visible through the definition. -/
@[reducible] def badPrime (p n : ℕ) : Prop := p ∣ Nat.gcd (a n) (L n)

/-- The dyadic shell `(X, 2X]` as a finset. -/
def shellOmega (X : ℕ) : Finset ℕ := Finset.Icc (X + 1) (2 * X)

/-- The primes `p` with `p ≤ 2X`. -/
def badPrimes (X : ℕ) : Finset ℕ := (Finset.Icc 2 (2 * X)).filter Nat.Prime

/-- The number of bad primes for `n`, i.e. `#{p ∈ badPrimes X : badPrime p n}`. -/
def Y (X : ℕ) (n : ℕ) : ℕ := ((badPrimes X).filter (fun p => badPrime p n)).card

/-- The normalized `j`-th factorial moment `(1 / X) · ∑_{n ∈ Ω_X} C(Y X n, j)`. -/
noncomputable def mu (X j : ℕ) : ℝ :=
  (1 / (X : ℝ)) * ∑ n ∈ shellOmega X, (Nat.choose (Y X n) j : ℝ)

/-- The local shell density of the prime `p`: the fraction of `n ∈ Ω_X` with `badPrime p n`. -/
noncomputable def beta (p X : ℕ) : ℝ :=
  (1 / (X : ℝ)) * (((shellOmega X).filter (fun n => badPrime p n)).card : ℝ)

/-- The expected number of bad primes: `∑_{p ∈ badPrimes X} beta p X`. -/
noncomputable def lambda (X : ℕ) : ℝ := ∑ p ∈ badPrimes X, beta p X

/-- A finite witness for Bonferroni's `factorialMoment`: `badWitness X p` records those
`n ≤ 2X` (with `n ∈ range (2X + 1)`) for which `p` is bad. -/
def badWitness (X : ℕ) (p : ℕ) : Finset ℕ :=
  (Finset.range (2 * X + 1)).filter (fun n => badPrime p n)

/-! ## The bridge from `badCount` to `Y` -/

/-- For `n ≤ 2X`, membership in `badWitness X p` is exactly `badPrime p n`. -/
lemma mem_badWitness_iff (X p n : ℕ) (hn : n ≤ 2 * X) : n ∈ badWitness X p ↔ badPrime p n := by
  rw [badWitness, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨Finset.mem_range.mpr ?_, h⟩
    omega

/-- `badCount (badPrimes X) (badWitness X) n = Y X n` whenever `n ≤ 2X`. -/
lemma badCount_eq_Y (X n : ℕ) (hn : n ≤ 2 * X) :
    badCount (badPrimes X) (badWitness X) n = Y X n := by
  unfold badCount Y
  apply congr_arg Finset.card
  ext p
  simp [mem_badWitness_iff X p n hn]

/-! ## The Fubini double-count -/

/-- Double-counting: summing over `s` the count of `t`-elements satisfying `r` equals
summing over `t` the count of `s`-elements satisfying `r`. -/
lemma sum_card_filter_comm (s t : Finset ℕ) (r : ℕ → ℕ → Prop) [DecidableRel r] :
    (∑ n ∈ s, (t.filter (fun p => r n p)).card) =
      ∑ p ∈ t, (s.filter (fun n => r n p)).card := by
  calc
    (∑ n ∈ s, (t.filter (fun p => r n p)).card)
        = ∑ n ∈ s, ∑ p ∈ t, if r n p then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro n _
            exact (Finset.sum_boole (p := fun p => r n p) (s := t)).symm
    _ = ∑ p ∈ t, ∑ n ∈ s, if r n p then 1 else 0 := Finset.sum_comm
    _ = ∑ p ∈ t, (s.filter (fun n => r n p)).card := by
            apply Finset.sum_congr rfl
            intro p _
            exact Finset.sum_boole (p := fun n => r n p) (s := s)

/-- Fubini: `∑_n Y X n = ∑_p #{n ∈ Ω_X : badPrime p n}`. -/
lemma sum_Y_eq_sum_badPrime_count (X : ℕ) :
    (∑ n ∈ shellOmega X, Y X n) =
      ∑ p ∈ badPrimes X, ((shellOmega X).filter (fun n => badPrime p n)).card := by
  simp only [Y]
  exact sum_card_filter_comm (shellOmega X) (badPrimes X) (fun n p => badPrime p n)

/-! ## First-moment identity -/

/-- The first factorial moment equals the sum of local densities (Fubini, no independence
assumption). -/
theorem mu_one_eq_lambda (X : ℕ) : mu X 1 = lambda X := by
  unfold mu lambda beta
  rw [← Finset.mul_sum]
  congr 1
  have hchoose : (∑ n ∈ shellOmega X, (Nat.choose (Y X n) 1 : ℝ)) =
      ∑ n ∈ shellOmega X, (Y X n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Nat.choose_one_right]
  rw [hchoose]
  exact_mod_cast (sum_Y_eq_sum_badPrime_count X)

/-! ## Bridge to Bonferroni's `factorialMoment` -/

/-- The real-valued form of `factorialMoment`. -/
lemma factorialMoment_cast (Ω P : Finset ℕ) (S : ℕ → Finset ℕ) (j : ℕ) :
    (factorialMoment Ω P S j : ℝ) = ∑ n ∈ Ω, (Nat.choose (badCount P S n) j : ℝ) := by
  unfold factorialMoment
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro n _
  norm_cast

/-- `mu X j` is exactly `(1 / X)` times Bonferroni's `factorialMoment`, via the finite
witness `badWitness X`. -/
theorem mu_eq_factorialMoment_div (X j : ℕ) :
    mu X j = (1 / (X : ℝ)) * (factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) := by
  unfold mu
  rw [factorialMoment_cast]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hnle : n ≤ 2 * X := by
    rw [shellOmega] at hn
    exact (Finset.mem_Icc.mp hn).2
  simp [badCount_eq_Y X n hnle]

/-! ## Nonnegativity -/

/-- Every factorial moment `mu X j` is nonnegative. -/
theorem mu_nonneg (X j : ℕ) : 0 ≤ mu X j := by
  unfold mu
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg X))
    (Finset.sum_nonneg fun n _ => Nat.cast_nonneg (Nat.choose (Y X n) j))

/-- Every local density `beta p X` is nonnegative. -/
theorem beta_nonneg (p X : ℕ) : 0 ≤ beta p X := by
  unfold beta
  exact mul_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg X)) (Nat.cast_nonneg _)

end Erdos291
