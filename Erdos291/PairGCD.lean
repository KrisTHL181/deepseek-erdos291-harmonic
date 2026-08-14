import Erdos291.BadSet
import Erdos291.DoubleCount
import Erdos291.GapPolynomial
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Erdős #291 — the integer `A_r = r! · H_r` and the pair gcd criterion

For a prime `p`, the "bad digit" set `E p` records the `r ∈ [1, p - 1]` with `p ∣ (harmonic r).num`.
The harmonic number `H_r` is a rational, but multiplying by `r!` clears its denominator:

    `A_r = r! · H_r = Σ_{k = 1}^r r!/k`   (an integer, since `k ∣ r!` for `k ≤ r`).

Because `p ∤ r!` whenever `r < p`, the condition `r ∈ E p` is equivalent to `p ∣ A_r`.
The point of this file is a *pair* criterion: for `1 ≤ r` and `r + d < p`,

    `r, r + d ∈ E p  ⟺  p ∣ gcd (A_r, Q_d(r))`,

where `Q_d(r) = Σ_i ∏_{j ≠ i} (r + j)` is the (integer) evaluation of the formal derivative
of `∏_{j = 1}^d (X + j)` at `r`.  This strengthens `GapPolynomial`'s Theorem A by keeping
the `r ∈ E p` condition explicit through the integer `A_r` rather than only through a
`ZMod p` vanishing.

The main algebraic input is the shift identity

    `A_{r + d} = P_d(r) · A_r + r! · Q_d(r)`,   where   `P_d(r) = ∏_{j = 1}^d (r + j)`,

which follows from `H_{r + d} = H_r + Σ_{j = 1}^d 1/(r + j)` and `(r + d)! = r! · P_d(r)`.
-/

open scoped BigOperators
open scoped Nat

namespace Erdos291

/-- `A_r = r! · H_r = Σ_{k = 1}^r r!/k`, an integer since `k ∣ r!` for `k ≤ r`. -/
def A (r : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 r, (r)! / k

/-- `P_d(r) = ∏_{j = 1}^d (r + j)`, the integer value of `∏ (X + j)` at `r`. -/
def Pval (r d : ℕ) : ℕ := ∏ j ∈ Finset.Icc 1 d, (r + j)

/-- `Q_d(r) = Σ_{i = 1}^d ∏_{j ≠ i} (r + j)`, the integer value of the derivative of
`∏ (X + j)` at `r`. -/
def Qval (r d : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 d, ∏ j ∈ (Finset.Icc 1 d).erase i, (r + j)

/-- Unfolding `A`: `A_r = Σ_{k = 1}^r r!/k`. -/
theorem A_eq_sum_factorial_div (r : ℕ) :
    A r = ∑ k ∈ Finset.Icc 1 r, (r)! / k :=
  rfl

/-! ## Basic identities -/

/-- `P_d(r)` equals the ascending factorial `(r + 1)·(r + 2)⋯(r + d)`. -/
lemma Pval_eq_ascFactorial (r d : ℕ) : Pval r d = (r + 1).ascFactorial d := by
  rw [Pval]
  rw [Nat.ascFactorial_eq_prod_range (r + 1) d]
  symm
  refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    have hi' : i < d := Finset.mem_range.mp hi
    omega
  · intro i₁ _ i₂ _ h
    omega
  · intro j hj
    have hj' : 1 ≤ j ∧ j ≤ d := Finset.mem_Icc.mp hj
    refine ⟨j - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro i _
    omega

/-- `r! · P_d(r) = (r + d)!`. -/
lemma factorial_mul_Pval (r d : ℕ) : (r)! * Pval r d = (r + d)! := by
  rw [Pval_eq_ascFactorial]
  exact Nat.factorial_mul_ascFactorial r d

/-- `(A_r : ℚ) = (r! : ℚ) · harmonic r`. -/
lemma A_eq_factorial_mul_harmonic (r : ℕ) :
    (A r : ℚ) = ((r)! : ℚ) * harmonic r := by
  have hharm : harmonic r = ∑ k ∈ Finset.Icc 1 r, (k : ℚ)⁻¹ := by
    rw [harmonic]
    exact sum_range_one_add r (fun k => (k : ℚ)⁻¹)
  rw [A, hharm, Finset.mul_sum]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := by
    have h1k : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    omega
  have hkr : k ≤ r := (Finset.mem_Icc.mp hk).2
  have hkfac : k ∣ (r)! := Nat.dvd_factorial hkpos hkr
  rw [Rat.natCast_div (r)! k hkfac, div_eq_mul_inv]

/-- Reindex `Σ_{j = r+1}^{r+d} j⁻¹` as `Σ_{i = 1}^d (r + i)⁻¹`. -/
lemma sum_inv_Icc_one_add (r d : ℕ) :
    (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹)) =
      ∑ j ∈ Finset.Icc (r + 1) (r + d), ((j : ℕ) : ℚ)⁻¹ := by
  refine Finset.sum_bij (fun i _ => r + i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    have hi' : 1 ≤ i ∧ i ≤ d := Finset.mem_Icc.mp hi
    omega
  · intro i₁ _ i₂ _ h
    omega
  · intro j hj
    have hj' : r + 1 ≤ j ∧ j ≤ r + d := Finset.mem_Icc.mp hj
    refine ⟨j - r, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i _
    rfl

/-- `harmonic (r + d) = harmonic r + Σ_{i = 1}^d (r + i)⁻¹`. -/
lemma harmonic_add_eq_add_sum (r d : ℕ) :
    harmonic (r + d) = harmonic r + ∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹) := by
  have hharm_rd : harmonic (r + d) = ∑ k ∈ Finset.Icc 1 (r + d), (k : ℚ)⁻¹ := by
    rw [harmonic]
    exact sum_range_one_add (r + d) (fun k => (k : ℚ)⁻¹)
  have hharm_r : harmonic r = ∑ k ∈ Finset.Icc 1 r, (k : ℚ)⁻¹ := by
    rw [harmonic]
    exact sum_range_one_add r (fun k => (k : ℚ)⁻¹)
  rw [hharm_rd, hharm_r]
  rw [← sum_Icc_split_add (fun k => (k : ℚ)⁻¹) r d]
  rw [(sum_inv_Icc_one_add r d).symm]

/-- `(P_d(r) : ℚ) · (r + i)⁻¹ = ↑(∏_{j ≠ i} (r + j))` for `i ∈ [1, d]`. -/
lemma Pval_mul_inv_eq_prod_erase (r d i : ℕ) (hi : i ∈ Finset.Icc 1 d) :
    (Pval r d : ℚ) * (((r + i : ℕ) : ℚ)⁻¹) =
      (((∏ j ∈ (Finset.Icc 1 d).erase i, (r + j)) : ℕ) : ℚ) := by
  have hprod : (r + i) * ∏ j ∈ (Finset.Icc 1 d).erase i, (r + j) = Pval r d := by
    rw [Pval]
    exact Finset.mul_prod_erase (Finset.Icc 1 d) (fun j => r + j) hi
  have hprod' : ((r + i : ℕ) : ℚ) * (((∏ j ∈ (Finset.Icc 1 d).erase i, (r + j)) : ℕ) : ℚ) = (Pval r d : ℚ) := by
    norm_cast
  have ha : ((r + i : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (by
      have hi' : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      omega : r + i ≠ 0)
  calc
    (Pval r d : ℚ) * (((r + i : ℕ) : ℚ)⁻¹)
        = (((r + i : ℕ) : ℚ) * (((∏ j ∈ (Finset.Icc 1 d).erase i, (r + j)) : ℕ) : ℚ)) * (((r + i : ℕ) : ℚ)⁻¹) := by
            rw [← hprod']
    _ = (((∏ j ∈ (Finset.Icc 1 d).erase i, (r + j)) : ℕ) : ℚ) := by
            rw [mul_assoc, mul_left_comm, mul_inv_cancel₀ ha, mul_one]

/-! ## The shift identity -/

/-- The shift identity over `ℚ`: `(A_{r+d} : ℚ) = (P_d(r) : ℚ) · (A_r : ℚ) + (r! : ℚ) · (Q_d(r) : ℚ)`. -/
lemma A_shift_over_rat (r d : ℕ) :
    (A (r + d) : ℚ) =
      (Pval r d : ℚ) * (A r : ℚ) + ((r)! : ℚ) * (Qval r d : ℚ) := by
  have hfac : ((r + d)! : ℚ) = ((r)! : ℚ) * (Pval r d : ℚ) := by
    rw [← Nat.cast_mul]
    exact_mod_cast (factorial_mul_Pval r d).symm
  have hfirst : ((r + d)! : ℚ) * harmonic r = (Pval r d : ℚ) * (A r : ℚ) := by
    calc
      ((r + d)! : ℚ) * harmonic r
          = (((r)! : ℚ) * (Pval r d : ℚ)) * harmonic r := by rw [hfac]
      _ = (Pval r d : ℚ) * (((r)! : ℚ) * harmonic r) := by ring
      _ = (Pval r d : ℚ) * (A r : ℚ) := by
            rw [A_eq_factorial_mul_harmonic r]
  have hsecond : ((r + d)! : ℚ) * (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹)) =
      ((r)! : ℚ) * (Qval r d : ℚ) := by
    calc
      ((r + d)! : ℚ) * (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹))
          = (((r)! : ℚ) * (Pval r d : ℚ)) * (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹)) := by
              rw [hfac]
      _ = ((r)! : ℚ) * ((Pval r d : ℚ) * (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹))) := by
              ring
      _ = ((r)! : ℚ) * (∑ i ∈ Finset.Icc 1 d, ((Pval r d : ℚ) * (((r + i : ℕ) : ℚ)⁻¹))) := by
              rw [Finset.mul_sum]
      _ = ((r)! : ℚ) * (∑ i ∈ Finset.Icc 1 d, (((∏ j ∈ (Finset.Icc 1 d).erase i, (r + j)) : ℕ) : ℚ)) := by
              apply congrArg (fun x => ((r)! : ℚ) * x)
              apply Finset.sum_congr rfl
              intro i hi
              exact Pval_mul_inv_eq_prod_erase r d i hi
      _ = ((r)! : ℚ) * (Qval r d : ℚ) := by
              rw [Qval, Nat.cast_sum]
  calc
    (A (r + d) : ℚ)
        = ((r + d)! : ℚ) * harmonic (r + d) :=
            A_eq_factorial_mul_harmonic (r + d)
    _ = ((r + d)! : ℚ) * (harmonic r + ∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹)) := by
            rw [harmonic_add_eq_add_sum r d]
    _ = ((r + d)! : ℚ) * harmonic r + ((r + d)! : ℚ) * (∑ i ∈ Finset.Icc 1 d, (((r + i : ℕ) : ℚ)⁻¹)) := by
            ring
    _ = (Pval r d : ℚ) * (A r : ℚ) + ((r)! : ℚ) * (Qval r d : ℚ) := by
            rw [hfirst, hsecond]

/-- The shift identity `A_{r + d} = P_d(r) · A_r + r! · Q_d(r)`. -/
theorem A_shift (r d : ℕ) :
    A (r + d) = Pval r d * A r + (r)! * Qval r d := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  exact A_shift_over_rat r d

/-! ## The bridge: `p ∣ A_r ⟺ r ∈ E p` -/

/-- `p ∤ r!` whenever `r < p`. -/
lemma not_dvd_factorial_of_lt (p r : ℕ) [Fact p.Prime] (hrp : r < p) : ¬ p ∣ (r)! := by
  have hp : Nat.Prime p := Fact.out
  intro h
  exact (not_lt_of_ge (hp.dvd_factorial.mp h)) hrp

/-- Cross-multiplication identity `A_r · L r = r! · a r`. -/
lemma A_mul_L_eq_factorial_mul_a (r : ℕ) :
    A r * L r = (r)! * a r := by
  have h1 : (A r : ℚ) = ((r)! : ℚ) * harmonic r :=
    A_eq_factorial_mul_harmonic r
  have hL0 : (L r : ℚ) ≠ 0 := by exact_mod_cast (L_ne_zero r)
  have hHL : harmonic r * (L r : ℚ) = (a r : ℚ) := by
    rw [harmonic_eq_a_div_L r, div_mul_cancel₀ (a r : ℚ) hL0]
  have h4 : (A r : ℚ) * (L r : ℚ) = ((r)! : ℚ) * (a r : ℚ) := by
    rw [h1, mul_assoc, hHL]
  exact_mod_cast h4

/-- `p ∣ A_r ⟺ p ∣ a r` for `r < p`. -/
lemma prime_dvd_A_iff_dvd_a (p r : ℕ) [Fact p.Prime] (hrp : r < p) :
    p ∣ A r ↔ p ∣ a r := by
  have hp : Nat.Prime p := Fact.out
  have hmul : A r * L r = (r)! * a r :=
    A_mul_L_eq_factorial_mul_a r
  have hpnL : ¬ p ∣ L r := not_dvd_L_of_lt p r hrp
  have hpnfac : ¬ p ∣ (r)! := not_dvd_factorial_of_lt p r hrp
  constructor
  · intro h
    have h' : p ∣ A r * L r := dvd_mul_of_dvd_left h (L r)
    rw [hmul] at h'
    rcases hp.dvd_mul.mp h' with h1 | h2
    · exact (hpnfac h1).elim
    · exact h2
  · intro h
    have h' : p ∣ (r)! * a r := dvd_mul_of_dvd_right h (r)!
    rw [← hmul] at h'
    rcases hp.dvd_mul.mp h' with h1 | h2
    · exact h1
    · exact (hpnL h2).elim

/-- For `1 ≤ r < p`, `p ∣ A_r ⟺ r ∈ E p`. -/
lemma prime_dvd_A_iff_mem_E (p r : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrp : r < p) :
    p ∣ A r ↔ r ∈ E p := by
  have hp : Nat.Prime p := Fact.out
  have hE : r ∈ E p ↔ p ∣ a r := by
    rw [mem_E_iff_dvd_num p r hp h1r hrp]
    exact num_dvd_iff_a_dvd p r hrp
  exact (prime_dvd_A_iff_dvd_a p r hrp).trans hE.symm

/-! ## The pair gcd criterion -/

/-- **The strengthening.** For a prime `p` and `1 ≤ r`, `r + d < p`:

`r, r + d ∈ E p  ⟺  p ∣ gcd (A_r, Q_d(r))`.

The hypotheses `1 ≤ r` and `r + d < p` are the exact ones needed for the bridge
`p ∣ A_n ⟺ n ∈ E p` to apply at `n = r` and `n = r + d` (a separate lower bound on `d` is
unnecessary: `1 ≤ r + d` follows from `1 ≤ r`). -/
theorem pair_bad_iff_prime_dvd_gcd (p r d : ℕ) [Fact p.Prime] (h1r : 1 ≤ r) (hrd : r + d < p) :
    (r ∈ E p ∧ r + d ∈ E p) ↔ p ∣ Nat.gcd (A r) (Qval r d) := by
  have hp : Nat.Prime p := Fact.out
  have hr_lt : r < p := by omega
  have hradd_ge : 1 ≤ r + d := by omega
  constructor
  · intro h
    rcases h with ⟨hrE, hraddE⟩
    have hdvd_r : p ∣ A r :=
      (prime_dvd_A_iff_mem_E p r h1r hr_lt).mpr hrE
    have hdvd_rd : p ∣ A (r + d) :=
      (prime_dvd_A_iff_mem_E p (r + d) hradd_ge hrd).mpr hraddE
    have hsum : p ∣ Pval r d * A r + (r)! * Qval r d := by
      rw [← A_shift r d]
      exact hdvd_rd
    have hA : p ∣ Pval r d * A r := dvd_mul_of_dvd_right hdvd_r (Pval r d)
    have hB : p ∣ (r)! * Qval r d := (Nat.dvd_add_iff_right hA).mpr hsum
    have hQ : p ∣ Qval r d := by
      rcases hp.dvd_mul.mp hB with h | h
      · exact (not_dvd_factorial_of_lt p r hr_lt h).elim
      · exact h
    exact Nat.dvd_gcd hdvd_r hQ
  · intro hgcd
    have hdvd_r : p ∣ A r := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
    have hQ : p ∣ Qval r d := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
    have hA : p ∣ Pval r d * A r := dvd_mul_of_dvd_right hdvd_r (Pval r d)
    have hB : p ∣ (r)! * Qval r d := dvd_mul_of_dvd_right hQ (r)!
    have hsum : p ∣ Pval r d * A r + (r)! * Qval r d := Nat.dvd_add hA hB
    have hdvd_rd : p ∣ A (r + d) := by
      rwa [A_shift r d]
    have hrE : r ∈ E p :=
      (prime_dvd_A_iff_mem_E p r h1r hr_lt).mp hdvd_r
    have hraddE : r + d ∈ E p :=
      (prime_dvd_A_iff_mem_E p (r + d) hradd_ge hrd).mp hdvd_rd
    exact ⟨hrE, hraddE⟩

/-! ## Stirling number interpretation -/

/-- `A_{n + 1} = (n + 1) · A_n + n!`. -/
lemma A_succ (n : ℕ) :
    A (n + 1) = (n + 1) * A n + (n)! := by
  rw [A, A]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
  have hsum : (∑ k ∈ Finset.Icc 1 n, (n + 1)! / k) = (n + 1) * (∑ k ∈ Finset.Icc 1 n, (n)! / k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkpos : 0 < k := by
      have h1k : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      omega
    have hkr : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hkfac : k ∣ (n)! := Nat.dvd_factorial hkpos hkr
    rw [Nat.factorial_succ, Nat.mul_div_assoc (n + 1) hkfac]
  rw [hsum]
  have htop : (n + 1)! / (n + 1) = (n)! := by
    rw [Nat.factorial_succ]
    exact Nat.mul_div_right (n)! (by omega : 0 < n + 1)
  rw [htop]

/-- `A_r = {r + 1 \brack 2}`, the unsigned Stirling number of the first kind. -/
theorem A_eq_stirling (r : ℕ) : A r = Nat.stirlingFirst (r + 1) 2 := by
  induction r with
  | zero => native_decide
  | succ n ih =>
    rw [A_succ, ih]
    rw [Nat.stirlingFirst_succ_succ (n + 1) 1, Nat.stirlingFirst_one_right n]

end Erdos291
