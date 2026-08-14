import Erdos291.ShellMoments
import Erdos291.Bonferroni
import Erdos291.HAShell
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Erdős #291 — the finite-order Brun condition

On the dyadic shell `Ω_X = (X, 2X]` the random variable `Y X n` counts the bad primes of `n`.
Its normalized factorial moments `mu X j` and the expected count `lambda X = mu X 1` are already
formalized.  Write `R_j(X) = mu X j - (lambda X)^j / j!`.  The Bonferroni lower bound (odd
truncation `k = 2m + 2`) gives

    `ΔG(X) / X ≥ Σ_{j = 0}^{k - 1} (-1)^j mu_j(X)`.

Decomposing into the Poisson reference plus error,

    `Σ_{j = 0}^{k - 1} (-1)^j μ_j = Σ_{j = 0}^{k - 1} (-λ)^j / j! + Σ_{j = 0}^{k - 1} (-1)^j R_j`,

and by the alternating-series estimate `Σ_{j = 0}^{k - 1} (-λ)^j / j! ≥ η(λ, k)` (see
`sum_alternating_exp_ge_eta`).  So if the error term is `< η(λ, k)` then `ΔG(X)/X > 0`, hence
`ΔG(X) > 0`.  **The Brun condition is exactly this error bound**, and it is a sufficient
condition for `ΔG(X) > 0`; since `ΔG(X) > 0` for infinitely many `X` is equivalent to infinitely
many good `n` (`HA_shell_weak_iff_infinite`), this completes the reduction

    `HA_Brun ⟹ infinitely many n with gcd (a n) (L n) = 1`.

There are no unproved declarations in this file.
-/

open scoped BigOperators
open scoped Nat

namespace Erdos291

/-! ## The `η` function, the error term, and the Brun hypothesis -/

/-- `η(λ, k) = e^{-λ} - λ^k / k!`, the alternating-series lower bound for
`Σ_{j = 0}^{k - 1} (-λ)^j / j!`. -/
noncomputable def eta (l : ℝ) (k : ℕ) : ℝ := Real.exp (-l) - l ^ k / ((k) ! : ℝ)

/-- The truncated alternating Taylor polynomial `Σ_{j = 0}^{n - 1} (-1)^j l^j / j!`
for `e^{-l}`. -/
noncomputable def partialExpNeg (l : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1 : ℝ) ^ j * l ^ j / ((j) ! : ℝ)

/-- The (full-range) error term `Σ_{j = 0}^{k - 1} (-1)^j (mu X j - (lambda X)^j / j!)`.
For `X ≥ 1` the `j = 0` and `j = 1` summands vanish (because `mu X 0 = 1` and
`mu X 1 = lambda X`), so this coincides with `Σ_{j = 2}^{k - 1} (-1)^j R_j`. -/
noncomputable def errorBrun (X k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * (mu X j - (lambda X) ^ j / ((j) ! : ℝ))

/-- The finite-order Brun condition holds at `X` if, for some even `k ≥ 2` with `4 λ ≤ k`,
the error term is strictly smaller than `η(λ, k)`. -/
def BrunHoldsAt (X : ℕ) : Prop :=
  ∃ k : ℕ, Even k ∧ 2 ≤ k ∧ 4 * lambda X ≤ (k : ℝ) ∧ |errorBrun X k| < eta (lambda X) k

/-- The Brun hypothesis: `BrunHoldsAt X` holds for infinitely many `X`. -/
def HA_Brun : Prop := Set.Infinite { X : ℕ | BrunHoldsAt X }

/-! ## Elementary estimates for `η` -/

/-- `(k / 3)^k ≤ k!` for `k ≥ 1`. -/
lemma factorial_ge_three_pow (k : ℕ) (hk : 1 ≤ k) : ((k : ℝ) / 3) ^ k ≤ (k ! : ℝ) := by
  refine Nat.le_induction ?_ ?_ k hk
  · norm_num
  · intro n hn ih
    have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h3 : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n ≤ 3 := by
      calc
        (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n = (1 + (n : ℝ)⁻¹) ^ n := by
          congr 1
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          rw [hcast]
          field_simp [hnne]
        _ ≤ 3 := (Real.one_add_inv_pow_le_exp (n := n)).trans Real.exp_one_lt_three.le
    have hpowsplit : (((n + 1 : ℕ) : ℝ) / 3) ^ n =
        (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n * ((n : ℝ) / 3) ^ n := by
      rw [← mul_pow]
      congr 1
      field_simp [hnne]
    calc
      (((n + 1 : ℕ) : ℝ) / 3) ^ (n + 1)
        = (((n + 1 : ℕ) : ℝ) / 3) ^ n * (((n + 1 : ℕ) : ℝ) / 3) := by rw [pow_succ]
      _ = (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n * ((n : ℝ) / 3) ^ n *
            (((n + 1 : ℕ) : ℝ) / 3) := by rw [hpowsplit]
      _ ≤ 3 * ((n : ℝ) / 3) ^ n * (((n + 1 : ℕ) : ℝ) / 3) := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) * ((n : ℝ) / 3) ^ n := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * (n ! : ℝ) := by gcongr
      _ = (((n + 1) ! : ℕ) : ℝ) := by rw [Nat.factorial_succ, Nat.cast_mul]

/-- `3 / 4 < e^(-1/4)`. -/
lemma three_div_four_lt_exp_neg_quarter : (3 / 4 : ℝ) < Real.exp (-(1 / 4 : ℝ)) := by
  have h := Real.one_sub_lt_exp_neg (x := (1 / 4 : ℝ)) (by norm_num)
  norm_num at h
  exact h

/-- `η` is positive provided `k ≥ 4l` (and `k ≥ 2`). -/
lemma eta_pos (l : ℝ) (hl : 0 ≤ l) (k : ℕ) (_hk : Even k) (h2 : 2 ≤ k)
    (hkle : 4 * l ≤ (k : ℝ)) : 0 < eta l k := by
  unfold eta
  have hk1 : 1 ≤ k := by omega
  have hkpos : 0 < (k : ℝ) := by positivity
  have hk_fact : ((k : ℝ) / 3) ^ k ≤ (k ! : ℝ) := factorial_ge_three_pow k hk1
  have hinv : 1 / (k ! : ℝ) ≤ (3 / (k : ℝ)) ^ k := by
    calc
      1 / (k ! : ℝ) ≤ 1 / ((k : ℝ) / 3) ^ k :=
        one_div_le_one_div_of_le (by positivity) hk_fact
      _ = (3 / (k : ℝ)) ^ k := by rw [← one_div_pow, one_div_div]
  have h1 : l ^ k / (k ! : ℝ) ≤ (3 * l / k) ^ k := by
    calc
      l ^ k / (k ! : ℝ) = l ^ k * (1 / (k ! : ℝ)) := by rw [div_eq_mul_inv, one_div]
      _ ≤ l ^ k * (3 / (k : ℝ)) ^ k := mul_le_mul_of_nonneg_left hinv (pow_nonneg hl k)
      _ = (3 * l / k) ^ k := by
          rw [← mul_pow]
          congr 1
          field_simp [hkpos.ne']
  have hle_frac : 3 * l / k ≤ 3 / 4 := by
    rw [div_le_iff₀ hkpos]
    nlinarith [hkle]
  have h2' : (3 * l / k) ^ k ≤ (3 / 4) ^ k :=
    pow_le_pow_left₀ (by positivity) hle_frac k
  have h3 : (3 / 4) ^ k < Real.exp (-(k : ℝ) / 4) := by
    have hbase : (3 / 4 : ℝ) < Real.exp (-(1 / 4 : ℝ)) := three_div_four_lt_exp_neg_quarter
    have hpow : (3 / 4 : ℝ) ^ k < (Real.exp (-(1 / 4 : ℝ))) ^ k :=
      pow_lt_pow_left₀ hbase (by norm_num) (by omega : k ≠ 0)
    calc
      (3 / 4 : ℝ) ^ k < (Real.exp (-(1 / 4 : ℝ))) ^ k := hpow
      _ = Real.exp (k * (-(1 / 4 : ℝ))) := (Real.exp_nat_mul (-(1 / 4 : ℝ)) k).symm
      _ = Real.exp (-(k : ℝ) / 4) := by congr 1; ring
  have h4 : Real.exp (-(k : ℝ) / 4) ≤ Real.exp (-l) := by
    apply Real.exp_le_exp.mpr
    have hldiv : l ≤ (k : ℝ) / 4 := by
      rw [le_div_iff₀ (by norm_num : 0 < (4 : ℝ))]
      linarith [hkle]
    linarith
  have hmain : l ^ k / (k ! : ℝ) < Real.exp (-l) := by
    calc
      l ^ k / (k ! : ℝ) ≤ (3 * l / k) ^ k := h1
      _ ≤ (3 / 4) ^ k := h2'
      _ < Real.exp (-(k : ℝ) / 4) := h3
      _ ≤ Real.exp (-l) := h4
  linarith

/-! ## The alternating-series lower bound for `e^{-l}` -/

/-- `partialExpNeg 0 (n + 1) = 1`. -/
lemma partialExpNeg_zero (n : ℕ) : partialExpNeg 0 (n + 1) = 1 := by
  rw [partialExpNeg]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro b _ hb0
    rw [zero_pow hb0]
    simp
  · intro h
    have hmem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    exfalso
    exact h hmem

/-- `(-1)^(n+1) · (n+1) / (n+1)! = -(-1)^n / n!`. -/
lemma neg_one_pow_succ_mul_cast_ratio (n : ℕ) :
    (-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) / (((n + 1) ! : ℕ) : ℝ) = -((-1 : ℝ) ^ n / (n ! : ℝ)) := by
  have hfac : (((n + 1) ! : ℕ) : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]
    norm_num
  rw [hfac]
  rw [show (n + 1 : ℝ) = (n : ℝ) + 1 by norm_num]
  have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn, hn1]
  rw [pow_succ]
  ring

/-- `partialExpNeg l (n + 1) = partialExpNeg l n + (-1)^n · l^n / n!`. -/
lemma partialExpNeg_succ (l : ℝ) (n : ℕ) :
    partialExpNeg l (n + 1) = partialExpNeg l n + (-1 : ℝ) ^ n * l ^ n / (n ! : ℝ) := by
  rw [partialExpNeg, partialExpNeg, Finset.sum_range_succ]

/-- The derivative of `partialExpNeg · (n + 1)` is `-partialExpNeg · n`. -/
lemma hasDerivAt_partialExpNeg_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => partialExpNeg t (n + 1)) (-partialExpNeg x n) x := by
  induction n with
  | zero =>
      have h1 : (fun t : ℝ => partialExpNeg t 1) = fun _ => 1 := by
        funext t
        rw [partialExpNeg]
        simp
      have hp0 : partialExpNeg x 0 = 0 := by rw [partialExpNeg, Finset.sum_range_zero]
      rw [h1, hp0, neg_zero]
      exact hasDerivAt_const x (1 : ℝ)
  | succ n ih =>
      have htop : (-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) * x ^ n / (((n + 1) ! : ℕ) : ℝ) =
          -((-1 : ℝ) ^ n * x ^ n / (n ! : ℝ)) := by
        calc
          (-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) * x ^ n / (((n + 1) ! : ℕ) : ℝ)
            = x ^ n * ((-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) / (((n + 1) ! : ℕ) : ℝ)) := by
                rw [div_eq_mul_inv]
                ring
          _ = x ^ n * (-((-1 : ℝ) ^ n / (n ! : ℝ))) := by rw [neg_one_pow_succ_mul_cast_ratio n]
          _ = -((-1 : ℝ) ^ n * x ^ n / (n ! : ℝ)) := by
                rw [div_eq_mul_inv]
                ring
      have hterm : HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ (n + 1) * t ^ (n + 1) / (((n + 1) ! : ℕ) : ℝ))
          ((-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) * x ^ n / (((n + 1) ! : ℕ) : ℝ)) x := by
        have hpow : HasDerivAt (fun t : ℝ => t ^ (n + 1)) ((n + 1 : ℝ) * x ^ n) x := by
          simpa using hasDerivAt_pow (n + 1) x
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
          hpow.mul_const ((-1 : ℝ) ^ (n + 1) / (((n + 1) ! : ℕ) : ℝ))
      have hderiv : HasDerivAt (fun t : ℝ => partialExpNeg t (n + 2))
          (-partialExpNeg x n + (-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) * x ^ n / (((n + 1) ! : ℕ) : ℝ)) x := by
        have hrec : (fun t : ℝ => partialExpNeg t (n + 2)) =
            (fun t : ℝ => partialExpNeg t (n + 1) +
              (-1 : ℝ) ^ (n + 1) * t ^ (n + 1) / (((n + 1) ! : ℕ) : ℝ)) := by
          funext t
          exact partialExpNeg_succ t (n + 1)
        rw [hrec]
        exact ih.add hterm
      have hA : -partialExpNeg x n + (-1 : ℝ) ^ (n + 1) * (n + 1 : ℝ) * x ^ n / (((n + 1) ! : ℕ) : ℝ) =
          -partialExpNeg x (n + 1) := by
        rw [partialExpNeg_succ x n]
        rw [neg_add]
        linarith [htop]
      exact hderiv.congr_deriv hA

/-- Monotonicity on `[0, ∞)` from a nonnegative derivative. -/
private lemma monotoneOn_Ici_of_hasDerivAt_nonneg {f f' : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt f (f' x) x)
    (hpos : ∀ x : ℝ, 0 < x → 0 ≤ f' x) : MonotoneOn f (Set.Ici 0) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) (f' := f') hcont ?_ ?_
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    exact (hderiv x hx').hasDerivWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    exact hpos x hx'

/-- A function which is `0` at `0` and monotone on `[0, ∞)` is nonnegative there. -/
private lemma nonneg_of_monotoneOn_Ici {f : ℝ → ℝ} (hf0 : f 0 = 0)
    (hmono : MonotoneOn f (Set.Ici 0)) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have h : f 0 ≤ f x := hmono (Set.mem_Ici.mpr (by norm_num : 0 ≤ (0 : ℝ))) (Set.mem_Ici.mpr hx) hx
  rwa [hf0] at h

/-- `partialExpNeg · n` is continuous (it is a polynomial in the variable). -/
lemma continuous_partialExpNeg (n : ℕ) : Continuous (fun t : ℝ => partialExpNeg t n) := by
  unfold partialExpNeg
  refine continuous_finsetSum (Finset.range n) (fun j _ => ?_)
  exact (continuous_const.mul (continuous_id.pow j)).div_const ((j ! : ℕ) : ℝ)

/-- The sharp alternating-series remainder bound `|e^{-x} - Σ_{j=0}^{n-1} (-x)^j/j!| ≤ x^n/n!`
for `x ≥ 0`. -/
lemma abs_exp_neg_sub_partial_le (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    |Real.exp (-x) - partialExpNeg x n| ≤ x ^ n / ((n) ! : ℝ) := by
  induction n generalizing x with
  | zero =>
      rw [partialExpNeg, Finset.sum_range_zero]
      have hle : Real.exp (-x) ≤ 1 := by
        calc
          Real.exp (-x) ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
          _ = 1 := by norm_num
      simpa [abs_of_nonneg (Real.exp_pos (-x)).le] using hle
  | succ n ih =>
      let f : ℝ → ℝ := fun t => Real.exp (-t) - partialExpNeg t (n + 1)
      have hf0 : f 0 = 0 := by
        dsimp [f]
        rw [partialExpNeg_zero n]
        simp
      have hexp (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
        have hneg : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) t := (hasDerivAt_id t).neg
        simpa [mul_neg_one] using hneg.exp
      have hpow (t : ℝ) : HasDerivAt (fun s : ℝ => s ^ (n + 1) / ((n + 1) ! : ℝ))
          ((n + 1 : ℝ) * t ^ n / ((n + 1) ! : ℝ)) t := by
        convert (hasDerivAt_pow (n + 1) t).div_const (((n + 1) ! : ℕ) : ℝ) using 1 <;> first | rfl | simp
      have hpow_simp (t : ℝ) : (n + 1 : ℝ) * t ^ n / ((n + 1) ! : ℝ) = t ^ n / (n ! : ℝ) := by
        have hfac : ((n + 1) ! : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
          rw [Nat.factorial_succ]
          norm_num
        rw [hfac]
        have hn : (n ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
        have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hn, hn1]
      have hfderiv (t : ℝ) : HasDerivAt f (-(Real.exp (-t) - partialExpNeg t n)) t := by
        dsimp [f]
        have hpart : HasDerivAt (fun s : ℝ => partialExpNeg s (n + 1)) (-partialExpNeg t n) t :=
          hasDerivAt_partialExpNeg_succ n t
        exact ((hexp t).sub hpart).congr_deriv (by ring)
      -- upper bound
      have hU : f x ≤ x ^ (n + 1) / ((n + 1) ! : ℝ) := by
        have hUx : 0 ≤ x ^ (n + 1) / ((n + 1) ! : ℝ) - f x := by
          apply nonneg_of_monotoneOn_Ici ?_ ?_ hx
          · rw [hf0]
            simp [zero_pow (by omega : n + 1 ≠ 0)]
          · apply monotoneOn_Ici_of_hasDerivAt_nonneg
            · dsimp [f]
              exact (((continuous_id.pow (n + 1)).div_const (((n + 1) ! : ℕ) : ℝ)).sub
                ((Real.continuous_exp.comp continuous_neg).sub (continuous_partialExpNeg (n + 1)))).continuousOn
            · intro t ht
              have hderivU : HasDerivAt (fun t : ℝ => t ^ (n + 1) / ((n + 1) ! : ℝ) - f t)
                  (t ^ n / (n ! : ℝ) + (Real.exp (-t) - partialExpNeg t n)) t := by
                exact ((hpow t).sub (hfderiv t)).congr_deriv (by rw [hpow_simp t]; ring)
              exact hderivU
            · intro t ht
              have hih' := ih t (le_of_lt ht)
              have hneg : -(t ^ n / (n ! : ℝ)) ≤ Real.exp (-t) - partialExpNeg t n :=
                (abs_le.mp hih').1
              linarith
        linarith
      -- lower bound
      have hL : -(x ^ (n + 1) / ((n + 1) ! : ℝ)) ≤ f x := by
        have hVx : 0 ≤ f x + x ^ (n + 1) / ((n + 1) ! : ℝ) := by
          apply nonneg_of_monotoneOn_Ici ?_ ?_ hx
          · rw [hf0]
            simp [zero_pow (by omega : n + 1 ≠ 0)]
          · apply monotoneOn_Ici_of_hasDerivAt_nonneg
            · dsimp [f]
              exact (((Real.continuous_exp.comp continuous_neg).sub (continuous_partialExpNeg (n + 1))).add
                ((continuous_id.pow (n + 1)).div_const (((n + 1) ! : ℕ) : ℝ))).continuousOn
            · intro t ht
              have hderivV : HasDerivAt (fun t : ℝ => f t + t ^ (n + 1) / ((n + 1) ! : ℝ))
                  (-(Real.exp (-t) - partialExpNeg t n) + t ^ n / (n ! : ℝ)) t := by
                exact ((hfderiv t).add (hpow t)).congr_deriv (by rw [hpow_simp t])
              exact hderivV
            · intro t ht
              have hih' := ih t (le_of_lt ht)
              have hle : Real.exp (-t) - partialExpNeg t n ≤ t ^ n / (n ! : ℝ) :=
                (abs_le.mp hih').2
              linarith
        nlinarith
      exact abs_le.mpr ⟨hL, hU⟩

/-- `η(l, k) ≤ Σ_{j=0}^{k-1} (-1)^j l^j / j!` (the alternating-series lower bound). -/
lemma sum_alternating_exp_ge_eta (l : ℝ) (hl : 0 ≤ l) (k : ℕ) (_hk : Even k) (_h2 : 2 ≤ k) :
    eta l k ≤ ∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * l ^ j / ((j) ! : ℝ) := by
  unfold eta
  have h := abs_exp_neg_sub_partial_le l hl k
  have hle : Real.exp (-l) - partialExpNeg l k ≤ l ^ k / (k ! : ℝ) := (abs_le.mp h).2
  rw [partialExpNeg] at hle
  linarith

/-! ## `mu X 0 = 1` -/

/-- `mu X 0 = 1` for `X ≥ 1` (the shell `(X, 2X]` has `X` elements). -/
lemma mu_zero_eq_one (X : ℕ) (hX : 1 ≤ X) : mu X 0 = 1 := by
  unfold mu
  have hchoose : (∑ n ∈ shellOmega X, (Nat.choose (Y X n) 0 : ℝ)) = (X : ℝ) := by
    calc
      (∑ n ∈ shellOmega X, (Nat.choose (Y X n) 0 : ℝ))
          = ∑ n ∈ shellOmega X, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n _
            simp
      _ = ((shellOmega X).card : ℝ) := by
            exact_mod_cast (Finset.card_eq_sum_ones (shellOmega X)).symm
      _ = (X : ℝ) := by
            have hcard : (shellOmega X).card = X := by
              rw [shellOmega, Nat.card_Icc]
              omega
            exact_mod_cast hcard
  rw [hchoose]
  have hXne : (X : ℝ) ≠ 0 := by exact_mod_cast (by omega : X ≠ 0)
  exact one_div_mul_cancel hXne

/-! ## No bad prime iff `gcd = 1` -/

/-- `m = 1` iff no prime divides `m`. -/
lemma eq_one_iff_forall_not_prime_dvd (m : ℕ) :
    m = 1 ↔ ∀ p : ℕ, p.Prime → ¬ p ∣ m := by
  constructor
  · rintro rfl p hp h
    exact hp.not_dvd_one h
  · intro h
    by_contra hm
    rcases Nat.exists_prime_and_dvd hm with ⟨p, hp, hpd⟩
    exact h p hp hpd

/-- A prime divisor of `gcd (a n) (L n)` is at most `n` (hence at most `2X` if `n ≤ 2X`). -/
lemma prime_dvd_gcd_le (X n p : ℕ) (hn : n ≤ 2 * X) (hp : p.Prime)
    (hdvd : p ∣ Nat.gcd (a n) (L n)) : p ≤ 2 * X := by
  have hdL : p ∣ L n := dvd_trans hdvd (Nat.gcd_dvd_right (a n) (L n))
  have hpf : p ∈ (L n).primeFactors := hp.mem_primeFactors hdL (L_ne_zero n)
  rw [Nat.primeFactors_lcmUpto n, Nat.mem_primesLE] at hpf
  exact le_trans hpf.1 hn

/-- For `n ≤ 2X`, `badCount (badPrimes X) (badWitness X) n = 0` iff `gcd (a n) (L n) = 1`. -/
lemma badCount_eq_zero_iff_gcd_one (X n : ℕ) (hn : n ≤ 2 * X) :
    badCount (badPrimes X) (badWitness X) n = 0 ↔ Nat.gcd (a n) (L n) = 1 := by
  rw [badCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  have hmem_badWitness : ∀ p : ℕ, n ∈ badWitness X p ↔ badPrime p n := by
    intro p
    rw [badWitness, Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨Finset.mem_range.mpr (by omega), h⟩
  have hmem_badPrimes : ∀ p : ℕ, p ∈ badPrimes X ↔ p.Prime ∧ p ≤ 2 * X := by
    intro p
    rw [badPrimes, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.2, (Finset.mem_Icc.mp h.1).2⟩
    · intro h
      exact ⟨Finset.mem_Icc.mpr ⟨h.1.two_le, h.2⟩, h.1⟩
  constructor
  · intro h
    rw [eq_one_iff_forall_not_prime_dvd]
    intro p hp
    by_contra hpd
    have hle : p ≤ 2 * X := prime_dvd_gcd_le X n p hn hp hpd
    have hbad : p ∈ badPrimes X := (hmem_badPrimes p).mpr ⟨hp, hle⟩
    have hnw : ¬ n ∈ badWitness X p := h hbad
    exact hnw ((hmem_badWitness p).mpr hpd)
  · intro hg p hpmem
    have hp : p.Prime := (hmem_badPrimes p).mp hpmem |>.1
    intro hbp
    exact (eq_one_iff_forall_not_prime_dvd (Nat.gcd (a n) (L n))).mp hg p hp ((hmem_badWitness p).mp hbp)

/-! ## The main theorem -/

/-- If the Brun condition holds at `X`, then the shell `(X, 2X]` contains a good integer. -/
lemma brunHoldsAt_implies_deltaG_pos (X : ℕ) (h : BrunHoldsAt X) : 0 < deltaG X := by
  rcases h with ⟨k, hkEven, hk2, hkle, herr⟩
  let m := (k - 2) / 2
  have hk_eq : 2 * m + 2 = k := by
    dsimp [m]
    rcases hkEven with ⟨r, hr⟩
    subst k
    omega
  have hbonf : (((shellOmega X).filter (fun n => badCount (badPrimes X) (badWitness X) n = 0)).card : ℤ) ≥
      ∑ j ∈ Finset.range (2 * m + 2), ((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j :=
    bonferroni_lower (shellOmega X) (badPrimes X) (badWitness X) m
  have hbonfR : (((shellOmega X).filter (fun n => badCount (badPrimes X) (badWitness X) n = 0)).card : ℝ) ≥
      (∑ j ∈ Finset.range k, ((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) := by
    have htmp : (((shellOmega X).filter (fun n => badCount (badPrimes X) (badWitness X) n = 0)).card : ℝ) ≥
        (∑ j ∈ Finset.range (2 * m + 2), ((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) := by
      exact_mod_cast hbonf
    simpa [hk_eq] using htmp
  have hfilter : (shellOmega X).filter (fun n => badCount (badPrimes X) (badWitness X) n = 0) =
      (shellOmega X).filter (fun n => Nat.gcd (a n) (L n) = 1) := by
    apply Finset.filter_congr
    intro n hn
    exact badCount_eq_zero_iff_gcd_one X n (by
      rw [shellOmega, Finset.mem_Icc] at hn
      exact hn.2)
  have hdelta : (((shellOmega X).filter (fun n => Nat.gcd (a n) (L n) = 1)).card : ℝ) = (deltaG X : ℝ) := by
    rw [shellOmega]
    exact_mod_cast (shell_count_identity X).symm
  have hgood : (((shellOmega X).filter (fun n => badCount (badPrimes X) (badWitness X) n = 0)).card : ℝ) =
      (deltaG X : ℝ) := by
    rw [hfilter, hdelta]
  have hbonfG : (deltaG X : ℝ) ≥
      (∑ j ∈ Finset.range k, ((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) := by
    rwa [← hgood]
  have hX : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hdiv : (deltaG X : ℝ) / (X : ℝ) ≥
      (∑ j ∈ Finset.range k, ((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right hbonfG hX
  have hsum_mu : (∑ j ∈ Finset.range k, ((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) / (X : ℝ) =
      ∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * mu X j := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    have hm : (factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) / (X : ℝ) = mu X j := by
      rw [div_eq_mul_inv, mul_comm, ← one_div, mu_eq_factorialMoment_div X j]
    calc
      (((-1 : ℤ) ^ j) * factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) / (X : ℝ)
          = (((-1 : ℝ) ^ j) * (factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ)) / (X : ℝ) := by norm_cast
      _ = ((-1 : ℝ) ^ j) * ((factorialMoment (shellOmega X) (badPrimes X) (badWitness X) j : ℝ) / (X : ℝ)) := by rw [mul_div_assoc]
      _ = ((-1 : ℝ) ^ j) * mu X j := by rw [hm]
  have hlower : (deltaG X : ℝ) / (X : ℝ) ≥ ∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * mu X j := by
    rw [← hsum_mu]
    exact hdiv
  have hdecomp : (∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * mu X j) =
      (∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * (lambda X) ^ j / ((j) ! : ℝ)) + errorBrun X k := by
    rw [errorBrun]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_sub]
    rw [← mul_div_assoc]
    rw [add_comm, sub_add_cancel]
  have hlam_nonneg : 0 ≤ lambda X := by
    unfold lambda
    exact Finset.sum_nonneg (fun p _ => beta_nonneg p X)
  have hsum_ge : (∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * (lambda X) ^ j / ((j) ! : ℝ)) ≥ eta (lambda X) k :=
    sum_alternating_exp_ge_eta (lambda X) hlam_nonneg k hkEven hk2
  have herr_ge : -|errorBrun X k| ≤ errorBrun X k := (abs_le.mp (le_rfl : |errorBrun X k| ≤ |errorBrun X k|)).1
  have htotal : (∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * mu X j) ≥ eta (lambda X) k - |errorBrun X k| := by
    calc
      (∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * mu X j)
          = (∑ j ∈ Finset.range k, ((-1 : ℝ) ^ j) * (lambda X) ^ j / ((j) ! : ℝ)) + errorBrun X k := by
            exact hdecomp
      _ ≥ eta (lambda X) k - |errorBrun X k| := by linarith [hsum_ge, herr_ge]
  have hpos : eta (lambda X) k - |errorBrun X k| > 0 := by
    linarith [herr]
  have hfrac : (deltaG X : ℝ) / (X : ℝ) > 0 :=
    lt_of_lt_of_le hpos (le_trans htotal hlower)
  have hdg_ne : deltaG X ≠ 0 := by
    intro hz
    have hz' : (deltaG X : ℝ) = 0 := by exact_mod_cast hz
    rw [hz'] at hfrac
    simp [zero_div] at hfrac
  exact Nat.pos_of_ne_zero hdg_ne

/-- `HA_Brun` forces infinitely many `n` with `gcd (a n) (L n) = 1`. -/
theorem HA_Brun_implies_infinite (h : HA_Brun) :
    Set.Infinite { n : ℕ | Nat.gcd (a n) (L n) = 1 } := by
  have hsub : { X : ℕ | BrunHoldsAt X } ⊆ { X : ℕ | 0 < deltaG X } := by
    intro X hX
    exact brunHoldsAt_implies_deltaG_pos X hX
  have hw : HA_shell_weak := Set.Infinite.mono hsub h
  exact HA_shell_weak_iff_infinite.mp hw

end Erdos291
