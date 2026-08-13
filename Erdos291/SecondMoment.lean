import Erdos291.GcdOneWeak
import Erdos291.MertensUpper
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD

/-!
# Erdős #291 — the second-moment reduction for `HA_arith`

This file formalizes the *single sound reduction* of the arithmetic hypothesis
`HA_arith` that the multi-agent search established: `HA_arith` is *implied by* the
second factorial-moment bound

  `M x := Σ_{p ≤ x} f_p (f_p - 1) / (p - 1) = O(log log x)`,

where `f_p = |E p|` is the number of "bad" residues modulo the prime `p`.

The reduction is elementary.  Writing `c p = f_p / (p - 1)`, the identity
`f_p ≤ 1 + f_p (f_p - 1)` (equivalently `(f_p - 1)² ≥ 0`) gives, after dividing by
`p - 1 > 0`,

  `c p ≤ 1 / (p - 1) + f_p (f_p - 1) / (p - 1)`.

Summing over the primes `p ≤ x` and applying Mertens' bound `Σ_{p ≤ x} 1/(p-1) =
O(log log x)` (here bridged from `MertensUpper.sum_one_div_primes_le_loglog`) gives

  `S x ≤ O(log log x) + M x`,

so `HA_second_moment` (the bound on `M x`) implies `HA_arith` (the bound on `S x`).

We also record the *structural* lemma that makes the second moment the correct
obstruction to control: for any two rationals `x, y` written in lowest terms, the
gcd of their numerators divides the numerator of their difference.  Specialized to
harmonic numbers this is the key fact behind the pair-counting obstruction
`gcd (num H_r, num H_s) ∣ num (H_r - H_s)`.

There are no unproved declarations in this file.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-! ## The second factorial moment and the elementary pointwise bound -/

/-- The second factorial moment `M x = Σ_{p ≤ x} f_p (f_p - 1) / (p - 1)`, where
`f_p = |E p|` counts the bad residues modulo the prime `p`. -/
noncomputable def M (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
    ((E p).card : ℝ) * (((E p).card : ℝ) - 1) / ((p - 1 : ℕ) : ℝ)

/-- The second-moment hypothesis: `M x = O(log log x)`. -/
def HA_second_moment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
    M x ≤ C * (1 + Real.log (Real.log (x : ℝ)))

/-- The elementary inequality `f_p ≤ 1 + f_p (f_p - 1)`, i.e. `(f_p - 1)² ≥ 0`. -/
lemma card_le_one_add_card_mul_pred_card (p : ℕ) :
    ((E p).card : ℝ) ≤ 1 + ((E p).card : ℝ) * (((E p).card : ℝ) - 1) := by
  have hsq : 0 ≤ (((E p).card : ℝ) - 1) ^ 2 := sq_nonneg _
  nlinarith

/-- Pointwise reduction: for a prime `p`, `c p ≤ 1/(p-1) + f_p (f_p - 1) / (p-1)`. -/
lemma c_le_inv_pred_add_second_moment_term (p : ℕ) (hp : Nat.Prime p) :
    (c p : ℝ) ≤ (1 / ((p - 1 : ℕ) : ℝ)) +
      ((E p).card : ℝ) * (((E p).card : ℝ) - 1) / ((p - 1 : ℕ) : ℝ) := by
  have hq : 0 < ((p - 1 : ℕ) : ℝ) := by
    have hp2 : 2 ≤ p := hp.two_le
    have : 0 < p - 1 := by omega
    exact_mod_cast this
  have hf : ((E p).card : ℝ) ≤ 1 + ((E p).card : ℝ) * (((E p).card : ℝ) - 1) :=
    card_le_one_add_card_mul_pred_card p
  have hc : (c p : ℝ) = ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    unfold c
    rw [Rat.cast_div]
    norm_num
    rw [Nat.cast_sub (by have hp2 : 2 ≤ p := hp.two_le; omega : (1 : ℕ) ≤ p)]
    norm_num
  have hdiv : ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
      (1 + ((E p).card : ℝ) * (((E p).card : ℝ) - 1)) / ((p - 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hf (le_of_lt hq)
  have hsplit : (1 + ((E p).card : ℝ) * (((E p).card : ℝ) - 1)) / ((p - 1 : ℕ) : ℝ)
      = (1 / ((p - 1 : ℕ) : ℝ)) +
        ((E p).card : ℝ) * (((E p).card : ℝ) - 1) / ((p - 1 : ℕ) : ℝ) := by
    rw [add_div]
  calc
    (c p : ℝ) = ((E p).card : ℝ) / ((p - 1 : ℕ) : ℝ) := hc
    _ ≤ (1 + ((E p).card : ℝ) * (((E p).card : ℝ) - 1)) / ((p - 1 : ℕ) : ℝ) := hdiv
    _ = (1 / ((p - 1 : ℕ) : ℝ)) +
        ((E p).card : ℝ) * (((E p).card : ℝ) - 1) / ((p - 1 : ℕ) : ℝ) := hsplit

/-! ## The Mertens bridge: `Σ_{p ≤ x} 1/(p - 1) = O(log log x)` -/

/-- `1/(p - 1) ≤ 2/p` for `p ≥ 2`. -/
lemma one_div_pred_le_two_div (p : ℕ) (hp : 2 ≤ p) :
    (1 / ((p - 1 : ℕ) : ℝ)) ≤ 2 / (p : ℝ) := by
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hp)
  have hpp : 0 < ((p - 1 : ℕ) : ℝ) := by
    have : 0 < p - 1 := by omega
    exact_mod_cast this
  have hineq : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by
    have hineq_nat : p ≤ 2 * (p - 1) := by omega
    exact_mod_cast hineq_nat
  rw [div_le_div_iff₀ hpp hp_pos]
  simpa using hineq

/-- `Σ_{p ≤ x} 1/(p - 1) ≤ 2 · Σ_{p ≤ x} 1/p`. -/
lemma sum_inv_pred_le_two_mul_sum_inv (x : ℕ) :
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
      ≤ 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / (p : ℝ))) := by
  calc
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (2 / (p : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
          exact one_div_pred_le_two_div p hp2
    _ = 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / (p : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring

/-- `Σ_{p ≤ x} 1/p ≤ Σ_{p < x + 1} 1/p`. -/
lemma sum_inv_le_sum_inv_primesBelow (x : ℕ) :
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / (p : ℝ)))
      ≤ ∑ p ∈ Nat.primesBelow (x + 1), (1 / (p : ℝ)) := by
  have hsub : (Finset.Icc 2 x).filter Nat.Prime ⊆ Nat.primesBelow (x + 1) := by
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hle : p ≤ x := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    rw [Nat.mem_primesBelow]
    exact ⟨Nat.lt_succ_of_le hle, hpP⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by intro p _ _; exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg p))

/-- The log-log shift: `1 + log log (x+1) ≤ 2 (1 + log log x)` for `x ≥ 3`. -/
lemma one_add_loglog_succ_le_two_mul_one_add_loglog {x : ℕ} (hx : 3 ≤ x) :
    1 + Real.log (Real.log ((x + 1 : ℕ) : ℝ)) ≤
      2 * (1 + Real.log (Real.log (x : ℝ))) := by
  have hx3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx1 : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1 : ℕ) < 3) hx)
  have hxpos : 0 < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 3) hx)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  -- log(x+1) ≤ log(2x) = log 2 + log x
  have hle1 : Real.log ((x + 1 : ℕ) : ℝ) ≤ Real.log (2 * (x : ℝ)) := by
    have hcast : ((x + 1 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by
      have hle : (x + 1 : ℕ) ≤ 2 * x := by omega
      exact_mod_cast hle
    exact Real.log_le_log (by positivity : 0 < ((x + 1 : ℕ) : ℝ)) hcast
  have hlog2x : Real.log (2 * (x : ℝ)) = Real.log 2 + Real.log (x : ℝ) :=
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hxpos.ne'
  have hlog2_le_logx : Real.log 2 ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by exact_mod_cast (by omega : 2 ≤ x) : (2 : ℝ) ≤ (x : ℝ))
  have hle2 : Real.log (2 * (x : ℝ)) ≤ 2 * Real.log (x : ℝ) := by
    rw [hlog2x]
    nlinarith [hlog2_le_logx]
  have hll : Real.log (Real.log ((x + 1 : ℕ) : ℝ)) ≤ Real.log (2 * Real.log (x : ℝ)) := by
    have hpos1 : 0 < Real.log ((x + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < x + 1))
    exact Real.log_le_log hpos1 (le_trans hle1 hle2)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hll_bound : Real.log (Real.log ((x + 1 : ℕ) : ℝ)) ≤ 1 + Real.log (Real.log (x : ℝ)) := by
    have h : Real.log (2 * Real.log (x : ℝ)) = Real.log 2 + Real.log (Real.log (x : ℝ)) :=
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogx_pos.ne'
    nlinarith [hll, h, hlog2le1]
  have hll_nonneg : 0 ≤ Real.log (Real.log (x : ℝ)) := by
    have h3e : (3 : ℝ) > Real.exp 1 := by
      have h := Real.exp_lt_two_add_div_two_sub (by norm_num : (0 : ℝ) < 1)
        (by norm_num : (1 : ℝ) < 2)
      norm_num at h
      exact h
    have hlogx_gt_one : (1 : ℝ) < Real.log (x : ℝ) := by
      rw [Real.lt_log_iff_exp_lt hxpos]
      exact lt_of_lt_of_le h3e hx3
    exact le_of_lt (Real.log_pos hlogx_gt_one)
  nlinarith [hll_bound, hll_nonneg]

/-- Mertens' upper bound in the form needed here: `Σ_{p ≤ x} 1/(p - 1) = O(log log x)`. -/
theorem sum_inv_pred_le_loglog :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
        ≤ C * (1 + Real.log (Real.log (x : ℝ))) := by
  rcases sum_one_div_primes_le_loglog with ⟨C₀, hC₀⟩
  have hC0pos : 0 < C₀ := by
    have h3e : (3 : ℝ) > Real.exp 1 := by
      have h := Real.exp_lt_two_add_div_two_sub (by norm_num : (0 : ℝ) < 1)
        (by norm_num : (1 : ℝ) < 2)
      norm_num at h
      exact h
    have hlog3 : (1 : ℝ) < Real.log (3 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
      exact h3e
    have hll3 : 0 < Real.log (Real.log (3 : ℝ)) := Real.log_pos hlog3
    have hfac : 0 < (1 + Real.log (Real.log (3 : ℝ))) := by linarith [hll3]
    have hsum : 0 < (∑ p ∈ Nat.primesBelow 3, (1 / (p : ℝ))) := by
      have h2mem : (2 : ℕ) ∈ Nat.primesBelow 3 := by
        rw [Nat.mem_primesBelow]
        exact ⟨by norm_num, by decide⟩
      have hnonneg : ∀ p ∈ Nat.primesBelow 3, 0 ≤ (1 / (p : ℝ)) := by
        intro p _
        exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg p)
      have hterm : (0 : ℝ) < (1 / (2 : ℝ)) := by norm_num
      exact lt_of_lt_of_le hterm (Finset.single_le_sum hnonneg h2mem)
    have h3 := hC₀ 3 (by norm_num : 3 ≤ 3)
    have hlt : 0 < C₀ * (1 + Real.log (Real.log (3 : ℝ))) := lt_of_lt_of_le hsum h3
    exact pos_of_mul_pos_left hlt (le_of_lt hfac)
  refine ⟨4 * C₀, by positivity, ?_⟩
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with x hx
    have hx1 : 3 ≤ x + 1 := by omega
    have hmert := hC₀ (x + 1) hx1
    have hC0nonneg : 0 ≤ C₀ := le_of_lt hC0pos
    calc
      (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ)))
          ≤ 2 * (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / (p : ℝ))) :=
            sum_inv_pred_le_two_mul_sum_inv x
      _ ≤ 2 * (∑ p ∈ Nat.primesBelow (x + 1), (1 / (p : ℝ))) := by
            exact mul_le_mul_of_nonneg_left (sum_inv_le_sum_inv_primesBelow x)
              (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ 2 * (C₀ * (1 + Real.log (Real.log ((x + 1 : ℕ) : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left hmert (by norm_num : (0 : ℝ) ≤ 2)
      _ ≤ 4 * C₀ * (1 + Real.log (Real.log (x : ℝ))) := by
            have hloglog := one_add_loglog_succ_le_two_mul_one_add_loglog hx
            have h2C0 : 0 ≤ 2 * C₀ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC0nonneg
            calc
              2 * (C₀ * (1 + Real.log (Real.log ((x + 1 : ℕ) : ℝ))))
                  = (2 * C₀) * (1 + Real.log (Real.log ((x + 1 : ℕ) : ℝ))) := by ring
              _ ≤ (2 * C₀) * (2 * (1 + Real.log (Real.log (x : ℝ)))) :=
                    mul_le_mul_of_nonneg_left hloglog h2C0
              _ = 4 * C₀ * (1 + Real.log (Real.log (x : ℝ))) := by ring

/-! ## Assembling the reduction `HA_second_moment → HA_arith` -/

/-- `S x ≤ Σ_{p ≤ x} 1/(p-1) + M x`. -/
lemma S_le_sum_inv_pred_add_M (x : ℕ) :
    S x ≤ (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) + M x := by
  unfold S M
  calc
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (c p : ℝ))
        ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
            ((1 / ((p - 1 : ℕ) : ℝ)) +
              ((E p).card : ℝ) * (((E p).card : ℝ) - 1) / ((p - 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          exact c_le_inv_pred_add_second_moment_term p (Finset.mem_filter.mp hp).2
    _ = (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) +
        (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
          ((E p).card : ℝ) * (((E p).card : ℝ) - 1) / ((p - 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_add_distrib]

/-- The main reduction: the second-moment bound `M x = O(log log x)` implies `HA_arith`. -/
theorem HA_arith_of_HA_second_moment (hM : HA_second_moment) : HA_arith := by
  rcases hM with ⟨C₂, hC2pos, hM⟩
  rcases sum_inv_pred_le_loglog with ⟨C₁, hC1pos, hC₁⟩
  have hll_tendsto : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hll_ge : ∀ᶠ x : ℕ in atTop, 1 ≤ Real.log (Real.log (x : ℝ)) :=
    (hll_tendsto.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 : ℝ)
  refine ⟨2 * (C₁ + C₂), by positivity, ?_⟩
  filter_upwards [hC₁, hM, hll_ge] with x hC1x hMx hllx
  calc
    S x ≤ (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 / ((p - 1 : ℕ) : ℝ))) + M x :=
        S_le_sum_inv_pred_add_M x
    _ ≤ C₁ * (1 + Real.log (Real.log (x : ℝ))) + C₂ * (1 + Real.log (Real.log (x : ℝ))) :=
        add_le_add hC1x hMx
    _ = (C₁ + C₂) * (1 + Real.log (Real.log (x : ℝ))) := by ring
    _ ≤ 2 * (C₁ + C₂) * Real.log (Real.log (x : ℝ)) := by
        have hCnonneg : 0 ≤ C₁ + C₂ := add_nonneg (le_of_lt hC1pos) (le_of_lt hC2pos)
        have hfac : 1 + Real.log (Real.log (x : ℝ)) ≤ 2 * Real.log (Real.log (x : ℝ)) := by
          nlinarith [hllx]
        have hmul : (C₁ + C₂) * (1 + Real.log (Real.log (x : ℝ))) ≤
            (C₁ + C₂) * (2 * Real.log (Real.log (x : ℝ))) :=
          mul_le_mul_of_nonneg_left hfac hCnonneg
        have h2 : (C₁ + C₂) * (2 * Real.log (Real.log (x : ℝ))) =
            2 * (C₁ + C₂) * Real.log (Real.log (x : ℝ)) := by ring
        exact h2 ▸ hmul

/-! ## The structural lemma: `gcd(num x, num y) ∣ num(x - y)` -/

/-- For rationals `x, y` written in lowest terms, the gcd of the numerators divides the
numerator of `x - y`. -/
theorem gcd_num_sub_dvd (x y : ℚ) :
    (Int.gcd x.num y.num : ℤ) ∣ (x - y).num := by
  let g : ℕ := Int.gcd x.num y.num
  change (g : ℤ) ∣ (x - y).num
  have hsub := Rat.substr_num_den' x y
  -- hsub : (x - y).num * ↑x.den * ↑y.den = (x.num * ↑y.den - y.num * ↑x.den) * ↑(x - y).den
  -- 1. (g : ℤ) | x.num and (g : ℤ) | y.num
  have hgx : (g : ℤ) ∣ x.num := by
    have hnat : g ∣ x.num.natAbs := by
      dsimp [g]
      rw [Int.gcd_def]
      exact Nat.gcd_dvd_left x.num.natAbs y.num.natAbs
    exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hnat)
  have hgy : (g : ℤ) ∣ y.num := by
    have hnat : g ∣ y.num.natAbs := by
      dsimp [g]
      rw [Int.gcd_def]
      exact Nat.gcd_dvd_right x.num.natAbs y.num.natAbs
    exact Int.dvd_natAbs.1 (Int.natCast_dvd_natCast.2 hnat)
  -- 2. (g : ℤ) | x.num * (y.den : ℤ) - y.num * (x.den : ℤ)
  have hN : (g : ℤ) ∣ x.num * (y.den : ℤ) - y.num * (x.den : ℤ) :=
    Int.dvd_sub (dvd_mul_of_dvd_left hgx (y.den : ℤ)) (dvd_mul_of_dvd_left hgy (x.den : ℤ))
  -- 3. (g : ℤ) | (x - y).num * (x.den : ℤ) * (y.den : ℤ)
  have hNmul : (g : ℤ) ∣ (x.num * (y.den : ℤ) - y.num * (x.den : ℤ)) * (x - y).den :=
    dvd_mul_of_dvd_left hN (x - y).den
  have hnum_den : (g : ℤ) ∣ (x - y).num * (x.den : ℤ) * (y.den : ℤ) := by
    rw [← hsub] at hNmul
    exact hNmul
  -- 4. cancel y.den, then x.den, using coprimality
  have hg_cop_d : Nat.Coprime g y.den := by
    dsimp [g]
    rw [Int.gcd_def]
    exact Nat.Coprime.of_dvd_left (Nat.gcd_dvd_right x.num.natAbs y.num.natAbs) y.reduced
  have hgcd_d : Int.gcd (g : ℤ) (y.den : ℤ) = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hg_cop_d.gcd_eq_one
  have hnum_x : (g : ℤ) ∣ (x - y).num * (x.den : ℤ) :=
    Int.dvd_of_dvd_mul_left_of_gcd_one hnum_den hgcd_d
  have hg_cop_b : Nat.Coprime g x.den := by
    dsimp [g]
    rw [Int.gcd_def]
    exact Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left x.num.natAbs y.num.natAbs) x.reduced
  have hgcd_b : Int.gcd (g : ℤ) (x.den : ℤ) = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact hg_cop_b.gcd_eq_one
  exact Int.dvd_of_dvd_mul_left_of_gcd_one hnum_x hgcd_b

/-- Specialized to harmonic numbers: `gcd(num H_r, num H_s)` divides the numerator of
`H_r - H_s`. -/
theorem harmonic_sub_num_gcd_dvd (r s : ℕ) :
    (Int.gcd (harmonic r).num (harmonic s).num : ℤ) ∣ (harmonic r - harmonic s).num :=
  gcd_num_sub_dvd (harmonic r) (harmonic s)

end Erdos291
