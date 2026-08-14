import Erdos291.GcdOneWeak
import Erdos291.GcdOne

/-!
# The product `x · P(x)` and its unboundedness reductions

Let `P x = ∏_{p ≤ x, p prime} (1 - c p)`.  The goal `x · P x` is unbounded is
strictly weaker than the arithmetic hypotheses already present in the repository.
This file records the two reductions:

* `HA_arith ⟹ x · P x → ∞`
* `HA_arith_weak ⟹ x · P x → ∞`

Both are already implicit in `GcdOne.prod_one_sub_c_ge` and
`GcdOneWeak.x_mul_prod_tendsto_atTop`; here we give the product a name and state
the unboundedness formulation explicitly.

The unconditional proof of unboundedness itself is not attempted in this file.
-/

open scoped BigOperators Topology
open Filter

namespace Erdos291

/-- The product of `1 - c p` over primes `p ≤ x`. -/
noncomputable def prodOneSub (x : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))

/-- The target: `x · P x` is unbounded, i.e. it eventually exceeds every constant somewhere. -/
def HA_prod_unbounded : Prop :=
  ∀ C : ℕ, ∃ x : ℕ, (C : ℝ) ≤ (x : ℝ) * prodOneSub x

/-- A sequence tending to `atTop` is unbounded in the weak sense used here. -/
lemma unbounded_of_tendsto_atTop {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    ∀ C : ℕ, ∃ x : ℕ, (C : ℝ) ≤ f x := by
  intro C
  rcases (hf.eventually_ge_atTop (C : ℝ)).exists with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Under `HA_arith`, the product `P x` has a power-of-log lower bound, hence
`x · P x → ∞`.  This is the natural-language proof:
`HA_arith` gives `P x ≥ K · (log x)^(-M)`; multiplying by `x` gives
`x·P x ≥ K·x/(log x)^M → ∞`. -/
theorem xP_tendsto_atTop_of_HA_arith (harith : HA_arith) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  rcases prod_one_sub_c_ge harith with ⟨K, M, hKpos, hMpos, hprod⟩
  have hbase : Tendsto (fun x : ℕ => (x : ℝ) / (Real.log (x : ℝ)) ^ M) atTop atTop :=
    tendsto_div_log_pow_atTop M hMpos
  have hKbase : Tendsto (fun x : ℕ => K * ((x : ℝ) / (Real.log (x : ℝ)) ^ M)) atTop atTop :=
    hbase.const_mul_atTop hKpos
  have hmono : ∀ᶠ x : ℕ in atTop,
      K * ((x : ℝ) / (Real.log (x : ℝ)) ^ M) ≤ (x : ℝ) * prodOneSub x := by
    filter_upwards [hprod, eventually_gt_atTop (1 : ℕ)] with x hpx hxgt
    have hlogpos : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hxgt : (1 : ℝ) < (x : ℝ))
    have hprod' : K / (Real.log (x : ℝ)) ^ M ≤ prodOneSub x := by
      simpa [prodOneSub, div_eq_mul_inv, Real.rpow_neg (le_of_lt hlogpos) M] using hpx
    have hxnonneg : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
    calc
      K * ((x : ℝ) / (Real.log (x : ℝ)) ^ M)
          = (x : ℝ) * (K / (Real.log (x : ℝ)) ^ M) := by ring
      _ ≤ (x : ℝ) * prodOneSub x := mul_le_mul_of_nonneg_left hprod' hxnonneg
  exact tendsto_atTop_mono' atTop hmono hKbase

/-- Under `HA_arith`, `x · P x` is unbounded. -/
theorem HA_prod_unbounded_of_HA_arith (harith : HA_arith) : HA_prod_unbounded := by
  unfold HA_prod_unbounded
  exact unbounded_of_tendsto_atTop (xP_tendsto_atTop_of_HA_arith harith)

/-- Under the weaker arithmetic hypothesis `S x = o(log x)`, the existing lemma
`GcdOneWeak.x_mul_prod_tendsto_atTop` already proves `x · P x → ∞`. -/
theorem xP_tendsto_atTop_of_HA_arith_weak (hS : HA_arith_weak) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  simpa [prodOneSub] using x_mul_prod_tendsto_atTop hS

/-- Under `HA_arith_weak`, `x · P x` is unbounded. -/
theorem HA_prod_unbounded_of_HA_arith_weak (hS : HA_arith_weak) : HA_prod_unbounded := by
  unfold HA_prod_unbounded
  exact unbounded_of_tendsto_atTop (xP_tendsto_atTop_of_HA_arith_weak hS)


/-- A strictly weaker sufficient condition: if eventually `S x ≤ c · log x` for some
constant `c < 1/2`, then `x · P x → ∞`.  Indeed `P x ≥ exp(-2 S x)`, so
`x · P x ≥ x · exp(-2 c log x) = x ^ (1 - 2c)`, and `1 - 2c > 0`. -/
theorem xP_tendsto_atTop_of_S_le_const_mul_log
    (h : ∃ c : ℝ, c < 1 / 2 ∧ ∀ᶠ x : ℕ in atTop, S x ≤ c * Real.log (x : ℝ)) :
    Tendsto (fun x : ℕ => (x : ℝ) * prodOneSub x) atTop atTop := by
  rcases h with ⟨c, hc, hS⟩
  have hexp_pos : 0 < 1 - 2 * c := by linarith
  have hbase : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 - 2 * c)) atTop atTop :=
    (tendsto_rpow_atTop hexp_pos).comp tendsto_natCast_atTop_atTop
  have hmono : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) ^ (1 - 2 * c) ≤ (x : ℝ) * prodOneSub x := by
    filter_upwards [hS, eventually_gt_atTop (0 : ℕ)] with x hSx hxgt
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast hxgt
    have hS2' : 2 * S x ≤ 2 * (c * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hSx (by norm_num : 0 ≤ (2 : ℝ))
    have hS2 : 2 * S x ≤ (2 * c) * Real.log (x : ℝ) := by
      simpa [mul_assoc] using hS2' 
    have hneg : -(2 * c) * Real.log (x : ℝ) ≤ -2 * S x := by linarith
    have hexp_le : Real.exp (-(2 * c) * Real.log (x : ℝ)) ≤ prodOneSub x :=
      (Real.exp_le_exp.mpr hneg).trans (exp_neg_two_mul_S_le_prod x)
    have hid : (x : ℝ) ^ (1 - 2 * c) =
        (x : ℝ) * Real.exp (-(2 * c) * Real.log (x : ℝ)) := by
      rw [Real.rpow_def_of_pos hxpos]
      rw [show Real.log (x : ℝ) * (1 - 2 * c) =
          Real.log (x : ℝ) + (-(2 * c)) * Real.log (x : ℝ) by ring]
      rw [Real.exp_add, Real.exp_log hxpos]
    calc
      (x : ℝ) ^ (1 - 2 * c) = (x : ℝ) * Real.exp (-(2 * c) * Real.log (x : ℝ)) := hid
      _ ≤ (x : ℝ) * prodOneSub x :=
        mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg x)
  exact tendsto_atTop_mono' atTop hmono hbase

/-- Under the sufficient condition `S x ≤ c log x` with `c < 1/2`, `x · P x` is unbounded. -/
theorem HA_prod_unbounded_of_S_le_const_mul_log
    (h : ∃ c : ℝ, c < 1 / 2 ∧ ∀ᶠ x : ℕ in atTop, S x ≤ c * Real.log (x : ℝ)) :
    HA_prod_unbounded := by
  unfold HA_prod_unbounded
  exact unbounded_of_tendsto_atTop (xP_tendsto_atTop_of_S_le_const_mul_log h)

end Erdos291

