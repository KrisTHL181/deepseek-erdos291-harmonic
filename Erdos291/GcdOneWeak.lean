import Erdos291.GcdOne

/-!
# Erdős #291 — the `gcd = 1` direction under `S x = o(log x)`

This file records a *weakening* of the arithmetic hypothesis used in `GcdOne.lean`.  There the
conclusion `gcd (a n) (L n) = 1` for infinitely many `n` is derived from `HA_dist` (a distribution
estimate on the bad digits) together with `HA_arith`, the bound `∑_{p ≤ x} c p = O(log log x)`.
Here we show that the *much weaker* hypothesis

  `S x := ∑_{p ≤ x} c p = o(log x)`

already suffices.  The point is elementary: for every prime `p` one has `0 ≤ c p ≤ 1 / 2`, so
`log (1 - c p) ≥ -2 c p` (see `GcdOne.log_one_sub_ge_neg_two_mul`).  Summing and exponentiating
gives

  `∏_{p ≤ x} (1 - c p) ≥ exp (-2 S x)`,

and therefore

  `x · ∏_{p ≤ x} (1 - c p) ≥ x · exp (-2 S x) = exp (log x - 2 S x) → ∞`,

because `log x - 2 S x = log x · (1 - 2 · S x / log x) → ∞` under `S x / log x → 0`.

The rest of the argument (passing from a `→ ∞` lower bound on `x · ∏ (1 - c p)` to the infinite set
of good `n`) is shared with `GcdOne.lean`; the only difference is that we key it to
`x · ∏ (1 - c p) → ∞` rather than to the quantitative `K / (log x)^M` bound.

There are no unproved declarations in this file.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-- The sum of the bad-digit densities over primes `p ≤ x`. -/
noncomputable def S (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (c p : ℝ)

/-- The weakened arithmetic hypothesis: `S x = o(log x)`. -/
def HA_arith_weak : Prop :=
  Tendsto (fun x : ℕ => S x / Real.log (x : ℝ)) atTop (𝓝 0)

/-- The elementary product bound: `∏_{p ≤ x} (1 - c p) ≥ exp (-2 · S x)`, obtained by summing
`log (1 - c p) ≥ -2 c p` over the primes `p ≤ x` and exponentiating. -/
lemma exp_neg_two_mul_S_le_prod (x : ℕ) :
    Real.exp (-2 * S x) ≤
      ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
  have hlog_elem : ∀ p ∈ (Finset.Icc 2 x).filter Nat.Prime,
      -2 * (c p : ℝ) ≤ Real.log (1 - (c p : ℝ)) := by
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    exact log_one_sub_ge_neg_two_mul (c_nonneg p) (c_le_one_half p hpP)
  have hsum_le : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, -2 * (c p : ℝ)) ≤
      ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, Real.log (1 - (c p : ℝ)) :=
    Finset.sum_le_sum hlog_elem
  have hsum_eq : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, -2 * (c p : ℝ)) = -2 * S x := by
    unfold S
    rw [← Finset.mul_sum]
  have hne : ∀ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) ≠ 0 := by
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hlt : (c p : ℝ) < 1 := c_lt_one p hp2
    linarith
  have hlog_prod : (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, Real.log (1 - (c p : ℝ))) =
      Real.log (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) :=
    (Real.log_prod hne).symm
  have hmain : -2 * S x ≤
      Real.log (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) := by
    calc
      -2 * S x = ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, -2 * (c p : ℝ) := hsum_eq.symm
      _ ≤ ∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, Real.log (1 - (c p : ℝ)) := hsum_le
      _ = Real.log (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) := hlog_prod
  have hpos_prod : 0 < ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
    refine Finset.prod_pos ?_
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hlt : (c p : ℝ) < 1 := c_lt_one p hp2
    linarith
  calc
    Real.exp (-2 * S x) ≤
        Real.exp (Real.log (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)))) :=
      Real.exp_le_exp.mpr hmain
    _ = ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) :=
      Real.exp_log hpos_prod

/-- `log x - 2 · S x → ∞` along `ℕ`, provided `S x = o(log x)`. -/
lemma log_sub_two_mul_S_tendsto_atTop (hS : HA_arith_weak) :
    Tendsto (fun x : ℕ => Real.log (x : ℝ) - 2 * S x) atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h2S : Tendsto (fun x : ℕ => 2 * (S x / Real.log (x : ℝ))) atTop (𝓝 0) := by
    simpa using hS.const_mul (2 : ℝ)
  have hone : Tendsto (fun x : ℕ => 1 - 2 * (S x / Real.log (x : ℝ))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub h2S
  have hone_ge : ∀ᶠ x : ℕ in atTop, (1 / 2 : ℝ) ≤ 1 - 2 * (S x / Real.log (x : ℝ)) := by
    have hgt : ∀ᶠ x : ℕ in atTop, (1 / 2 : ℝ) < 1 - 2 * (S x / Real.log (x : ℝ)) :=
      (tendsto_order.1 hone).1 (1 / 2) (by norm_num)
    filter_upwards [hgt] with x hx
    exact hx.le
  have hlog_nonneg : ∀ᶠ x : ℕ in atTop, 0 ≤ Real.log (x : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    exact (Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ))).le
  have hlower : ∀ᶠ x : ℕ in atTop, (1 / 2 : ℝ) * Real.log (x : ℝ) ≤
      (1 - 2 * (S x / Real.log (x : ℝ))) * Real.log (x : ℝ) := by
    filter_upwards [hlog_nonneg, hone_ge] with x hlog₀ hge
    exact mul_le_mul_of_nonneg_right hge hlog₀
  have hlog_half : Tendsto (fun x : ℕ => (1 / 2 : ℝ) * Real.log (x : ℝ)) atTop atTop :=
    hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hdiff_factor : Tendsto
      (fun x : ℕ => (1 - 2 * (S x / Real.log (x : ℝ))) * Real.log (x : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hlower hlog_half
  have hdiff_eq : ∀ᶠ x : ℕ in atTop,
      (1 - 2 * (S x / Real.log (x : ℝ))) * Real.log (x : ℝ) = Real.log (x : ℝ) - 2 * S x := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hlogne : Real.log (x : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hx : (1 : ℝ) < (x : ℝ)))
    field_simp [hlogne]
  exact hdiff_factor.congr' hdiff_eq

/-- `x · ∏_{p ≤ x} (1 - c p) → ∞` provided `S x = o(log x)`. -/
theorem x_mul_prod_tendsto_atTop (hS : HA_arith_weak) :
    Tendsto (fun x : ℕ =>
      (x : ℝ) * ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) atTop atTop := by
  have hdiff : Tendsto (fun x : ℕ => Real.log (x : ℝ) - 2 * S x) atTop atTop :=
    log_sub_two_mul_S_tendsto_atTop hS
  have hexp : Tendsto (fun x : ℕ => Real.exp (Real.log (x : ℝ) - 2 * S x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hdiff
  have hexp_eq : ∀ᶠ x : ℕ in atTop,
      Real.exp (Real.log (x : ℝ) - 2 * S x) = (x : ℝ) * Real.exp (-2 * S x) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with x hx
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast hx
    calc
      Real.exp (Real.log (x : ℝ) - 2 * S x)
          = Real.exp (Real.log (x : ℝ)) / Real.exp (2 * S x) := by rw [Real.exp_sub]
      _ = (x : ℝ) / Real.exp (2 * S x) := by rw [Real.exp_log hxpos]
      _ = (x : ℝ) * (Real.exp (2 * S x))⁻¹ := by rw [div_eq_mul_inv]
      _ = (x : ℝ) * Real.exp (-2 * S x) := by
          rw [← Real.exp_neg, show -(2 * S x) = -2 * S x by ring]
  have hxexp : Tendsto (fun x : ℕ => (x : ℝ) * Real.exp (-2 * S x)) atTop atTop :=
    hexp.congr' hexp_eq
  have hprod_ge : ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Real.exp (-2 * S x) ≤
        (x : ℝ) * ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
    filter_upwards [] with x
    exact mul_le_mul_of_nonneg_left (exp_neg_two_mul_S_le_prod x) (Nat.cast_nonneg x)
  exact tendsto_atTop_mono' atTop hprod_ge hxexp

/-- `HA_dist` together with `x · ∏_{p ≤ x} (1 - c p) → ∞` forces `G x` to be eventually at least
every constant (and hence the good set to be infinite). -/
lemma G_tendsto_atTop_of_x_mul_prod (hdist : HA_dist)
    (hxP : Tendsto (fun x : ℕ =>
      (x : ℝ) * ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) atTop atTop) :
    ∀ C : ℕ, ∀ᶠ x in atTop, C ≤ G x := by
  intro C
  rcases hdist with ⟨ε, hε0, hdist_ineq⟩
  have hεsmall : ∀ᶠ x : ℕ in atTop, ε x ≤ 1 / 2 := by
    have hlt : ∀ᶠ x : ℕ in atTop, ε x < 1 / 2 :=
      (tendsto_order.1 hε0).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hlt] with x hx
    exact hx.le
  have hxP_ge : ∀ᶠ x : ℕ in atTop, (2 : ℝ) * (C : ℝ) ≤
      (x : ℝ) * ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) :=
    hxP.eventually_ge_atTop ((2 : ℝ) * (C : ℝ))
  filter_upwards [hdist_ineq, hxP_ge, hεsmall, eventually_gt_atTop (1 : ℕ)] with
    x hdistx hxPx hεx hxgt
  have hprod_nonneg : 0 ≤ ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hcp : (c p : ℝ) ≤ 1 / 2 := c_le_one_half p hpP
    linarith
  have hx_nonneg : 0 ≤ (x : ℝ) := Nat.cast_nonneg _
  have hinner : (1 / 2 : ℝ) * (x : ℝ) ≤ (1 - ε x) * (x : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [hεx] : (1 / 2 : ℝ) ≤ 1 - ε x) hx_nonneg
  have hlower : (1 / 2 : ℝ) * (x : ℝ) *
        ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) ≤
      (1 - ε x) * (x : ℝ) *
        ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) :=
    mul_le_mul_of_nonneg_right hinner hprod_nonneg
  have hmain : (C : ℝ) ≤ (G x : ℝ) := by
    calc
      (C : ℝ) = (1 / 2 : ℝ) * (2 * (C : ℝ)) := by ring
      _ ≤ (1 / 2 : ℝ) *
            ((x : ℝ) * ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) :=
        mul_le_mul_of_nonneg_left hxPx (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = (1 / 2 : ℝ) * (x : ℝ) *
            ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by ring
      _ ≤ (1 - ε x) * (x : ℝ) *
            ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := hlower
      _ ≤ (G x : ℝ) := hdistx
  exact_mod_cast hmain

/-- `HA_dist` together with the weakened arithmetic hypothesis `S x = o(log x)` imply that
`gcd (a n) (L n) = 1` for infinitely many `n`. -/
theorem gcd_eq_one_infinite_of_S_o_log (hdist : HA_dist) (hS : HA_arith_weak) :
    Set.Infinite { n : ℕ | Nat.gcd (a n) (L n) = 1 } := by
  rw [← infinite_good_iff_G_tendsto]
  exact G_tendsto_atTop_of_x_mul_prod hdist (x_mul_prod_tendsto_atTop hS)

end Erdos291
