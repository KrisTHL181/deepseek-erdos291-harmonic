import Erdos291.BadSet
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.Nat
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős #291 — the `gcd = 1` direction

The open Shiu (2016) conjecture asserts that `gcd(a_n, L_n) = 1` for infinitely many `n`.
This file sets up the two analytic hypotheses under which the conjecture is *known* to
hold (`HA_dist`, the distribution estimate on the bad digits, and `HA_arith`, the
estimate on their average density), and proves the conditional conclusion:

* `infinite_good_iff_G_tendsto`: infinitely many good `n` iff the count `G x` is
  eventually at least every constant.
* `gcd_eq_one_infinite`: under `HA_dist` and `HA_arith`, the good set is infinite.

There are no unproved declarations in this file.  The bound `c p ≤ 1 / 2` is proved
unconditionally for *every* prime `p` from the elementary "no two adjacent bad digits"
argument (`BadSet.E_card_le_half`): `E p` has no two consecutive elements, so its
`(p - 1) / 2` consecutive pairs `{1, 2}, {3, 4}, …` each hold at most one bad digit.  The
remaining content — the elementary bound `log(1 - t) ≥ -2t`, the product lower bound, and
the fact that `x / (log x)^M → ∞` — is fully proved.
-/

open scoped BigOperators
open scoped Topology

namespace Erdos291

open Filter

/-- The "distribution" hypothesis: the product of `(1 - c p)` over primes `p ≤ x` is
essentially `1`, so that a constant-proportion `(1 - ε x) · x` lower-bounds `G x`. -/
def HA_dist : Prop :=
  ∃ ε : ℕ → ℝ,
    Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ x in atTop,
        (1 - ε x) * (x : ℝ) *
          (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)))
          ≤ (G x : ℝ)

/-- The "arithmetic" hypothesis: the sum of the bad-digit densities over primes `p ≤ x`
grows at most like `log log x`. -/
def HA_arith : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
    (∑ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (c p : ℝ))
      ≤ C * Real.log (Real.log (x : ℝ))

/-- For every prime `p`, the bad-digit density `c p = |E p| / (p - 1)` is at most `1 / 2`.
This follows from the elementary "no two adjacent bad digits" argument: `E p` has no two
consecutive elements, so its `(p - 1) / 2` consecutive pairs `{1, 2}, {3, 4}, …` each hold
at most one bad digit (see `BadSet.E_card_le_half`). -/
theorem c_le_one_half (p : ℕ) (hp : Nat.Prime p) : (c p : ℝ) ≤ 1 / 2 := by
  by_cases hp2 : p = 2
  · rw [hp2]
    rw [c]
    have hE : (E 2).card = 0 := by native_decide
    rw [hE]
    norm_num
  · have hp_ge3 : 3 ≤ p := by
      have hgt : 2 < p := Nat.lt_of_le_of_ne hp.two_le (by intro h; exact hp2 h.symm)
      omega
    have hcard : (E p).card ≤ (p - 1) / 2 := @E_card_le_half p ⟨hp⟩ hp_ge3
    have h2card : 2 * (E p).card ≤ p - 1 := by
      have hmul : (p - 1) / 2 * 2 ≤ p - 1 := Nat.div_mul_le_self (p - 1) 2
      omega
    have hq : (c p : ℚ) ≤ 1 / 2 := by
      rw [c]
      have hden_pos : (0 : ℚ) < (p : ℚ) - 1 := by
        have hp' : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
        linarith
      rw [div_le_iff₀ hden_pos]
      have h2 : (2 : ℚ) * ((E p).card : ℚ) ≤ (p : ℚ) - 1 := by
        have h2cardq : ((2 * (E p).card : ℕ) : ℚ) ≤ ((p - 1 : ℕ) : ℚ) := by
          exact_mod_cast h2card
        have hsub : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ p)]
          norm_num
        rw [Nat.cast_mul, hsub] at h2cardq
        exact h2cardq
      nlinarith
    exact (Rat.cast_le.mpr hq).trans_eq (by norm_num)

/-- The bad-digit density `c p = |E p| / (p - 1)` is `≤ 1/2` for all sufficiently large
primes `p` (in fact for all primes). -/
theorem c_eventually_le_one_half : ∀ᶠ p in atTop, Nat.Prime p → (c p : ℝ) ≤ 1 / 2 := by
  filter_upwards [] with p
  exact c_le_one_half p

/-- `c p` is nonnegative for every `p` (including `p = 0, 1`, where `p - 1 = 0` and
`c p = 0`). -/
lemma c_nonneg (p : ℕ) : 0 ≤ (c p : ℝ) := by
  by_cases hp : p ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
    · rw [c]
      have hE : (E 0).card = 0 := by native_decide
      rw [hE]
      norm_num
    · rw [c]
      have hE : (E 1).card = 0 := by native_decide
      rw [hE]
      norm_num
  · have hp2 : 2 ≤ p := by omega
    have hq : (0 : ℚ) ≤ c p := by
      rw [c]
      have hden : (0 : ℚ) ≤ (p : ℚ) - 1 := by
        have hp' : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 1 < p)
        linarith
      exact div_nonneg (Nat.cast_nonneg (E p).card) hden
    exact_mod_cast hq

/-- For `p ≥ 2`, the bad-digit density `c p` is strictly less than `1`: the digit `1` is
never bad, so `|E p| ≤ p - 2 < p - 1`. -/
lemma c_lt_one (p : ℕ) (hp : 2 ≤ p) : (c p : ℝ) < 1 := by
  have h1not : 1 ∉ E p := by
    intro hmem
    have hdvd : (p : ℤ) ∣ (harmonic 1).num := by
      unfold E at hmem
      exact (Finset.mem_filter.mp hmem).2
    norm_num [harmonic] at hdvd
    have hp1 : p = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hdvd)
    omega
  have hsub : E p ⊆ Finset.Icc 2 (p - 1) := by
    intro r hr
    rw [Finset.mem_Icc]
    have hrIcc : r ∈ Finset.Icc 1 (p - 1) := by
      unfold E at hr
      exact (Finset.mem_filter.mp hr).1
    have h1r : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
    have hne : r ≠ 1 := by
      intro hreq
      rw [hreq] at hr
      exact h1not hr
    constructor
    · omega
    · exact (Finset.mem_Icc.mp hrIcc).2
  have hcard : (E p).card ≤ p - 2 := by
    have hcardIcc : (Finset.Icc 2 (p - 1)).card = p - 2 := by
      rw [Nat.card_Icc]
      omega
    rw [← hcardIcc]
    exact Finset.card_le_card hsub
  have hcq : (c p : ℚ) < 1 := by
    rw [c]
    have hden : (0 : ℚ) < (p : ℚ) - 1 := by
      have hp' : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 1 < p)
      linarith
    have hcardq : ((E p).card : ℚ) ≤ (p : ℚ) - 2 := by
      have hcardq' : ((E p).card : ℚ) ≤ ((p - 2 : ℕ) : ℚ) := by exact_mod_cast hcard
      have hcast : ((p - 2 : ℕ) : ℚ) = (p : ℚ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ p)]
        norm_num
      rwa [hcast] at hcardq'
    have hle : ((E p).card : ℚ) / ((p : ℚ) - 1) ≤ ((p : ℚ) - 2) / ((p : ℚ) - 1) := by
      exact div_le_div_of_nonneg_right hcardq (le_of_lt hden)
    have hlt : ((p : ℚ) - 2) / ((p : ℚ) - 1) < 1 := by
      rw [div_lt_one hden]
      linarith
    exact hle.trans_lt hlt
  exact_mod_cast hcq

/-- For `0 ≤ t ≤ 1 / 2` one has `log (1 - t) ≥ -2t`, obtained from `log x ≤ x - 1` at
`x = (1 - t)⁻¹`. -/
lemma log_one_sub_ge_neg_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -2 * t ≤ Real.log (1 - t) := by
  have hpos : 0 < 1 - t := by linarith [ht1]
  have hle1 : Real.log ((1 - t)⁻¹) ≤ (1 - t)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have hle2 : -Real.log (1 - t) ≤ t / (1 - t) := by
    rw [Real.log_inv] at hle1
    have hrhs : (1 - t)⁻¹ - 1 = t / (1 - t) := by
      field_simp [hpos.ne']
      ring
    rwa [hrhs] at hle1
  have hle3 : t / (1 - t) ≤ 2 * t := by
    rw [div_le_iff₀ hpos]
    have hnonneg : 0 ≤ t * (1 - 2 * t) :=
      mul_nonneg ht0 (by linarith [ht1] : 0 ≤ 1 - 2 * t)
    nlinarith [hnonneg]
  have hle4 : -Real.log (1 - t) ≤ 2 * t := hle2.trans hle3
  linarith

/-- `x / (log x)^M → ∞` over `ℕ` for any `M > 0` (in fact for any real `M`). -/
lemma tendsto_div_log_pow_atTop (M : ℝ) (_hM : 0 < M) :
    Tendsto (fun x : ℕ => (x : ℝ) / (Real.log (x : ℝ)) ^ M) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.exp x / x ^ M) atTop atTop :=
    tendsto_exp_div_rpow_atTop M
  have h2 : Tendsto (fun x : ℝ => Real.exp (Real.log x) / (Real.log x) ^ M) atTop atTop :=
    h1.comp Real.tendsto_log_atTop
  have h3 : Tendsto (fun x : ℝ => x / (Real.log x) ^ M) atTop atTop :=
    h2.congr' (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.exp_log hx])
  exact h3.comp tendsto_natCast_atTop_atTop

/-- `HA_arith` + `c` eventually small on primes forces the product of `(1 - c p)` over
primes `p ≤ x` to be `≥ K · (log x)^(-M)` eventually (in fact with `M = 2C`). -/
lemma prod_one_sub_c_ge (harith : HA_arith) :
    ∃ K M : ℝ, 0 < K ∧ 0 < M ∧ ∀ᶠ x : ℕ in atTop,
      K * (Real.log (x : ℝ)) ^ (-M) ≤
        ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
  rcases eventually_atTop.mp c_eventually_le_one_half with ⟨p₀, hp₀⟩
  rcases harith with ⟨C, hCpos, hsum⟩
  rcases eventually_atTop.mp hsum with ⟨N, hN⟩
  let p₁ : ℕ := max p₀ 2
  have h2p₁ : 2 ≤ p₁ := le_max_right p₀ 2
  have hp₀p₁ : p₀ ≤ p₁ := le_max_left p₀ 2
  have hp₁ : ∀ p, p₁ ≤ p → Nat.Prime p → (c p : ℝ) ≤ 1 / 2 :=
    fun p hpp₁ hpP => hp₀ p (hp₀p₁.trans hpp₁) hpP
  let A : ℝ := ∏ p ∈ (Finset.Icc 2 (p₁ - 1)).filter Nat.Prime, (1 - (c p : ℝ))
  let T : ℕ → Finset ℕ := fun x => (Finset.Icc p₁ x).filter Nat.Prime
  have hApos : 0 < A := by
    dsimp [A]
    refine Finset.prod_pos ?_
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hple : p ∈ Finset.Icc 2 (p₁ - 1) := (Finset.mem_filter.mp hp).1
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp hple).1
    have hcp : (c p : ℝ) < 1 := c_lt_one p hp2
    linarith
  refine ⟨A, 2 * C, hApos, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop p₁, eventually_ge_atTop N] with x hx hxN
  have hlogx_pos : 0 < Real.log (x : ℝ) := by
    have hxgt : 1 < x := by omega
    exact Real.log_pos (by exact_mod_cast hxgt : (1 : ℝ) < (x : ℝ))
  -- (1) the sum of `c p` over the tail `T x` is bounded by `C · log(log x)`
  have hsub : T x ⊆ (Finset.Icc 2 x).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter]
    have hpIcc : p ∈ Finset.Icc p₁ x := (Finset.mem_filter.mp hp).1
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨h2p₁.trans (Finset.mem_Icc.mp hpIcc).1, (Finset.mem_Icc.mp hpIcc).2⟩
    · exact (Finset.mem_filter.mp hp).2
  have hsumTail : (∑ p ∈ T x, (c p : ℝ)) ≤ C * Real.log (Real.log (x : ℝ)) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => c_nonneg p)).trans (hN x hxN)
  -- (2) per-prime log bound, summed over the tail
  have hlog_elem : ∀ p ∈ T x, -2 * (c p : ℝ) ≤ Real.log (1 - (c p : ℝ)) := by
    intro p hp
    have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hpp₁ : p₁ ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact log_one_sub_ge_neg_two_mul (c_nonneg p) (hp₁ p hpp₁ hpP)
  have hlogsum : (∑ p ∈ T x, -2 * (c p : ℝ)) ≤ ∑ p ∈ T x, Real.log (1 - (c p : ℝ)) :=
    Finset.sum_le_sum hlog_elem
  have hlogsum_lower : -(2 * C) * Real.log (Real.log (x : ℝ)) ≤
      ∑ p ∈ T x, Real.log (1 - (c p : ℝ)) := by
    calc
      -(2 * C) * Real.log (Real.log (x : ℝ)) ≤ -2 * (∑ p ∈ T x, (c p : ℝ)) := by
        nlinarith [hsumTail]
      _ = ∑ p ∈ T x, -2 * (c p : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ T x, Real.log (1 - (c p : ℝ)) := hlogsum
  -- (3) exponentiate the sum-of-logs lower bound
  have hle_exp : Real.exp (-(2 * C) * Real.log (Real.log (x : ℝ))) ≤
      ∏ p ∈ T x, (1 - (c p : ℝ)) := by
    have h1 : Real.exp (-(2 * C) * Real.log (Real.log (x : ℝ))) ≤
        Real.exp (∑ p ∈ T x, Real.log (1 - (c p : ℝ))) :=
      Real.exp_le_exp.mpr hlogsum_lower
    have h2 : Real.exp (∑ p ∈ T x, Real.log (1 - (c p : ℝ))) =
        ∏ p ∈ T x, Real.exp (Real.log (1 - (c p : ℝ))) :=
      Real.exp_sum (T x) (fun p => Real.log (1 - (c p : ℝ)))
    have h3 : ∏ p ∈ T x, Real.exp (Real.log (1 - (c p : ℝ))) =
        ∏ p ∈ T x, (1 - (c p : ℝ)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      have hpP : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hpp₁ : p₁ ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      have hpos : 0 < 1 - (c p : ℝ) := by
        have hle : (c p : ℝ) ≤ 1 / 2 := hp₁ p hpp₁ hpP
        linarith
      exact Real.exp_log hpos
    rwa [h2, h3] at h1
  -- (4) rewrite the exp form as a rpow
  have htail : (Real.log (x : ℝ)) ^ (-(2 * C)) ≤ ∏ p ∈ T x, (1 - (c p : ℝ)) := by
    have hrpow : (Real.log (x : ℝ)) ^ (-(2 * C)) =
        Real.exp (-(2 * C) * Real.log (Real.log (x : ℝ))) := by
      rw [Real.rpow_def_of_pos hlogx_pos]
      congr 1
      ring
    rwa [hrpow]
  -- (5) split the full product into small primes `A` and the tail `T x`
  have hsplit := (Finset.prod_filter_mul_prod_filter_not
    (s := (Finset.Icc 2 x).filter Nat.Prime)
    (p := fun q => p₁ ≤ q)
    (f := fun q => (1 - (c q : ℝ)))).symm
  have htail_eq : ((Finset.Icc 2 x).filter Nat.Prime).filter (fun q => p₁ ≤ q) = T x := by
    ext q
    constructor
    · intro hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨hP, hqp₁⟩
      rw [Finset.mem_filter] at hP
      rcases hP with ⟨hIcc, hqP⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        exact ⟨hqp₁, (Finset.mem_Icc.mp hIcc).2⟩
      · exact hqP
    · intro hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨hIcc, hqP⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Icc]
          exact ⟨h2p₁.trans (Finset.mem_Icc.mp hIcc).1, (Finset.mem_Icc.mp hIcc).2⟩
        · exact hqP
      · exact (Finset.mem_Icc.mp hIcc).1
  have hsmall_eq : ((Finset.Icc 2 x).filter Nat.Prime).filter (fun q => ¬ p₁ ≤ q) =
      (Finset.Icc 2 (p₁ - 1)).filter Nat.Prime := by
    ext q
    constructor
    · intro hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨hP, hnot⟩
      rw [Finset.mem_filter] at hP
      rcases hP with ⟨hIcc, hqP⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc]
        exact ⟨(Finset.mem_Icc.mp hIcc).1, by omega⟩
      · exact hqP
    · intro hq
      rw [Finset.mem_filter] at hq
      rcases hq with ⟨hIcc, hqP⟩
      rcases Finset.mem_Icc.mp hIcc with ⟨hq2, hqle⟩
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_filter]
        constructor
        · rw [Finset.mem_Icc]
          exact ⟨hq2, by omega⟩
        · exact hqP
      · exact Nat.not_le.mpr (by omega : q < p₁)
  have hprod_split : (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) =
      A * (∏ p ∈ T x, (1 - (c p : ℝ))) := by
    dsimp [A]
    rw [hsplit, htail_eq, hsmall_eq, mul_comm]
  -- (6) combine the tail bound with the positive constant `A`
  have hmain : A * (Real.log (x : ℝ)) ^ (-(2 * C)) ≤
      ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
    have hA : A * (Real.log (x : ℝ)) ^ (-(2 * C)) ≤
        A * (∏ p ∈ T x, (1 - (c p : ℝ))) :=
      mul_le_mul_of_nonneg_left htail (le_of_lt hApos)
    simpa [hprod_split] using hA
  exact hmain

/-- Infinitely many `n` have `gcd (a n) (L n) = 1` iff the count `G x` is eventually at
least every constant. -/
lemma infinite_good_iff_G_tendsto :
    (∀ C : ℕ, ∀ᶠ x in atTop, C ≤ G x) ↔
      Set.Infinite {n : ℕ | Nat.gcd (a n) (L n) = 1} := by
  set S : Set ℕ := {n : ℕ | Nat.gcd (a n) (L n) = 1}
  constructor
  · intro h
    by_contra hSinf
    have hSfin : S.Finite := Set.not_infinite.mp hSinf
    have hGle : ∀ x, G x ≤ hSfin.toFinset.card := by
      intro x
      unfold G
      have hsub :
          (Finset.Icc 1 x).filter (fun n => Nat.gcd (a n) (L n) = 1) ⊆ hSfin.toFinset := by
        rw [← Finset.coe_subset]
        rw [hSfin.coe_toFinset]
        intro n hn
        exact (Finset.mem_filter.mp (Finset.mem_coe.mp hn)).2
      exact Finset.card_le_card hsub
    have hevent : ∀ᶠ x in atTop, hSfin.toFinset.card + 1 ≤ G x := h (hSfin.toFinset.card + 1)
    rcases eventually_atTop.mp hevent with ⟨N, hN⟩
    have hcontra : hSfin.toFinset.card + 1 ≤ hSfin.toFinset.card := by
      calc
        hSfin.toFinset.card + 1 ≤ G N := hN N le_rfl
        _ ≤ hSfin.toFinset.card := hGle N
    omega
  · intro hS C
    obtain ⟨t, htsub, htcard⟩ := Set.Infinite.exists_subset_card_eq hS (C + 1)
    let t' := t.erase (0 : ℕ)
    have ht'card : C ≤ t'.card := by
      have hle : t.card - 1 ≤ t'.card := Finset.pred_card_le_card_erase (s := t) (a := 0)
      rw [htcard] at hle
      omega
    let N := t'.sup id
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro x hx
    have ht'sub_Icc : t' ⊆ Finset.Icc 1 x := by
      intro n hn
      rw [Finset.mem_Icc]
      constructor
      · exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finset.mem_erase.mp hn).1)
      · exact le_trans (Finset.le_sup (s := t') (f := id) hn) hx
    have ht'card_le : t'.card ≤ G x := by
      unfold G
      have hsub2 : t' ⊆ (Finset.Icc 1 x).filter (fun n => Nat.gcd (a n) (L n) = 1) := by
        intro n hn
        rw [Finset.mem_filter]
        constructor
        · exact ht'sub_Icc hn
        · exact htsub (Finset.mem_coe.2 ((Finset.erase_subset (0 : ℕ) t) hn))
      exact Finset.card_le_card hsub2
    exact le_trans ht'card ht'card_le

/-- `HA_dist` + `HA_arith` force `G x` to be eventually at least every constant. -/
lemma G_tendsto_atTop (hdist : HA_dist) (harith : HA_arith) :
    ∀ C : ℕ, ∀ᶠ x in atTop, C ≤ G x := by
  intro C
  rcases hdist with ⟨ε, hε0, hdist_ineq⟩
  rcases prod_one_sub_c_ge harith with ⟨K, M, hKpos, hMpos, hprod⟩
  have hεsmall : ∀ᶠ x in atTop, ε x ≤ 1 / 2 := by
    have hlt : ∀ᶠ x in atTop, ε x < 1 / 2 :=
      (tendsto_order.1 hε0).2 (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hlt] with x hx
    exact hx.le
  have hf : Tendsto (fun x : ℕ => (K / 2) * (x : ℝ) / (Real.log (x : ℝ)) ^ M) atTop atTop := by
    have hbase : Tendsto (fun x : ℕ => (x : ℝ) / (Real.log (x : ℝ)) ^ M) atTop atTop :=
      tendsto_div_log_pow_atTop M hMpos
    have hKhalf : 0 < K / 2 := by positivity
    simpa [div_eq_mul_inv, mul_assoc] using hbase.const_mul_atTop hKhalf
  have hCevent := hf.eventually_ge_atTop (C : ℝ)
  filter_upwards [hdist_ineq, hprod, hεsmall, hCevent, eventually_gt_atTop (1 : ℕ)] with
    x hdistx hprodx hεx hCx hxgt
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hxgt : (1 : ℝ) < (x : ℝ))
  have hnonneg_mul : 0 ≤ (1 - ε x) * (x : ℝ) := by
    exact mul_nonneg (by linarith [hεx] : 0 ≤ 1 - ε x) (Nat.cast_nonneg _)
  have hprod' : K / (Real.log (x : ℝ)) ^ M ≤
      ∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ)) := by
    simpa [div_eq_mul_inv, Real.rpow_neg (le_of_lt hlogpos) M] using hprodx
  have hmul : (1 - ε x) * (x : ℝ) * (K / (Real.log (x : ℝ)) ^ M) ≤
      (1 - ε x) * (x : ℝ) *
        (∏ p ∈ (Finset.Icc 2 x).filter Nat.Prime, (1 - (c p : ℝ))) :=
    mul_le_mul_of_nonneg_left hprod' hnonneg_mul
  have hleG : (1 - ε x) * (x : ℝ) * (K / (Real.log (x : ℝ)) ^ M) ≤ (G x : ℝ) :=
    hmul.trans hdistx
  have hlower : (K / 2) * (x : ℝ) / (Real.log (x : ℝ)) ^ M ≤
      (1 - ε x) * (x : ℝ) * (K / (Real.log (x : ℝ)) ^ M) := by
    have hxnonneg : 0 ≤ (x : ℝ) := Nat.cast_nonneg _
    have hlogMpos : 0 < (Real.log (x : ℝ)) ^ M := Real.rpow_pos_of_pos hlogpos M
    have hfactor : 0 ≤ (x : ℝ) * ((Real.log (x : ℝ)) ^ M)⁻¹ :=
      mul_nonneg hxnonneg (le_of_lt (inv_pos.mpr hlogMpos))
    have hcoef : K / 2 ≤ (1 - ε x) * K := by
      have hhalf : 1 / 2 ≤ 1 - ε x := by linarith [hεx]
      have hle : (1 / 2) * K ≤ (1 - ε x) * K :=
        mul_le_mul_of_nonneg_right hhalf (le_of_lt hKpos)
      nlinarith [hle]
    have h1 : (K / 2) * ((x : ℝ) * ((Real.log (x : ℝ)) ^ M)⁻¹) ≤
        (1 - ε x) * K * ((x : ℝ) * ((Real.log (x : ℝ)) ^ M)⁻¹) :=
      mul_le_mul_of_nonneg_right hcoef hfactor
    have hL : (K / 2) * (x : ℝ) / (Real.log (x : ℝ)) ^ M =
        (K / 2) * ((x : ℝ) * ((Real.log (x : ℝ)) ^ M)⁻¹) := by
      rw [div_eq_mul_inv]
      ring
    have hR : (1 - ε x) * (x : ℝ) * (K / (Real.log (x : ℝ)) ^ M) =
        (1 - ε x) * K * ((x : ℝ) * ((Real.log (x : ℝ)) ^ M)⁻¹) := by
      rw [div_eq_mul_inv]
      ring
    rwa [hL, hR]
  have hmain : (C : ℝ) ≤ (G x : ℝ) := by
    calc
      (C : ℝ) ≤ (K / 2) * (x : ℝ) / (Real.log (x : ℝ)) ^ M := hCx
      _ ≤ (1 - ε x) * (x : ℝ) * (K / (Real.log (x : ℝ)) ^ M) := hlower
      _ ≤ (G x : ℝ) := hleG
  exact_mod_cast hmain

/-- Under `HA_dist` and `HA_arith`, the set of `n` with `gcd (a n) (L n) = 1` is
infinite. -/
theorem gcd_eq_one_infinite (hdist : HA_dist) (harith : HA_arith) :
    Set.Infinite {n : ℕ | Nat.gcd (a n) (L n) = 1} := by
  rw [← infinite_good_iff_G_tendsto]
  exact G_tendsto_atTop hdist harith

end Erdos291
