import Erdos291.BadSet

/-!
# Erdős #291 — unconditional progress on the "bad digit" density

This file proves three *unconditional* facts (i.e. not resting on the analytic
hypotheses `HA_dist` / `HA_arith` of `GcdOne.lean`) about the bad-digit set `E p` and
its density `c p = |E p| / (p - 1)`:

* `c_ge_inv_pred`: for every odd prime `p` one has `1 / (p - 1) ≤ c p`.  Wolstenholme's
  theorem supplies the bad digit `p - 1`, so `E p` is nonempty.

* `sum_c_ge_sum_inv_pred`: summing the previous bound over primes `p ≤ x` gives
  `∑_{p ≤ x} 1 / (p - 1) ≤ ∑_{p ≤ x} c p`.

* `count_pbad_in_decade`: in a base-`p` decade `[p^e, p^(e+1))` (with `1 ≤ e` so that
  `p ≤ n` throughout the decade) the number of `n` with `p ∣ gcd (a n) (L n)` is exactly
  `|E p| · p^e`, i.e. the fraction of `p`-bad integers in the decade is precisely `c p`.

The hypothesis `1 ≤ e` in the last statement is essential: for `e = 0` the interval is
`[1, p)` and `p ∤ L n` for every `n` in it (no `k ≤ n < p` is a multiple of `p`), so the
count is `0` while `|E p| ≥ 1`; see `count_pbad_in_decade_false_for_e_zero` at the bottom.
-/

open scoped BigOperators

namespace Erdos291

/-- Wolstenholme's theorem gives the bad digit `p - 1`, so the density `c p = |E p| / (p-1)`
is at least `1 / (p - 1)`. -/
theorem c_ge_inv_pred (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (((p - 1 : ℕ) : ℚ)⁻¹) ≤ c p := by
  have hmem : p - 1 ∈ E p := wolstenholme_mem_E p hp
  have hcard : 1 ≤ (E p).card := by
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨p - 1, hmem⟩)
  have hden : (0 : ℚ) < (p : ℚ) - 1 := by
    have hp_gt : (1 : ℚ) < (p : ℚ) := by
      have : (1 : ℕ) < p := by omega
      exact_mod_cast this
    linarith
  have hle : (1 : ℚ) ≤ ((E p).card : ℚ) := by
    exact_mod_cast hcard
  rw [c]
  rw [← one_div]
  have hcast : ((p - 1 : ℕ) : ℚ) = (p : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  rw [hcast]
  exact div_le_div_of_nonneg_right hle (le_of_lt hden)

/-- Summing `c_ge_inv_pred` over the primes `p ≤ x` gives
`∑_{p ≤ x} 1 / (p - 1) ≤ ∑_{p ≤ x} c p`. -/
theorem sum_c_ge_sum_inv_pred (x : ℕ) :
    (∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (((p - 1 : ℕ) : ℚ)⁻¹))
      ≤ ∑ p ∈ (Finset.Icc 3 x).filter Nat.Prime, (c p : ℚ) := by
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp3 : 3 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  exact @c_ge_inv_pred p ⟨hpPrime⟩ hp3

/-- For `n` in the base-`p` decade `[p^e, p^(e+1))` with `1 ≤ e` (so that `p ≤ n`), the
prime `p` divides `gcd (a n) (L n)` exactly when the leading base-`p` digit `n / p^e` is
bad (`∈ E p`). -/
lemma p_dvd_gcd_iff_leadingDigit_mem_E (p e n : ℕ) [Fact p.Prime] (he : 1 ≤ e)
    (hn : n ∈ Finset.Ico (p ^ e) (p ^ (e + 1))) :
    p ∣ Nat.gcd (a n) (L n) ↔ n / p ^ e ∈ E p := by
  have hp : Nat.Prime p := Fact.out
  have hp1 : 1 ≤ p := le_of_lt (Nat.Prime.one_lt hp)
  have he0 : e ≠ 0 := by omega
  have hpow_le : p ≤ p ^ e := Nat.le_self_pow he0 p
  have hn_le : p ^ e ≤ n := (Finset.mem_Ico.mp hn).1
  have hpn : p ≤ n := hpow_le.trans hn_le
  have hdvdL : p ∣ L n := dvd_L_of_mem_Icc n p (by
    rw [Finset.mem_Icc]
    exact ⟨hp1, hpn⟩)
  have hgcd_iff : p ∣ Nat.gcd (a n) (L n) ↔ p ∣ a n := by
    constructor
    · intro h
      exact Nat.dvd_trans h (Nat.gcd_dvd_left (a n) (L n))
    · intro h
      exact Nat.dvd_gcd h hdvdL
  have hdvd_a_iff : p ∣ a n ↔ n / p ^ e ∈ E p := by
    have hlog : Nat.log p n = e :=
      Nat.log_eq_of_pow_le_of_lt_pow hn_le (Finset.mem_Ico.mp hn).2
    have hdiv_lt : n / p ^ e < p := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hp.pos e)]
      simpa [pow_succ, mul_comm] using (Finset.mem_Ico.mp hn).2
    have hdiv_pos : 0 < n / p ^ e := Nat.div_pos hn_le (pow_pos hp.pos e)
    have hmemIcc : n / p ^ e ∈ Finset.Icc 1 (p - 1) := by
      rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_of_lt hdiv_pos, by omega⟩
    rw [dvd_a_iff_sum_inv_eq_zero p n hpn, hlog]
    rw [E, Finset.mem_filter]
    rw [num_dvd_iff_sum_inv_zero p (n / p ^ e) hdiv_lt]
    constructor
    · intro h
      exact ⟨hmemIcc, h⟩
    · intro h
      exact h.2
  exact hgcd_iff.trans hdvd_a_iff

/-- In a base-`p` decade `[p^e, p^(e+1))` with `1 ≤ e`, exactly `|E p| · p^e` integers `n`
satisfy `p ∣ gcd (a n) (L n)`: the map `n ↦ (n / p^e, n % p^e)` is a bijection onto
`E p × Ico 0 (p^e)`. -/
theorem count_pbad_in_decade (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    ((Finset.Ico (p ^ e) (p ^ (e + 1))).filter fun n => p ∣ Nat.gcd (a n) (L n)).card
      = (E p).card * p ^ e := by
  have hp : Nat.Prime p := Fact.out
  let s : Finset ℕ :=
    (Finset.Ico (p ^ e) (p ^ (e + 1))).filter fun n => p ∣ Nat.gcd (a n) (L n)
  let t : Finset (ℕ × ℕ) := (E p) ×ˢ (Finset.Ico 0 (p ^ e))
  have hcard : s.card = t.card := by
    refine Finset.card_bij (fun n _ => (n / p ^ e, n % p ^ e)) ?_ ?_ ?_
    · -- membership: the forward map lands in `t`
      intro n hn
      have hnIco : n ∈ Finset.Ico (p ^ e) (p ^ (e + 1)) := (Finset.mem_filter.mp hn).1
      have hbad : p ∣ Nat.gcd (a n) (L n) := (Finset.mem_filter.mp hn).2
      have hrE : n / p ^ e ∈ E p :=
        (p_dvd_gcd_iff_leadingDigit_mem_E p e n he hnIco).mp hbad
      have htIco : n % p ^ e ∈ Finset.Ico 0 (p ^ e) := by
        rw [Finset.mem_Ico]
        exact ⟨Nat.zero_le _, Nat.mod_lt n (pow_pos hp.pos e)⟩
      exact Finset.mk_mem_product hrE htIco
    · -- injectivity
      intro n₁ _ n₂ _ h
      have hdiv : n₁ / p ^ e = n₂ / p ^ e := by simpa using congrArg Prod.fst h
      have hmod : n₁ % p ^ e = n₂ % p ^ e := by simpa using congrArg Prod.snd h
      calc
        n₁ = p ^ e * (n₁ / p ^ e) + n₁ % p ^ e := (Nat.div_add_mod n₁ (p ^ e)).symm
        _ = p ^ e * (n₂ / p ^ e) + n₂ % p ^ e := by rw [hdiv, hmod]
        _ = n₂ := Nat.div_add_mod n₂ (p ^ e)
    · -- surjectivity
      intro b hb
      rcases b with ⟨r, t⟩
      have hrE : r ∈ E p := (Finset.mem_product.mp hb).1
      have htIco : t ∈ Finset.Ico 0 (p ^ e) := (Finset.mem_product.mp hb).2
      have ht_lt : t < p ^ e := (Finset.mem_Ico.mp htIco).2
      have hrIcc : r ∈ Finset.Icc 1 (p - 1) := by
        unfold E at hrE
        exact (Finset.mem_filter.mp hrE).1
      have hr_ge : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
      have hr_le : r ≤ p - 1 := (Finset.mem_Icc.mp hrIcc).2
      let n : ℕ := r * p ^ e + t
      have hdiv_n : n / p ^ e = r := by
        dsimp [n]
        apply Nat.div_eq_of_lt_le
        · exact Nat.le_add_right (r * p ^ e) t
        · have h : r * p ^ e + t < r * p ^ e + p ^ e := Nat.add_lt_add_left ht_lt _
          have hgoal : (r + 1) * p ^ e = r * p ^ e + p ^ e := by rw [add_mul, one_mul]
          rw [hgoal]
          exact h
      have hmod_n : n % p ^ e = t := by
        dsimp [n]
        rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht_lt]
      have hnIco : n ∈ Finset.Ico (p ^ e) (p ^ (e + 1)) := by
        dsimp [n]
        rw [Finset.mem_Ico]
        constructor
        · have hp_le : p ^ e ≤ r * p ^ e := by
            simpa using (Nat.mul_le_mul_right (p ^ e) hr_ge : 1 * p ^ e ≤ r * p ^ e)
          exact hp_le.trans (Nat.le_add_right (r * p ^ e) t)
        · have h : r * p ^ e + t < r * p ^ e + p ^ e := Nat.add_lt_add_left ht_lt _
          have hle2 : r * p ^ e + p ^ e ≤ p ^ (e + 1) := by
            calc
              r * p ^ e + p ^ e = (r + 1) * p ^ e := by rw [add_mul, one_mul]
              _ ≤ p * p ^ e := Nat.mul_le_mul_right (p ^ e) (by omega : r + 1 ≤ p)
              _ = p ^ (e + 1) := (pow_succ' p e).symm
          exact h.trans_le hle2
      have hbad : p ∣ Nat.gcd (a n) (L n) := by
        exact (p_dvd_gcd_iff_leadingDigit_mem_E p e n he hnIco).mpr (by rw [hdiv_n]; exact hrE)
      have hn : n ∈ s := Finset.mem_filter.mpr ⟨hnIco, hbad⟩
      refine ⟨n, hn, ?_⟩
      exact Prod.ext hdiv_n hmod_n
  have htcard : t.card = (E p).card * p ^ e := by
    dsimp [t]
    rw [Finset.card_product, Nat.card_Ico, Nat.sub_zero]
  simpa [s] using hcard.trans htcard

/-- The hypothesis `1 ≤ e` in `count_pbad_in_decade` is essential: for `p = 3` and `e = 0`
the interval is `Ico 1 3 = {1, 2}`, and `3 ∤ L 1`, `3 ∤ L 2`, so the count is `0`, while
`(E 3).card = 1`. -/
lemma count_pbad_in_decade_false_for_e_zero :
    ¬ (((Finset.Ico (3 ^ 0) (3 ^ 1)).filter fun n => 3 ∣ Nat.gcd (a n) (L n)).card
        = (E 3).card * 3 ^ 0) := by
  native_decide

end Erdos291
