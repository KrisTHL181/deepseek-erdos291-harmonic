import Erdos291.BadSet
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Rat.Lemmas

/-!
# Erdős #291 — the Bernoulli characterization of the bad-digit set

For a prime `p`, the bad digits are `E p = {r ∈ [1, p-1] : p ∣ (harmonic r).num}`. This file
proves the bridge to the root-set bijection: the congruence

    (p - 1) · H_r ≡ B_{p-1}(r+1) - B_{p-1}  (mod p),

or, in the clean `ZMod p` form mirroring `num_dvd_iff_sum_inv_zero`,

    p ∣ (harmonic r).num  ↔  bernoulli_mod p (p-1) (r+1) = 0.

The route is: (1) Fermat (`j⁻¹ = j^(p-2)`), (2) Faulhaber's sum-of-powers identity in
`Polynomial.sum_range_pow_eq_bernoulli_sub`, (3) the von Staudt–Clausen theorem to show the
*difference* polynomial `B_n(x) - B_n` has `p`-adically integral coefficients (so reducing it
modulo `p` is legitimate).

The key subtlety: the Bernoulli number `B_{p-1}` has `p` in its denominator, so we never cast
`B_{p-1}` or `B_{p-1}(x)` to `ZMod p` directly. Instead we reduce the difference
`B_n(x) - B_n = Σ_{k=0}^{n-1} C(n,k)·B_k·x^{n-k}`, whose every coefficient `C(n,k)·B_k`
(for `k < n = p-1`) has `p`-free denominator by von Staudt–Clausen.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

/-! ## Reducing `p`-integral rationals to `ZMod p` -/

/-- The reduction of a rational `q = num / den` modulo `p`, defined for *all* rationals but
only a ring hom on the `p`-integral ones (those with `p ∤ q.den`). -/
def ratMod (p : ℕ) (q : ℚ) : ZMod p :=
  (q.num : ZMod p) * ((q.den : ZMod p))⁻¹

/-- `p` never divides `1`. -/
lemma p_not_dvd_one (p : ℕ) [Fact p.Prime] : ¬ p ∣ 1 :=
  (Fact.out : Nat.Prime p).not_dvd_one

@[simp]
lemma ratMod_intCast (p : ℕ) (z : ℤ) : ratMod p (z : ℚ) = (z : ZMod p) := by
  rw [ratMod, Rat.num_intCast, Rat.den_intCast]
  simp

@[simp]
lemma ratMod_natCast (p : ℕ) (n : ℕ) : ratMod p (n : ℚ) = (n : ZMod p) := by
  rw [ratMod, Rat.num_natCast, Rat.den_natCast]
  simp

/-- `ratMod` of a natural power of a natural. -/
lemma ratMod_natCast_pow (p x m : ℕ) : ratMod p ((x : ℚ) ^ m) = (x : ZMod p) ^ m := by
  rw [← Nat.cast_pow, ratMod_natCast, Nat.cast_pow]

/-- `(1 / q).den = q` for `q ≠ 0`. -/
lemma one_div_den_eq (q : ℕ) (hq : q ≠ 0) : ((1 : ℚ) / (q : ℚ)).den = q := by
  rw [one_div, Rat.den_inv, Rat.num_natCast]
  simp [hq]

/-- If `p` does not divide `a.den` or `b.den`, then `p` does not divide `(a + b).den`. -/
lemma not_dvd_den_add (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ¬ p ∣ (a + b).den := by
  intro h
  have hdiv : (a + b).den ∣ a.den * b.den := Rat.add_den_dvd a b
  have hpab : p ∣ a.den * b.den := dvd_trans h hdiv
  rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime p)).mp hpab with hpa | hpb
  · exact ha hpa
  · exact hb hpb

/-- If `p` does not divide `a.den` or `b.den`, then `p` does not divide `(a * b).den`. -/
lemma not_dvd_den_mul (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ¬ p ∣ (a * b).den := by
  intro h
  have hdiv : (a * b).den ∣ a.den * b.den := Rat.mul_den_dvd a b
  have hpab : p ∣ a.den * b.den := dvd_trans h hdiv
  rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime p)).mp hpab with hpa | hpb
  · exact ha hpa
  · exact hb hpb

/-- A finite sum of rationals with `p`-free denominators has `p`-free denominator. -/
lemma not_dvd_den_sum (p : ℕ) [Fact p.Prime] {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ a ∈ s, ¬ p ∣ (f a).den) : ¬ p ∣ (∑ a ∈ s, f a).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [p_not_dvd_one p]
  | @insert a s has ih =>
      rw [Finset.sum_insert has]
      exact not_dvd_den_add p (h a (Finset.mem_insert.mpr (Or.inl rfl)))
        (ih fun b hb => h b (Finset.mem_insert.mpr (Or.inr hb)))

/-- Cross-multiplication identity underlying additivity of the reduction map (over `ℚ`). -/
lemma cross_add (a b : ℚ) :
    ((a + b).num : ℚ) * ((a.den * b.den : ℕ) : ℚ) =
      (((a + b).den : ℕ) : ℚ) * ((a.num : ℚ) * (b.den : ℚ) + (b.num : ℚ) * (a.den : ℚ)) := by
  have hab : ((a + b).num : ℚ) = ((a + b).den : ℚ) * (a + b) := by
    have h := Rat.num_div_den (a + b)
    rw [div_eq_iff_mul_eq] at h
    · simpa [mul_comm] using h.symm
    · exact_mod_cast (Rat.den_ne_zero (a + b))
  have ha : (a.num : ℚ) = (a.den : ℚ) * a := by
    have h := Rat.num_div_den a
    rw [div_eq_iff_mul_eq] at h
    · simpa [mul_comm] using h.symm
    · exact_mod_cast (Rat.den_ne_zero a)
  have hb : (b.num : ℚ) = (b.den : ℚ) * b := by
    have h := Rat.num_div_den b
    rw [div_eq_iff_mul_eq] at h
    · simpa [mul_comm] using h.symm
    · exact_mod_cast (Rat.den_ne_zero b)
  rw [hab, ha, hb]
  simp only [Nat.cast_mul]
  ring

/-- Cross-multiplication identity underlying multiplicativity of the reduction map (over `ℚ`). -/
lemma cross_mul (a b : ℚ) :
    ((a * b).num : ℚ) * ((a.den * b.den : ℕ) : ℚ) =
      (((a * b).den : ℕ) : ℚ) * ((a.num : ℚ) * (b.num : ℚ)) := by
  have hab : ((a * b).num : ℚ) = ((a * b).den : ℚ) * (a * b) := by
    have h := Rat.num_div_den (a * b)
    rw [div_eq_iff_mul_eq] at h
    · simpa [mul_comm] using h.symm
    · exact_mod_cast (Rat.den_ne_zero (a * b))
  have ha : (a.num : ℚ) = (a.den : ℚ) * a := by
    have h := Rat.num_div_den a
    rw [div_eq_iff_mul_eq] at h
    · simpa [mul_comm] using h.symm
    · exact_mod_cast (Rat.den_ne_zero a)
  have hb : (b.num : ℚ) = (b.den : ℚ) * b := by
    have h := Rat.num_div_den b
    rw [div_eq_iff_mul_eq] at h
    · simpa [mul_comm] using h.symm
    · exact_mod_cast (Rat.den_ne_zero b)
  rw [hab, ha, hb]
  simp only [Nat.cast_mul]
  ring

/-- Cross-multiplication identity underlying additivity of the reduction map (over `ℤ`). -/
lemma cross_add_int (a b : ℚ) :
    (a + b).num * ((a.den * b.den : ℕ) : ℤ) =
      ((a + b).den : ℤ) * (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)) := by
  exact_mod_cast (cross_add a b)

/-- Cross-multiplication identity underlying multiplicativity of the reduction map (over `ℤ`). -/
lemma cross_mul_int (a b : ℚ) :
    (a * b).num * ((a.den * b.den : ℕ) : ℤ) =
      ((a * b).den : ℤ) * (a.num * b.num) := by
  exact_mod_cast (cross_mul a b)

/-- `ratMod` is additive on `p`-integral rationals. -/
lemma ratMod_add (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ratMod p (a + b) = ratMod p a + ratMod p b := by
  have hua : IsUnit ((a.den : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact ha
  have hub : IsUnit ((b.den : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact hb
  have hdab : IsUnit (((a + b).den : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact not_dvd_den_add p ha hb
  -- the cross identity reduced to ZMod p
  have hz : ((a + b).num : ZMod p) * (((a.den : ℕ) : ZMod p) * ((b.den : ℕ) : ZMod p)) =
      (((a + b).den : ℕ) : ZMod p) *
        ((a.num : ZMod p) * (b.den : ℕ) + (b.num : ZMod p) * (a.den : ℕ)) := by
    have hz_int := cross_add_int a b
    have hz0 := congrArg (fun z : ℤ => (z : ZMod p)) hz_int
    simpa [Nat.cast_mul] using hz0
  unfold ratMod
  field_simp [hua.ne_zero, hub.ne_zero, hdab.ne_zero]
  ring_nf at hz ⊢
  exact hz

/-- `ratMod` is multiplicative on `p`-integral rationals. -/
lemma ratMod_mul (p : ℕ) [Fact p.Prime] {a b : ℚ}
    (ha : ¬ p ∣ a.den) (hb : ¬ p ∣ b.den) : ratMod p (a * b) = ratMod p a * ratMod p b := by
  have hua : IsUnit ((a.den : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact ha
  have hub : IsUnit ((b.den : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact hb
  have hab : IsUnit (((a * b).den : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    exact not_dvd_den_mul p ha hb
  have hz : ((a * b).num : ZMod p) * (((a.den : ℕ) : ZMod p) * ((b.den : ℕ) : ZMod p)) =
      (((a * b).den : ℕ) : ZMod p) * ((a.num : ZMod p) * (b.num : ZMod p)) := by
    have hz_int := cross_mul_int a b
    have hz0 := congrArg (fun z : ℤ => (z : ZMod p)) hz_int
    simpa [Nat.cast_mul] using hz0
  unfold ratMod
  field_simp [hua.ne_zero, hub.ne_zero, hab.ne_zero]
  ring_nf at hz ⊢
  exact hz

/-- `ratMod` commutes with finite sums of `p`-integral rationals. -/
lemma ratMod_sum (p : ℕ) [Fact p.Prime] {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ a ∈ s, ¬ p ∣ (f a).den) :
    ratMod p (∑ a ∈ s, f a) = ∑ a ∈ s, ratMod p (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ratMod]
  | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      rw [ratMod_add]
      · rw [ih (fun b hb => h b (Finset.mem_insert.mpr (Or.inr hb)))]
      · exact h a (Finset.mem_insert.mpr (Or.inl rfl))
      · exact not_dvd_den_sum p s f (fun b hb => h b (Finset.mem_insert.mpr (Or.inr hb)))

/-! ## The difference polynomial and its reduction -/

/-- Reduction modulo `p` of the difference polynomial `B_n(x) - B_n`, i.e.
`Σ_{k=0}^{n-1} C(n,k)·B_k·x^{n-k}` reduced coefficient-wise. -/
def bernoulli_mod (p n : ℕ) (x : ℕ) : ZMod p :=
  ∑ j ∈ Finset.range n, ratMod p (bernoulli j * (n.choose j : ℚ)) * (x : ZMod p) ^ (n - j)

@[simp]
lemma bernoulli_mod_zero (p n : ℕ) : bernoulli_mod p n 0 = 0 := by
  unfold bernoulli_mod
  refine Finset.sum_eq_zero ?_
  intro j hj
  have hjlt : j < n := Finset.mem_range.mp hj
  have hne : n - j ≠ 0 := by omega
  rw [show ((0 : ℕ) : ZMod p) = 0 by norm_num]
  rw [zero_pow hne, mul_zero]

/-- The Bernoulli difference polynomial evaluated at `x` equals the coefficient sum
`Σ_{j<n} C(n,j)·B_j·x^{n-j}` (exact rational identity). -/
lemma bernoulli_eval_sub (n x : ℕ) :
    (Polynomial.bernoulli n).eval (x : ℚ) - bernoulli n =
      ∑ j ∈ Finset.range n, (bernoulli j * (n.choose j : ℚ)) * (x : ℚ) ^ (n - j) := by
  change ((∑ i ∈ Finset.range (n + 1),
    Polynomial.monomial (n - i) (bernoulli i * (n.choose i : ℚ))).eval (x : ℚ)) - bernoulli n = _
  rw [Polynomial.eval_finsetSum]
  simp_rw [Polynomial.eval_monomial]
  rw [Finset.sum_range_succ]
  simp

/-! ## von Staudt–Clausen: `B_k` is `p`-integral for `k < p - 1` -/

/-- For a prime `q ≠ p`, the denominator of `1/q` is not divisible by `p`. -/
lemma one_div_den_not_dvd (p : ℕ) {q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) :
    ¬ p ∣ ((1 : ℚ) / (q : ℚ)).den := by
  rw [one_div_den_eq q hq.ne_zero]
  have hcop : p.Coprime q := (Nat.coprime_primes (Fact.out : Nat.Prime p) hq).mpr hqp.symm
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mp hcop

/-- The von Staudt–Clausen consequence: for `k < p - 1`, `p` does not divide the denominator
of the Bernoulli number `B_k`. -/
lemma bernoulli_den_not_dvd (p k : ℕ) [Fact p.Prime] (hk : k < p - 1) :
    ¬ p ∣ (bernoulli k).den := by
  by_cases hk0 : k = 0
  · subst k
    rw [bernoulli_zero]
    exact p_not_dvd_one p
  by_cases hk1 : k = 1
  · subst k
    have h2 : ¬ p ∣ 2 := by
      intro hdvd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hden : (bernoulli 1).den = 2 := by norm_num [bernoulli]
    rw [hden]
    exact h2
  rcases Nat.even_or_odd k with hkeven | hkodd
  · rcases hkeven with ⟨m, hm⟩
    subst k
    rw [show m + m = 2 * m by omega]
    have hk' : 2 * m < p - 1 := by omega
    have hmpos : 0 < m := by omega
    obtain ⟨z, hz⟩ := Set.mem_range.mp (Bernoulli.vonStaudt_clausen m)
    let S : ℚ := ∑ q ∈ (Finset.range (2 * m + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * m),
      (1 : ℚ) / (q : ℚ)
    have hzS : (z : ℚ) = bernoulli (2 * m) + S := by
      simpa [S] using hz
    have hqp : ∀ q ∈ (Finset.range (2 * m + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * m), q ≠ p := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqdiv : (q - 1) ∣ 2 * m := hq'.2.2
      intro hqp
      subst q
      have hle : p - 1 ≤ 2 * m := Nat.le_of_dvd (by omega : 0 < 2 * m) hqdiv
      omega
    have hS : ¬ p ∣ S.den := by
      dsimp [S]
      refine not_dvd_den_sum p
        ((Finset.range (2 * m + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * m))
        (fun q => (1 : ℚ) / (q : ℚ)) ?_
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      exact one_div_den_not_dvd p hq'.2.1 (hqp q hq)
    have hz' : bernoulli (2 * m) = (z : ℚ) - S := by
      exact (eq_sub_iff_add_eq.mpr hzS.symm)
    rw [hz']
    intro hpden
    have hdiv : ((z : ℚ) - S).den ∣ S.den := by
      have h := Rat.sub_den_dvd (z : ℚ) S
      simpa [Rat.den_intCast] using h
    exact hS (dvd_trans hpden hdiv)
  · have hkgt1 : 1 < k := by omega
    rw [bernoulli_eq_zero_of_odd hkodd hkgt1]
    exact p_not_dvd_one p

/-- For `j < p - 1`, the coefficient `C(p-1, j)·B_j` has `p`-free denominator. -/
lemma bernoulli_choose_den_not_dvd (p j : ℕ) [Fact p.Prime] (hj : j < p - 1) :
    ¬ p ∣ (bernoulli j * ((p - 1).choose j : ℚ)).den := by
  have hb : ¬ p ∣ (bernoulli j).den := bernoulli_den_not_dvd p j hj
  have hc : ¬ p ∣ (((p - 1).choose j : ℕ) : ℚ).den := by
    rw [Rat.den_natCast]
    exact p_not_dvd_one p
  intro h
  have hdiv : (bernoulli j * ((p - 1).choose j : ℚ)).den ∣
      (bernoulli j).den * (((p - 1).choose j : ℕ) : ℚ).den :=
    Rat.mul_den_dvd (bernoulli j) ((p - 1).choose j : ℚ)
  have hpab : p ∣ (bernoulli j).den * (((p - 1).choose j : ℕ) : ℚ).den := dvd_trans h hdiv
  rcases (Nat.Prime.dvd_mul (Fact.out : Nat.Prime p)).mp hpab with hpa | hpb
  · exact hb hpa
  · exact hc hpb

/-! ## Faulhaber, Fermat, and the main characterization -/

/-- The Faulhaber identity in the form we need. -/
lemma faulhaber_bernoulli (p x : ℕ) (hp : 2 ≤ p) :
    (((p - 1 : ℕ) : ℚ) * ∑ k ∈ Finset.range x, (k : ℚ) ^ (p - 2)) =
      (Polynomial.bernoulli (p - 1)).eval (x : ℚ) - bernoulli (p - 1) := by
  have h := Polynomial.sum_range_pow_eq_bernoulli_sub x (p - 2)
  have hsucc : (p - 2).succ = p - 1 := by omega
  have hcast : (↑(p - 2) : ℚ) + 1 = (↑(p - 1) : ℚ) := by
    rw [show p - 1 = p - 2 + 1 by omega, Nat.cast_add]
    norm_num
  rw [hsucc, hcast] at h
  exact h

/-- `bernoulli_mod p (p-1) x` equals the reduction of the Faulhaber difference. -/
lemma bernoulli_mod_eq_ratMod_eval (p x : ℕ) [Fact p.Prime] :
    bernoulli_mod p (p-1) x =
      ratMod p ((Polynomial.bernoulli (p-1)).eval (x : ℚ) - bernoulli (p-1)) := by
  unfold bernoulli_mod
  rw [bernoulli_eval_sub (p - 1) x]
  rw [ratMod_sum]
  · refine Finset.sum_congr rfl ?_
    intro j hj
    have hjlt : j < p - 1 := Finset.mem_range.mp hj
    have hbj : ¬ p ∣ (bernoulli j * ((p - 1).choose j : ℚ)).den :=
      bernoulli_choose_den_not_dvd p j hjlt
    have hpow : ¬ p ∣ (((x : ℚ) ^ (p - 1 - j)).den) := by
      rw [← Nat.cast_pow, Rat.den_natCast]
      exact p_not_dvd_one p
    rw [ratMod_mul p hbj hpow]
    rw [ratMod_natCast_pow]
  · intro j hj
    have hjlt : j < p - 1 := Finset.mem_range.mp hj
    have hbj : ¬ p ∣ (bernoulli j * ((p - 1).choose j : ℚ)).den :=
      bernoulli_choose_den_not_dvd p j hjlt
    have hpow : ¬ p ∣ (((x : ℚ) ^ (p - 1 - j)).den) := by
      rw [← Nat.cast_pow, Rat.den_natCast]
      exact p_not_dvd_one p
    exact not_dvd_den_mul p hbj hpow

/-- The key congruence: `bernoulli_mod p (p-1) x = (p-1)·Σ_{k<x} k^{p-2}` in `ZMod p`. -/
lemma bernoulli_mod_eq_mul_sum_pow (p x : ℕ) [Fact p.Prime] :
    bernoulli_mod p (p-1) x = ((p-1 : ℕ) : ZMod p) * (∑ k ∈ Finset.range x, (k : ZMod p)^(p-2)) := by
  rw [bernoulli_mod_eq_ratMod_eval]
  have hfaulhaber := faulhaber_bernoulli p x (Fact.out : Nat.Prime p).two_le
  rw [← hfaulhaber]
  rw [ratMod_mul]
  · rw [ratMod_natCast]
    rw [ratMod_sum]
    · rw [Finset.sum_congr rfl (fun k hk => ratMod_natCast_pow p k (p - 2))]
    · intro k hk
      rw [← Nat.cast_pow, Rat.den_natCast]
      exact p_not_dvd_one p
  · rw [Rat.den_natCast]
    exact p_not_dvd_one p
  · exact not_dvd_den_sum p (Finset.range x) (fun k => (k : ℚ)^(p-2)) (fun k hk => by
      rw [← Nat.cast_pow, Rat.den_natCast]
      exact p_not_dvd_one p)

/-- Fermat: `j⁻¹ = j^(p-2)` in `ZMod p` for `1 ≤ j < p`. -/
lemma inv_eq_pow_card_sub_two (p j : ℕ) [Fact p.Prime] (hj1 : 1 ≤ j) (hjp : j < p) :
    ((j : ZMod p)⁻¹) = (j : ZMod p) ^ (p - 2) := by
  have hjunit : IsUnit (j : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm,
      Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)]
    intro hdvd
    exact (not_lt_of_ge (Nat.le_of_dvd (by omega : 0 < j) hdvd)) hjp
  have hjne : (j : ZMod p) ≠ 0 := hjunit.ne_zero
  have h := ZMod.pow_card_sub_one_eq_one (p := p) (a := (j : ZMod p)) hjne
  have hpow : (j : ZMod p) ^ (p - 1) = (j : ZMod p) ^ (p - 2) * (j : ZMod p) := by
    rw [show p - 1 = (p - 2) + 1 by omega, pow_succ]
  have hmain : (j : ZMod p) ^ (p - 2) * (j : ZMod p) = 1 := by
    rw [← hpow]
    exact h
  exact (eq_inv_of_mul_eq_one_left hmain).symm

/-- Reindex `Σ_{i<r} f (i+1)` as `Σ_{k∈Icc 1 r} f k` in any additive monoid. -/
lemma reindex_sum_range_one_add {M : Type*} [AddCommMonoid M] (r : ℕ) (f : ℕ → M) :
    (∑ i ∈ Finset.range r, f (i + 1)) = ∑ k ∈ Finset.Icc 1 r, f k := by
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    have := Finset.mem_range.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨k - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro i hi
    rfl

/-- Fermat: `Σ_{j=1}^r j⁻¹ = Σ_{j=1}^r j^{p-2}` in `ZMod p`. -/
lemma sum_inv_eq_sum_pow (p r : ℕ) [Fact p.Prime] (hrp : r < p) :
    (∑ j ∈ Finset.Icc 1 r, ((j : ZMod p)⁻¹)) =
      ∑ j ∈ Finset.Icc 1 r, (j : ZMod p)^(p-2) := by
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  exact inv_eq_pow_card_sub_two p j hj'.1 (lt_of_le_of_lt hj'.2 hrp)

/-- Drop the `k = 0` term of the sum of powers (valid for `p ≥ 3`). -/
lemma sum_pow_Icc_eq_sum_pow_range (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (∑ j ∈ Finset.Icc 1 r, (j : ZMod p)^(p-2)) =
      ∑ j ∈ Finset.range (r+1), (j : ZMod p)^(p-2) := by
  symm
  rw [Finset.sum_range_succ']
  have h0 : (↑(0 : ℕ) : ZMod p) ^ (p - 2) = 0 := by
    rw [Nat.cast_zero]
    rw [zero_pow]
    omega
  rw [h0, add_zero]
  exact reindex_sum_range_one_add (M := ZMod p) r (fun k => (k : ZMod p)^(p-2))

/-- **The Bernoulli characterization of the bad-digit set.** For an odd prime `p` and
`1 ≤ r < p`, `p` divides the numerator of `H_r` iff the reduction of the difference polynomial
`B_{p-1}(x) - B_{p-1}` vanishes at `x = r + 1`. -/
theorem num_dvd_iff_bernoulli (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hr : r < p) (_hr1 : 1 ≤ r) :
    (p : ℤ) ∣ (harmonic r).num ↔ bernoulli_mod p (p - 1) (r + 1) = 0 := by
  rw [num_dvd_iff_sum_inv_zero p r hr]
  rw [sum_inv_eq_sum_pow p r hr]
  rw [sum_pow_Icc_eq_sum_pow_range p r hp]
  have h := bernoulli_mod_eq_mul_sum_pow p (r + 1)
  rw [h]
  have hunit : ((p - 1 : ℕ) : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ p - 1 := (ZMod.natCast_eq_zero_iff (p - 1) p).mp hz
    have hpos : 0 < p - 1 := by omega
    have hle : p ≤ p - 1 := Nat.le_of_dvd hpos hdvd
    omega
  have hiff : (((p - 1 : ℕ) : ZMod p) * (∑ k ∈ Finset.range (r + 1), (k : ZMod p)^(p-2)) = 0) ↔
      (∑ k ∈ Finset.range (r + 1), (k : ZMod p)^(p-2)) = 0 := by
    constructor
    · intro hz
      rw [mul_eq_zero] at hz
      rcases hz with h0 | hS
      · exact False.elim (hunit h0)
      · exact hS
    · intro hS
      rw [hS, mul_zero]
  exact hiff.symm

end

end Erdos291
