import Erdos291.MidTwoHalves

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

private def reflect (r : ℕ) : Polynomial ℤ :=
  -Polynomial.X - Polynomial.C ((r : ℤ) + 1)

private lemma reflect_degree (r : ℕ) : (reflect r).degree = 1 := by
  unfold reflect
  rw [show -Polynomial.X - Polynomial.C ((r : ℤ) + 1) =
      -(Polynomial.X + Polynomial.C ((r : ℤ) + 1)) by ring]
  rw [Polynomial.degree_neg, Polynomial.degree_X_add_C]

private lemma A_poly_comp_reflect (r : ℕ) :
    (A_poly r).comp (reflect r) = A_poly r := by
  unfold A_poly reflect
  simp only [sub_eq_add_neg, mul_comp, add_comp, neg_comp, X_comp, C_comp]
  norm_num [Nat.cast_add, Nat.cast_mul]
  ring

private lemma RemainderR_comp_reflect_even (k : ℕ) :
    (RemainderR (2 * k)).comp (reflect (2 * k)) = -RemainderR (2 * k) := by
  have hodd : Odd (2 * k + 1) := odd_two_mul_add_one k
  have hsign : ((↑(-1 : ℤ) : Polynomial ℤ) ^ (2 * k + 1)) = -1 := by
    have hcast : (↑(-1 : ℤ) : Polynomial ℤ) = -1 := by norm_num
    rw [hcast]
    exact hodd.neg_one_pow
  have hQ : (Qd (2 * k)).comp (reflect (2 * k)) = -Qd (2 * k) := by
    rw [reflect, Qd_comp_neg_X_sub_C_add_one, hsign]
    ring
  have hdiv := Polynomial.modByMonic_add_div (Qd (2 * k)) (A_poly (2 * k))
  have hdivcomp := congrArg (fun f : Polynomial ℤ => f.comp (reflect (2 * k))) hdiv
  rw [add_comp, mul_comp, A_poly_comp_reflect, hQ] at hdivcomp
  have hdeg : ((RemainderR (2 * k)).comp (reflect (2 * k))).degree <
      (A_poly (2 * k)).degree := by
    rw [RemainderR, Polynomial.degree_comp (by rw [reflect_degree]; norm_num), reflect_degree,
      mul_one]
    exact Polynomial.degree_modByMonic_lt _ (A_poly_monic _)
  have hrem : (-Qd (2 * k)) %ₘ A_poly (2 * k) =
      (RemainderR (2 * k)).comp (reflect (2 * k)) :=
    (Polynomial.div_modByMonic_unique
      ((Qd (2 * k) /ₘ A_poly (2 * k)).comp (reflect (2 * k)))
      ((RemainderR (2 * k)).comp (reflect (2 * k))) (A_poly_monic _) ⟨hdivcomp, hdeg⟩).2
  simpa [RemainderR, Polynomial.neg_modByMonic] using hrem.symm

private lemma RemainderR_comp_reflect_odd (k : ℕ) :
    (RemainderR (2 * k + 1)).comp (reflect (2 * k + 1)) = RemainderR (2 * k + 1) := by
  have heven : Even (2 * k + 1 + 1) := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    exact even_two_mul _
  have hsign : ((↑(-1 : ℤ) : Polynomial ℤ) ^ (2 * k + 1 + 1)) = 1 := by
    have hcast : (↑(-1 : ℤ) : Polynomial ℤ) = -1 := by norm_num
    rw [hcast]
    exact heven.neg_one_pow
  have hQ : (Qd (2 * k + 1)).comp (reflect (2 * k + 1)) = Qd (2 * k + 1) := by
    rw [reflect, Qd_comp_neg_X_sub_C_add_one, hsign]
    ring
  have hdiv := Polynomial.modByMonic_add_div (Qd (2 * k + 1)) (A_poly (2 * k + 1))
  have hdivcomp := congrArg (fun f : Polynomial ℤ => f.comp (reflect (2 * k + 1))) hdiv
  rw [add_comp, mul_comp, A_poly_comp_reflect, hQ] at hdivcomp
  have hdeg : ((RemainderR (2 * k + 1)).comp (reflect (2 * k + 1))).degree <
      (A_poly (2 * k + 1)).degree := by
    rw [RemainderR, Polynomial.degree_comp (by rw [reflect_degree]; norm_num), reflect_degree,
      mul_one]
    exact Polynomial.degree_modByMonic_lt _ (A_poly_monic _)
  have hrem : (Qd (2 * k + 1)) %ₘ A_poly (2 * k + 1) =
      (RemainderR (2 * k + 1)).comp (reflect (2 * k + 1)) :=
    (Polynomial.div_modByMonic_unique
      ((Qd (2 * k + 1) /ₘ A_poly (2 * k + 1)).comp (reflect (2 * k + 1)))
      ((RemainderR (2 * k + 1)).comp (reflect (2 * k + 1))) (A_poly_monic _) ⟨hdivcomp, hdeg⟩).2
  simpa [RemainderR] using hrem.symm

private lemma RemainderR_comp_reflect (r : ℕ) :
    (RemainderR r).comp (reflect r) = (-1 : ℤ) ^ (r + 1) * RemainderR r := by
  by_cases hr : r % 2 = 0
  · have htwo : r = 2 * (r / 2) := by
      have hdm := Nat.div_add_mod r 2
      omega
    rw [htwo]
    have h := RemainderR_comp_reflect_even (r / 2)
    rw [h]
    have hsign : ((↑(-1 : ℤ) : Polynomial ℤ) ^ (2 * (r / 2) + 1)) = -1 := by
      have hcast : (↑(-1 : ℤ) : Polynomial ℤ) = -1 := by norm_num
      rw [hcast]
      exact (odd_two_mul_add_one (r / 2)).neg_one_pow
    rw [hsign]
    simp
  · have hodd : r % 2 = 1 := by omega
    have htwo : r = 2 * (r / 2) + 1 := by
      have hdm := Nat.div_add_mod r 2
      omega
    rw [htwo]
    have h := RemainderR_comp_reflect_odd (r / 2)
    rw [h]
    have hsign : ((↑(-1 : ℤ) : Polynomial ℤ) ^ (2 * (r / 2) + 1 + 1)) = 1 := by
      have heven : Even (2 * (r / 2) + 1 + 1) := by
        rw [show 2 * (r / 2) + 1 + 1 = 2 * (r / 2 + 1) by omega]
        exact even_two_mul _
      have hcast : (↑(-1 : ℤ) : Polynomial ℤ) = -1 := by norm_num
      rw [hcast]
      exact heven.neg_one_pow
    rw [hsign]
    simp

private lemma poly_eq_coeff_zero_one_two_three (f : Polynomial ℤ) (hf : f.natDegree < 4) :
    f = Polynomial.monomial 0 (f.coeff 0) + Polynomial.monomial 1 (f.coeff 1) +
      Polynomial.monomial 2 (f.coeff 2) + Polynomial.monomial 3 (f.coeff 3) := by
  conv_lhs => rw [f.as_sum_range' 4 hf]
  repeat rw [Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]

private lemma poly_eq_C_coeff_zero_one_two_three (f : Polynomial ℤ) (hf : f.natDegree < 4) :
    f = Polynomial.C (f.coeff 0) + Polynomial.C (f.coeff 1) * Polynomial.X +
      Polynomial.C (f.coeff 2) * Polynomial.X ^ 2 +
        Polynomial.C (f.coeff 3) * Polynomial.X ^ 3 := by
  calc
    f = Polynomial.monomial 0 (f.coeff 0) + Polynomial.monomial 1 (f.coeff 1) +
        Polynomial.monomial 2 (f.coeff 2) + Polynomial.monomial 3 (f.coeff 3) :=
      poly_eq_coeff_zero_one_two_three f hf
    _ = Polynomial.C (f.coeff 0) + Polynomial.C (f.coeff 1) * Polynomial.X +
        Polynomial.C (f.coeff 2) * Polynomial.X ^ 2 +
          Polynomial.C (f.coeff 3) * Polynomial.X ^ 3 := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
        ← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.C_mul_X_pow_eq_monomial]
      norm_num

private lemma cubic_comp_reflect_expansion (a0 a1 a2 a3 k : ℤ) :
    (Polynomial.C a0 + Polynomial.C a1 * Polynomial.X + Polynomial.C a2 * Polynomial.X ^ 2 +
      Polynomial.C a3 * Polynomial.X ^ 3).comp (-Polynomial.X - Polynomial.C k) =
      Polynomial.C (a0 - k * a1 + k ^ 2 * a2 - k ^ 3 * a3) +
        Polynomial.C (-a1 + 2 * k * a2 - 3 * k ^ 2 * a3) * Polynomial.X +
          Polynomial.C (a2 - 3 * k * a3) * Polynomial.X ^ 2 +
            Polynomial.C (-a3) * Polynomial.X ^ 3 := by
  simp only [sub_eq_add_neg, add_comp, mul_comp, pow_comp, C_comp, X_comp]
  push_cast
  simp only [Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_neg]
  norm_num
  ring

private lemma A_poly_natDegree_test (r : ℕ) : (A_poly r).natDegree = 4 := by
  unfold A_poly
  compute_degree
  all_goals norm_num

private lemma RemainderR_natDegree_lt_four (r : ℕ) : (RemainderR r).natDegree < 4 := by
  have hne : A_poly r ≠ 1 := by
    intro h
    have hdeg := A_poly_natDegree_test r
    rw [h] at hdeg
    norm_num at hdeg
  change (Qd r %ₘ A_poly r).natDegree < 4
  rw [← A_poly_natDegree_test r]
  exact Polynomial.natDegree_modByMonic_lt _ (A_poly_monic r) hne

private lemma invariant_cubic_formula (f : Polynomial ℤ) (k : ℤ)
    (hdeg : f.natDegree < 4)
    (hsym : f.comp (-Polynomial.X - Polynomial.C k) = f) :
    f = Polynomial.C (f.coeff 0) +
      Polynomial.C (f.coeff 2) * (Polynomial.C k * Polynomial.X + Polynomial.X ^ 2) := by
  have hpoly := poly_eq_C_coeff_zero_one_two_three f hdeg
  have heq :
      (Polynomial.C (f.coeff 0) + Polynomial.C (f.coeff 1) * Polynomial.X +
        Polynomial.C (f.coeff 2) * Polynomial.X ^ 2 +
          Polynomial.C (f.coeff 3) * Polynomial.X ^ 3).comp
          (-Polynomial.X - Polynomial.C k) =
        Polynomial.C (f.coeff 0) + Polynomial.C (f.coeff 1) * Polynomial.X +
          Polynomial.C (f.coeff 2) * Polynomial.X ^ 2 +
            Polynomial.C (f.coeff 3) * Polynomial.X ^ 3 := by
    rw [← hpoly]
    exact hsym
  rw [cubic_comp_reflect_expansion] at heq
  have h3 : -(f.coeff 3) = f.coeff 3 := by
    have h := congrArg (fun q : Polynomial ℤ => q.coeff 3) heq
    simpa only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, ite_false, ite_true, Nat.reduceEqDiff, zero_add, add_zero] using h
  have h3zero : f.coeff 3 = 0 := by omega
  have h1 : -(f.coeff 1) + 2 * k * f.coeff 2 - 3 * k ^ 2 * f.coeff 3 = f.coeff 1 := by
    have h := congrArg (fun q : Polynomial ℤ => q.coeff 1) heq
    simpa only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, ite_false, ite_true, Nat.reduceEqDiff, zero_add, add_zero] using h
  have h1formula : f.coeff 1 = k * f.coeff 2 := by
    rw [h3zero] at h1
    nlinarith [h1]
  calc
    f = Polynomial.C (f.coeff 0) + Polynomial.C (f.coeff 1) * Polynomial.X +
        Polynomial.C (f.coeff 2) * Polynomial.X ^ 2 +
          Polynomial.C (f.coeff 3) * Polynomial.X ^ 3 := hpoly
    _ = Polynomial.C (f.coeff 0) +
        Polynomial.C (f.coeff 2) * (Polynomial.C k * Polynomial.X + Polynomial.X ^ 2) := by
      rw [h3zero, h1formula, Polynomial.C_mul]
      simp
      ring

private lemma RemainderR_odd_closed_form (k : ℕ) :
    RemainderR (2 * k + 1) = Polynomial.C (hN (2 * k + 1) : ℤ) +
      Polynomial.C ((RemainderR (2 * k + 1)).coeff 2) *
        (Polynomial.C (((2 * k + 1 : ℕ) : ℤ) + 1) * Polynomial.X + Polynomial.X ^ 2) := by
  have hconst : (RemainderR (2 * k + 1)).coeff 0 = (hN (2 * k + 1) : ℤ) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, RemainderR_eval_zero_eq_hN]
  have h := invariant_cubic_formula (RemainderR (2 * k + 1))
    (((2 * k + 1 : ℕ) : ℤ) + 1) (RemainderR_natDegree_lt_four _)
    (by simpa [reflect] using RemainderR_comp_reflect_odd k)
  rw [hconst] at h
  exact h

private lemma cN_sub_hN_eq_odd_remainder_coeff (k : ℕ) :
    (cN (2 * k + 1) : ℤ) - (hN (2 * k + 1) : ℤ) =
      ((2 * k + 1 : ℕ) : ℤ) * (2 * ((2 * k + 1 : ℕ) : ℤ) + 1) *
        (RemainderR (2 * k + 1)).coeff 2 := by
  have hform := RemainderR_odd_closed_form k
  have heval := congrArg (fun q : Polynomial ℤ => q.eval ((2 * k + 1 : ℕ) : ℤ)) hform
  rw [RemainderR_eval_r_eq_cN] at heval
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow] at heval
  ring_nf at heval ⊢
  linarith


end

end Erdos291
