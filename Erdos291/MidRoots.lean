import Erdos291.MidResultant
import Erdos291.MidBlockRestrictions
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Erdős #291 — root characterization of middle polynomials

For a prime `p` the distance polynomial `P p d` splits over `ZMod p` with roots
`-1, …, -d`, and the reciprocal interval product `intervalProduct p a b` is
`∏_{j=a}^b (X - j)`.  This file proves the root/product identities that connect
the middle polynomials `Q p r` and `Q p (p-1-2r)` to the harmonic sums
`harmonicSum p β`, and uses them to reduce the middle resultant to a resultant
between `Q p r` and the derivative of the tail product.
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The interval product `∏_{j=a}^b (X - j)` over `ZMod p`. -/
noncomputable def intervalProduct (p a b : ℕ) : Polynomial (ZMod p) :=
  ∏ j ∈ Finset.Icc a b, (Polynomial.X - Polynomial.C (j : ZMod p))

/-- The plus product `∏_{j=a}^b (X + j)` over `ZMod p`. -/
noncomputable def plusProduct (p a b : ℕ) : Polynomial (ZMod p) :=
  ∏ j ∈ Finset.Icc a b, (Polynomial.X + Polynomial.C (j : ZMod p))

/-- The tail product `∏_{j=r+1}^e (X + j)` used in the middle decomposition. -/
noncomputable def midTailProduct (p r e : ℕ) : Polynomial (ZMod p) :=
  plusProduct p (r + 1) e

/-- `plusProduct p 1 d` is definitionally `P p d`. -/
lemma plusProduct_one_eq_P (p d : ℕ) : plusProduct p 1 d = P p d := by
  rfl

/-- `P p d` is definitionally `plusProduct p 1 d`. -/
lemma P_eq_plusProduct_one (p d : ℕ) : P p d = plusProduct p 1 d := by
  rfl

/-- `intervalProduct` factors are monic. -/
lemma intervalProduct_monic (p a b : ℕ) : (intervalProduct p a b).Monic := by
  rw [intervalProduct]
  exact monic_prod_of_monic _ _ fun i hi => monic_X_sub_C (i : ZMod p)

/-- `plusProduct` factors are monic. -/
lemma plusProduct_monic (p a b : ℕ) : (plusProduct p a b).Monic := by
  rw [plusProduct]
  exact monic_prod_of_monic _ _ fun i hi => monic_X_add_C (i : ZMod p)

/-- `midTailProduct` factors are monic. -/
lemma midTailProduct_monic (p r e : ℕ) : (midTailProduct p r e).Monic := by
  rw [midTailProduct]
  exact plusProduct_monic p (r + 1) e

/-- The degree of `intervalProduct p a b`. -/
lemma intervalProduct_natDegree (p a b : ℕ) [Nontrivial (ZMod p)] :
    (intervalProduct p a b).natDegree = b + 1 - a := by
  rw [intervalProduct]
  have hmonic : ∀ i ∈ Finset.Icc a b, Monic (Polynomial.X - Polynomial.C (i : ZMod p)) := by
    intro i hi
    exact monic_X_sub_C (i : ZMod p)
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc a b)
    (fun i => Polynomial.X - Polynomial.C (i : ZMod p)) hmonic]
  simp only [Polynomial.natDegree_X_sub_C]
  rw [← Finset.card_eq_sum_ones, Nat.card_Icc]

/-- The degree of `plusProduct p a b`. -/
lemma plusProduct_natDegree (p a b : ℕ) [Nontrivial (ZMod p)] :
    (plusProduct p a b).natDegree = b + 1 - a := by
  rw [plusProduct]
  have hmonic : ∀ i ∈ Finset.Icc a b, Monic (Polynomial.X + Polynomial.C (i : ZMod p)) := by
    intro i hi
    exact monic_X_add_C (i : ZMod p)
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc a b)
    (fun i => Polynomial.X + Polynomial.C (i : ZMod p)) hmonic]
  simp only [Polynomial.natDegree_X_add_C]
  rw [← Finset.card_eq_sum_ones, Nat.card_Icc]

/-! ## Priority 1: root/product structure -/

/-- The product `∏_{j=1}^{p-1} (X + j)` equals `X^(p-1) - 1` over `ZMod p`. -/
lemma plusProduct_one_pred_eq_X_pow_pred_sub_one (p : ℕ) [Fact p.Prime] :
    plusProduct p 1 (p - 1) = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
  let q : Polynomial (ZMod p) := (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1
  have hp : Nat.Prime p := Fact.out
  have hp_ge_two : 2 ≤ p := hp.two_le
  have hn_pos : 0 < p - 1 := by omega
  have hq_monic : q.Monic := by
    dsimp [q]
    exact monic_X_pow_sub_C (1 : ZMod p) (by omega : p - 1 ≠ 0)
  have hq_deg : q.natDegree = p - 1 := by
    dsimp [q]
    change ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) -
      Polynomial.C (1 : ZMod p)).natDegree = p - 1
    rw [Polynomial.natDegree_X_pow_sub_C]
  let S : Finset (ZMod p) := (Finset.Icc 1 (p - 1)).image (fun n : ℕ => (n : ZMod p))
  have hS_card : S.card = p - 1 := by
    dsimp [S]
    rw [Finset.card_image_of_injOn]
    · rw [Nat.card_Icc]
      omega
    · intro x hx y hy hxy
      have hx' : 1 ≤ x ∧ x ≤ p - 1 := Finset.mem_Icc.mp hx
      have hy' : 1 ≤ y ∧ y ≤ p - 1 := Finset.mem_Icc.mp hy
      have hx_lt : x < p := by omega
      have hy_lt : y < p := by omega
      have hmod : x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
      rwa [Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt] at hmod
  have hq_ne : q ≠ 0 := by
    dsimp [q]
    exact X_pow_sub_C_ne_zero hn_pos (1 : ZMod p)
  have hroots : ∀ x ∈ S, Polynomial.eval x q = 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    have hn' : 1 ≤ n ∧ n ≤ p - 1 := Finset.mem_Icc.mp hn
    have hn_lt : n < p := by omega
    have hn_ne : (n : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp hz
      exact (not_lt_of_ge (Nat.le_of_dvd hn'.1 hdvd)) hn_lt
    have hnpow : (n : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hn_ne
    dsimp [q]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    rw [hnpow]
    simp
  have hq_roots : q.roots = S.val := by
    refine roots_eq_of_natDegree_le_card_of_ne_zero (p := q) (S := S) hroots ?_ hq_ne
    rw [hq_deg, hS_card]
  have hq_prod : (q.roots.map fun a => Polynomial.X - Polynomial.C a).prod = q := by
    apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hq_monic
    rw [hq_roots]
    rw [← Finset.card_def S]
    rw [hS_card, hq_deg]
  have hprod_roots : (q.roots.map fun a => Polynomial.X - Polynomial.C a).prod =
      ∏ x ∈ S, (Polynomial.X - Polynomial.C x) := by
    rw [hq_roots]
    rfl
  have hprod_S : (∏ x ∈ S, (Polynomial.X - Polynomial.C x)) =
      ∏ i ∈ Finset.Icc 1 (p - 1), (Polynomial.X - Polynomial.C (i : ZMod p)) := by
    dsimp [S]
    rw [Finset.prod_image]
    intro x hx y hy hxy
    have hx' : 1 ≤ x ∧ x ≤ p - 1 := Finset.mem_Icc.mp hx
    have hy' : 1 ≤ y ∧ y ≤ p - 1 := Finset.mem_Icc.mp hy
    have hx_lt : x < p := by omega
    have hy_lt : y < p := by omega
    have hmod : x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    rwa [Nat.mod_eq_of_lt hx_lt, Nat.mod_eq_of_lt hy_lt] at hmod
  have hreindex : (∏ i ∈ Finset.Icc 1 (p - 1), (Polynomial.X - Polynomial.C (i : ZMod p))) =
      ∏ i ∈ Finset.Icc 1 (p - 1), (Polynomial.X + Polynomial.C (i : ZMod p)) := by
    classical
    refine Finset.prod_bij (fun i hi => p - i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc]
      have hi' : 1 ≤ i ∧ i ≤ p - 1 := Finset.mem_Icc.mp hi
      omega
    · intro i₁ hi₁ i₂ hi₂ h
      have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ p - 1 := Finset.mem_Icc.mp hi₁
      have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ p - 1 := Finset.mem_Icc.mp hi₂
      omega
    · intro j hj
      have hj' : 1 ≤ j ∧ j ≤ p - 1 := Finset.mem_Icc.mp hj
      refine ⟨p - j, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        omega
      · omega
    · intro i hi
      have hi' : 1 ≤ i ∧ i ≤ p - 1 := Finset.mem_Icc.mp hi
      have hip : i ≤ p := by omega
      have hcast : ((p - i : ℕ) : ZMod p) = -((i : ℕ) : ZMod p) := by
        rw [Nat.cast_sub hip]
        simp
      change Polynomial.X - Polynomial.C ((i : ℕ) : ZMod p)
          = Polynomial.X + Polynomial.C (((p - i : ℕ) : ZMod p))
      rw [hcast, Polynomial.C_neg, sub_eq_add_neg]
  calc
    plusProduct p 1 (p - 1) = ∏ i ∈ Finset.Icc 1 (p - 1),
        (Polynomial.X + Polynomial.C (i : ZMod p)) := by rfl
    _ = ∏ i ∈ Finset.Icc 1 (p - 1), (Polynomial.X - Polynomial.C (i : ZMod p)) := by
        rw [← hreindex]
    _ = ∏ x ∈ S, (Polynomial.X - Polynomial.C x) := by
        rw [← hprod_S]
    _ = (q.roots.map fun a => Polynomial.X - Polynomial.C a).prod := by
        rw [← hprod_roots]
    _ = q := hq_prod
    _ = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by rfl

/-- `P p (p - 1) = X^(p-1) - 1` over `ZMod p`. -/
lemma P_p_pred_eq_X_pow_pred_sub_one (p : ℕ) [Fact p.Prime] :
    P p (p - 1) = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
  rw [← plusProduct_one_eq_P]
  exact plusProduct_one_pred_eq_X_pow_pred_sub_one p

/-- Split an `Icc` product at `c`: `∏_{i=a}^b f i = (∏_{i=a}^c f i) * ∏_{i=c+1}^b f i`. -/
lemma prod_Icc_split_add {M : Type*} [CommMonoid M] (f : ℕ → M) {a b c : ℕ}
    (hac : a ≤ c + 1) (hcb : c ≤ b) :
    (∏ i ∈ Finset.Icc a c, f i) * (∏ i ∈ Finset.Icc (c + 1) b, f i) =
      ∏ i ∈ Finset.Icc a b, f i := by
  classical
  have hIcc : Finset.Icc a b = Finset.Icc a c ∪ Finset.Icc (c + 1) b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc a c) (Finset.Icc (c + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hx1 : x ≤ c := (Finset.mem_Icc.mp hx).2
    have hx2 : c + 1 ≤ x := (Finset.mem_Icc.mp hx').1
    omega
  rw [hIcc, Finset.prod_union hdisj]

/-- The tail product reindexed: `∏_{i=e+1}^{p-1} (X + i) = ∏_{j=1}^{2r} (X - j)` when
`e = p - 1 - 2r`. -/
lemma plusProduct_tail_eq_intervalProduct (p r e : ℕ) [Fact p.Prime]
    (he : e = p - 1 - 2 * r) (h2r : 2 * r < p) :
    (∏ i ∈ Finset.Icc (e + 1) (p - 1), (Polynomial.X + Polynomial.C (i : ZMod p))) =
      intervalProduct p 1 (2 * r) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp.pos
  rw [intervalProduct]
  refine Finset.prod_bij (fun i hi => p - i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    have hi' : e + 1 ≤ i ∧ i ≤ p - 1 := Finset.mem_Icc.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    have hi₁' : e + 1 ≤ i₁ ∧ i₁ ≤ p - 1 := Finset.mem_Icc.mp hi₁
    have hi₂' : e + 1 ≤ i₂ ∧ i₂ ≤ p - 1 := Finset.mem_Icc.mp hi₂
    omega
  · intro j hj
    have hj' : 1 ≤ j ∧ j ≤ 2 * r := Finset.mem_Icc.mp hj
    refine ⟨p - j, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    have hi' : e + 1 ≤ i ∧ i ≤ p - 1 := Finset.mem_Icc.mp hi
    have hip : i ≤ p := by omega
    have hcast : ((p - i : ℕ) : ZMod p) = -((i : ℕ) : ZMod p) := by
      rw [Nat.cast_sub hip]
      simp
    change Polynomial.X + Polynomial.C ((i : ℕ) : ZMod p)
        = Polynomial.X - Polynomial.C (((p - i : ℕ) : ZMod p))
    rw [hcast, Polynomial.C_neg, sub_eq_add_neg, neg_neg]

/-- `P p e` times the interval product `∏_{j=1}^{2r} (X - j)` equals `X^(p-1) - 1`, where
`e = p - 1 - 2r`. -/
lemma P_e_mul_R_eq_X_pow_pred_sub_one (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) :
    P p (p - 1 - 2 * r) * intervalProduct p 1 (2 * r) =
      (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
  let e : ℕ := p - 1 - 2 * r
  have hp : Nat.Prime p := Fact.out
  have hp_ge_two : 2 ≤ p := hp.two_le
  have h1e : 1 ≤ e + 1 := by omega
  have he_le : e ≤ p - 1 := by dsimp [e]; omega
  have hsplit := prod_Icc_split_add (fun i : ℕ => Polynomial.X + Polynomial.C (i : ZMod p))
    (a := 1) (b := p - 1) (c := e) (by omega : 1 ≤ e + 1) he_le
  calc
    P p (p - 1 - 2 * r) * intervalProduct p 1 (2 * r)
        = (∏ i ∈ Finset.Icc 1 e, (Polynomial.X + Polynomial.C (i : ZMod p))) *
            intervalProduct p 1 (2 * r) := by rfl
    _ = (∏ i ∈ Finset.Icc 1 e, (Polynomial.X + Polynomial.C (i : ZMod p))) *
            (∏ i ∈ Finset.Icc (e + 1) (p - 1), (Polynomial.X + Polynomial.C (i : ZMod p))) := by
          rw [plusProduct_tail_eq_intervalProduct p r e rfl h2r]
    _ = ∏ i ∈ Finset.Icc 1 (p - 1), (Polynomial.X + Polynomial.C (i : ZMod p)) := by
          rw [hsplit]
    _ = P p (p - 1) := by rfl
    _ = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
          exact P_p_pred_eq_X_pow_pred_sub_one p

/-- The derivative of `X^(p-1) - 1` is `-X^(p-2)` over `ZMod p`. -/
lemma derivative_X_pow_pred_sub_one (p : ℕ) [Fact p.Prime] :
    Polynomial.derivative ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) =
      -((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2)) := by
  have hp : Nat.Prime p := Fact.out
  have hp_ge_two : 2 ≤ p := hp.two_le
  have hcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    simp
  rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero]
  rw [Polynomial.derivative_X_pow]
  rw [hcast]
  simp [show p - 1 - 1 = p - 2 by omega]

/-- Differentiating `P_e * R = X^(p-1) - 1` gives the key identity
`Q_e * R^2 = -X^(p-2) * R - (X^(p-1) - 1) * R'`. -/
lemma Q_e_mul_R_sq_eq_neg_X_pow_pred_two_mul_R_sub_mul_derivative
    (p r : ℕ) [Fact p.Prime] (h2r : 2 * r < p) :
    Q p (p - 1 - 2 * r) * intervalProduct p 1 (2 * r) ^ 2 =
      -((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2) * intervalProduct p 1 (2 * r))
      - ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) *
          Polynomial.derivative (intervalProduct p 1 (2 * r)) := by
  let e : ℕ := p - 1 - 2 * r
  let R : Polynomial (ZMod p) := intervalProduct p 1 (2 * r)
  have hP := P_e_mul_R_eq_X_pow_pred_sub_one p r h2r
  have hder := congrArg Polynomial.derivative hP
  have hder_lhs : Polynomial.derivative (P p e * R) = Q p e * R + P p e * Polynomial.derivative R := by
    rw [Polynomial.derivative_mul]
    rfl
  have hder_rhs : Polynomial.derivative ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) =
      -((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2)) := by
    exact derivative_X_pow_pred_sub_one p
  have hmain : Q p e * R + P p e * Polynomial.derivative R =
      -((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2)) := by
    rw [hder_lhs, hder_rhs] at hder
    exact hder
  have hsub : P p e * R = (Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1 := by
    simpa [e, R] using hP
  calc
    Q p e * R ^ 2
        = (Q p e * R + P p e * Polynomial.derivative R) * R -
            (P p e * R) * Polynomial.derivative R := by ring
    _ = (-((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2))) * R -
            ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) * Polynomial.derivative R := by
          rw [hmain, hsub]
    _ = -((Polynomial.X : Polynomial (ZMod p)) ^ (p - 2) * R) -
            ((Polynomial.X : Polynomial (ZMod p)) ^ (p - 1) - 1) * Polynomial.derivative R := by
          ring

/-- Evaluating the key identity at a nonzero `x` outside `[1, 2r]` gives
`eval Q_e * (x * eval R) = -1`. -/
lemma eval_Q_p_e_mul_x_mul_R_eq_neg_one (p r x : ℕ) [Fact p.Prime]
    (h2r : 2 * r < p) (hxlt : x < p) (hx0 : (x : ZMod p) ≠ 0)
    (hxnot : x ∉ Finset.Icc 1 (2 * r)) :
    Polynomial.eval (x : ZMod p) (Q p (p - 1 - 2 * r)) *
      ((x : ZMod p) * Polynomial.eval (x : ZMod p) (intervalProduct p 1 (2 * r))) = -1 := by
  let e : ℕ := p - 1 - 2 * r
  let R : Polynomial (ZMod p) := intervalProduct p 1 (2 * r)
  have hp : Nat.Prime p := Fact.out
  have hp_ge_two : 2 ≤ p := hp.two_le
  have hxpow : (x : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have hxpow2 : (x : ZMod p) * (x : ZMod p) ^ (p - 2) = 1 := by
    rw [← pow_succ']
    have h : p - 2 + 1 = p - 1 := by omega
    rw [h]
    exact hxpow
  have hR_ne : Polynomial.eval (x : ZMod p) R ≠ 0 := by
    dsimp [R, intervalProduct]
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ 2 * r := Finset.mem_Icc.mp hj
    have hj_lt : j < p := by omega
    have hxj : (x : ZMod p) ≠ (j : ZMod p) := by
      intro hxeq
      have hmod : x % p = j % p := (ZMod.natCast_eq_natCast_iff' x j p).mp hxeq
      have hxlt' : x < p := hxlt
      have heq : x = j := by
        rwa [Nat.mod_eq_of_lt hxlt', Nat.mod_eq_of_lt hj_lt] at hmod
      apply hxnot
      rw [Finset.mem_Icc]
      omega
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero_of_ne hxj
  have hkey := congrArg (fun t : Polynomial (ZMod p) => Polynomial.eval (x : ZMod p) t)
    (Q_e_mul_R_sq_eq_neg_X_pow_pred_two_mul_R_sub_mul_derivative p r h2r)
  have hE : Polynomial.eval (x : ZMod p) (Q p e) * (Polynomial.eval (x : ZMod p) R) ^ 2 =
      -((x : ZMod p) ^ (p - 2) * Polynomial.eval (x : ZMod p) R) := by
    have hE' := hkey
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hE'
    rw [Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_mul] at hE'
    rw [Polynomial.eval_mul, Polynomial.eval_pow] at hE'
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hE'
    rw [hxpow] at hE'
    simpa [e, R] using hE'
  have hcancel : Polynomial.eval (x : ZMod p) (Q p e) * Polynomial.eval (x : ZMod p) R =
      -((x : ZMod p) ^ (p - 2)) := by
    apply mul_right_cancel₀ hR_ne
    calc
      (Polynomial.eval (x : ZMod p) (Q p e) * Polynomial.eval (x : ZMod p) R) *
          Polynomial.eval (x : ZMod p) R
          = Polynomial.eval (x : ZMod p) (Q p e) *
              (Polynomial.eval (x : ZMod p) R * Polynomial.eval (x : ZMod p) R) := by ring
      _ = Polynomial.eval (x : ZMod p) (Q p e) *
              (Polynomial.eval (x : ZMod p) R) ^ 2 := by ring
      _ = -((x : ZMod p) ^ (p - 2) * Polynomial.eval (x : ZMod p) R) := hE
      _ = (-((x : ZMod p) ^ (p - 2))) * Polynomial.eval (x : ZMod p) R := by ring
  calc
    Polynomial.eval (x : ZMod p) (Q p e) *
        ((x : ZMod p) * Polynomial.eval (x : ZMod p) R)
        = (x : ZMod p) * (Polynomial.eval (x : ZMod p) (Q p e) *
            Polynomial.eval (x : ZMod p) R) := by ring
    _ = (x : ZMod p) * (-((x : ZMod p) ^ (p - 2))) := by rw [hcancel]
    _ = -((x : ZMod p) * (x : ZMod p) ^ (p - 2)) := by ring
    _ = -1 := by rw [hxpow2]
    _ = (-1 : ZMod p) := by simp

/-- `eval 0 (Q p e) = 0 ↔ H_{2r} = 0` for a middle pair. -/
lemma eval_zero_Q_p_e_eq_zero_iff_harmonicSum_two_mul_r_eq_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 2 * r + 1 < p) :
    Polynomial.eval (0 : ZMod p) (Q p (p - 1 - 2 * r)) = 0 ↔ harmonicSum p (2 * r) = 0 := by
  let e : ℕ := p - 1 - 2 * r
  have hp : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := by
    have h1r : 1 ≤ r := mem_E_ge_one p r hrE
    omega
  have he_lt : e < p := by dsimp [e]; omega
  have h2rle : 2 * r ≤ p - 1 := by omega
  have hsym : harmonicSum p e = harmonicSum p (2 * r) := by
    have h := harmonicSum_two_mul_r_eq_harmonicSum_pred_sub_two_mul_r p r hp3 h2rle
    dsimp [e]
    exact h.symm
  have hfact_ne : (Nat.factorial e : ZMod p) ≠ 0 := by
    intro hz
    have hpdvd : p ∣ Nat.factorial e := (ZMod.natCast_eq_zero_iff (Nat.factorial e) p).mp hz
    have hp_le : p ≤ e := (hp.dvd_factorial).mp hpdvd
    dsimp [e] at hp_le
    omega
  have heval : Polynomial.eval (0 : ZMod p) (Q p e) =
      (Nat.factorial e : ZMod p) * harmonicSum p e := by
    simpa [e] using eval_zero_Q_eq_factorial_mul_harmonic p e he_lt
  constructor
  · intro h
    rw [heval] at h
    rcases mul_eq_zero.mp h with hf | hH
    · exact (hfact_ne hf).elim
    · rwa [hsym] at hH
  · intro h
    rw [heval]
    rw [hsym, h]
    simp

/-- `eval β (Q p r) = eval β (P p r) * (H_{β+r} - H_β)` for `β ∈ [1, 2r]`. -/
lemma eval_Q_p_r_eq_P_r_mul_sub (p r β : ℕ) [Fact p.Prime]
    (hβ : β ∈ Finset.Icc 1 (2 * r)) (hβr : β + r < p) :
    Polynomial.eval (β : ZMod p) (Q p r) =
      Polynomial.eval (β : ZMod p) (P p r) * (harmonicSum p (β + r) - harmonicSum p β) := by
  have hp : Nat.Prime p := Fact.out
  have hβ' : 1 ≤ β ∧ β ≤ 2 * r := Finset.mem_Icc.mp hβ
  have hunits : ∀ i ∈ Finset.Icc 1 r, IsUnit (((β + i : ℕ) : ZMod p)) := by
    intro i hi
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hge : 1 ≤ β + i := by omega
    have hle : β + i ≤ β + r := by omega
    have hlt : β + i < p := lt_of_le_of_lt hle hβr
    exact (not_lt_of_ge (Nat.le_of_dvd hge hdvd)) hlt
  have hprod : (∏ i ∈ Finset.Icc 1 r, (((β + i : ℕ) : ZMod p))) =
      Polynomial.eval (β : ZMod p) (P p r) := by
    rw [P, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_add]
  have hsum : (∑ i ∈ Finset.Icc 1 r, (((β + i : ℕ) : ZMod p)⁻¹)) =
      harmonicSum p (β + r) - harmonicSum p β := by
    have hreindex : (∑ i ∈ Finset.Icc 1 r, (((β + i : ℕ) : ZMod p)⁻¹)) =
        (∑ j ∈ Finset.Icc (β + 1) (β + r), ((j : ZMod p)⁻¹)) := by
      refine Finset.sum_bij (fun i hi => β + i) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_Icc]
        have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        omega
      · intro j hj
        have hj' : β + 1 ≤ j ∧ j ≤ β + r := Finset.mem_Icc.mp hj
        refine ⟨j - β, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      · intro i hi
        rfl
    rw [hreindex]
    exact (harmonicSum_sub_eq_sum_inv_Icc p β r hβr).symm
  rw [eval_Q_eq_sum_prod_erase]
  rw [sum_prod_erase_eq_mul_inv (Finset.Icc 1 r) (fun i => (((β + i : ℕ) : ZMod p))) hunits]
  rw [hprod, hsum]

/-- `eval β (Q p e) = eval β (P p e) * (H_{2r-β} - H_β)` for `β ∈ [1, 2r]`. -/
lemma eval_Q_p_e_eq_P_e_mul_sub (p r x : ℕ) [Fact p.Prime]
    (h2r : 2 * r < p) (hx : x ∈ Finset.Icc 1 (2 * r)) :
    Polynomial.eval (x : ZMod p) (Q p (p - 1 - 2 * r)) =
      Polynomial.eval (x : ZMod p) (P p (p - 1 - 2 * r)) *
        (harmonicSum p (2 * r - x) - harmonicSum p x) := by
  let e : ℕ := p - 1 - 2 * r
  have hp : Nat.Prime p := Fact.out
  have hp3 : 3 ≤ p := by
    have hx' : 1 ≤ x ∧ x ≤ 2 * r := Finset.mem_Icc.mp hx
    have hr1 : 1 ≤ r := by omega
    omega
  have hx' : 1 ≤ x ∧ x ≤ 2 * r := Finset.mem_Icc.mp hx
  have hxe_lt : x + e < p := by dsimp [e]; omega
  have hunits : ∀ i ∈ Finset.Icc 1 e, IsUnit (((x + i : ℕ) : ZMod p)) := by
    intro i hi
    have hi' : 1 ≤ i ∧ i ≤ e := Finset.mem_Icc.mp hi
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hge : 1 ≤ x + i := by omega
    have hle : x + i ≤ x + e := by omega
    have hlt : x + i < p := lt_of_le_of_lt hle hxe_lt
    exact (not_lt_of_ge (Nat.le_of_dvd hge hdvd)) hlt
  have hprod : (∏ i ∈ Finset.Icc 1 e, (((x + i : ℕ) : ZMod p))) =
      Polynomial.eval (x : ZMod p) (P p e) := by
    rw [P, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_add]
  have hsym : harmonicSum p (x + e) = harmonicSum p (2 * r - x) := by
    have hle : 2 * r - x ≤ p - 1 := by omega
    have h := sum_inv_Icc_sub_eq_sum_inv p (2 * r - x) hp3 hle
    unfold harmonicSum at h ⊢
    have harg : p - 1 - (2 * r - x) = x + e := by dsimp [e]; omega
    simpa [harg] using h
  have hsum : (∑ i ∈ Finset.Icc 1 e, (((x + i : ℕ) : ZMod p)⁻¹)) =
      harmonicSum p (2 * r - x) - harmonicSum p x := by
    have hreindex : (∑ i ∈ Finset.Icc 1 e, (((x + i : ℕ) : ZMod p)⁻¹)) =
        (∑ j ∈ Finset.Icc (x + 1) (x + e), ((j : ZMod p)⁻¹)) := by
      refine Finset.sum_bij (fun i hi => x + i) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_Icc]
        have hi' : 1 ≤ i ∧ i ≤ e := Finset.mem_Icc.mp hi
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        omega
      · intro j hj
        have hj' : x + 1 ≤ j ∧ j ≤ x + e := Finset.mem_Icc.mp hj
        refine ⟨j - x, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      · intro i hi
        rfl
    calc
      (∑ i ∈ Finset.Icc 1 e, (((x + i : ℕ) : ZMod p)⁻¹))
          = ∑ j ∈ Finset.Icc (x + 1) (x + e), ((j : ZMod p)⁻¹) := hreindex
      _ = harmonicSum p (x + e) - harmonicSum p x :=
          (harmonicSum_sub_eq_sum_inv_Icc p x e hxe_lt).symm
      _ = harmonicSum p (2 * r - x) - harmonicSum p x := by rw [hsym]
  rw [eval_Q_eq_sum_prod_erase]
  rw [sum_prod_erase_eq_mul_inv (Finset.Icc 1 e) (fun i => (((x + i : ℕ) : ZMod p))) hunits]
  rw [hprod, hsum]

/-- `eval x (P p e) ≠ 0` for `x ∈ [1, 2r]` (the factors `x + i` are all units). -/
lemma eval_P_e_ne_zero_of_mem_Icc_one_two_mul_r (p r x : ℕ) [Fact p.Prime]
    (h2r : 2 * r < p) (hx : x ∈ Finset.Icc 1 (2 * r)) :
    Polynomial.eval (x : ZMod p) (P p (p - 1 - 2 * r)) ≠ 0 := by
  let e : ℕ := p - 1 - 2 * r
  have hp : Nat.Prime p := Fact.out
  have hx' : 1 ≤ x ∧ x ≤ 2 * r := Finset.mem_Icc.mp hx
  rw [P, Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi' : 1 ≤ i ∧ i ≤ e := Finset.mem_Icc.mp hi
  have hge : 1 ≤ x + i := by omega
  have hle : x + i ≤ x + e := by omega
  have hlt : x + i < p := by omega
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.cast_add]
  intro hz
  have hpdvd : p ∣ x + i := (ZMod.natCast_eq_zero_iff (x + i) p).mp hz
  exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt

/-- `eval β (P p r) ≠ 0` for `β ∈ [1, 2r]` when `3r < p`. -/
lemma eval_P_r_ne_zero_of_mem_Icc_one_two_mul_r (p r β : ℕ) [Fact p.Prime]
    (h3r : 3 * r < p) (hβ : β ∈ Finset.Icc 1 (2 * r)) :
    Polynomial.eval (β : ZMod p) (P p r) ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have hβ' : 1 ≤ β ∧ β ≤ 2 * r := Finset.mem_Icc.mp hβ
  rw [P, Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
  have hge : 1 ≤ β + i := by omega
  have hle : β + i ≤ 3 * r := by omega
  have hlt : β + i < p := lt_of_le_of_lt hle h3r
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← Nat.cast_add]
  intro hz
  have hpdvd : p ∣ β + i := (ZMod.natCast_eq_zero_iff (β + i) p).mp hz
  exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt

/-- The F_p-valued common roots of `QrFactor` and `QeFactor` are exactly the common
harmonic solutions `H_β = H_{β+r} = H_{2r-β}`. -/
theorem Fp_common_root_iff_CR (p r β : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p)
    (hβ1 : 1 ≤ β) (hβ2 : β ≤ 2 * r) (hβne : β ≠ r) :
    (Polynomial.eval (β : ZMod p) (QrFactor p r) = 0 ∧
      Polynomial.eval (β : ZMod p) (QeFactor p r) = 0) ↔
      (harmonicSum p β = harmonicSum p (β + r) ∧
        harmonicSum p β = harmonicSum p (2 * r - β)) := by
  let e : ℕ := p - 1 - 2 * r
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have h3r : 3 * r < p := by omega
  have hβ_lt : β < p := by omega
  have hβIcc : β ∈ Finset.Icc 1 (2 * r) := by
    rw [Finset.mem_Icc]
    exact ⟨hβ1, hβ2⟩
  have hβr_lt : β + r < p := by omega
  have hβ_ne_zero : (β : ZMod p) ≠ 0 := by
    intro hz
    have hpdvd : p ∣ β := (ZMod.natCast_eq_zero_iff β p).mp hz
    exact (not_lt_of_ge (Nat.le_of_dvd hβ1 hpdvd)) hβ_lt
  have hβ_ne_r_mod : (β : ZMod p) ≠ (r : ZMod p) := by
    intro hz
    have hmod : β % p = r % p := (ZMod.natCast_eq_natCast_iff' β r p).mp hz
    have hβlt : β < p := hβ_lt
    have hrlt : r < p := hr_lt
    have heq : β = r := by
      rwa [Nat.mod_eq_of_lt hβlt, Nat.mod_eq_of_lt hrlt] at hmod
    exact hβne heq
  -- Factorization of `Q p r` by `X` and of `Q p e` by `X - C r`.
  have hroot0 : (Q p r).IsRoot 0 := by
    rw [Polynomial.IsRoot, eval_zero_Q_eq_factorial_mul_harmonic p r hr_lt,
      harmonicSum_middle_pair_zero p r hrE hr_lt, mul_zero]
  have hQr_mul : (Polynomial.X : Polynomial (ZMod p)) * QrFactor p r = Q p r := by
    have h := (mul_divByMonic_eq_iff_isRoot (p := Q p r) (a := (0 : ZMod p))).2 hroot0
    simpa [QrFactor] using h
  have hrootr : (Q p e).IsRoot (r : ZMod p) := by
    rw [Polynomial.IsRoot]
    dsimp [e]
    exact eval_Q_p_e_eq_zero_of_middle_pair p r hrE (by omega : 2 * r + 1 < p)
  have hQe_mul : (Polynomial.X - Polynomial.C (r : ZMod p)) * QeFactor p r = Q p e := by
    have h := (mul_divByMonic_eq_iff_isRoot (p := Q p e) (a := (r : ZMod p))).2 hrootr
    simpa [QeFactor] using h
  have hevalQr : Polynomial.eval (β : ZMod p) (Q p r) =
      (β : ZMod p) * Polynomial.eval (β : ZMod p) (QrFactor p r) := by
    rw [← hQr_mul, Polynomial.eval_mul, Polynomial.eval_X]
  have hevalQe : Polynomial.eval (β : ZMod p) (Q p e) =
      ((β : ZMod p) - (r : ZMod p)) * Polynomial.eval (β : ZMod p) (QeFactor p r) := by
    rw [← hQe_mul, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hF_iff_Qr : Polynomial.eval (β : ZMod p) (QrFactor p r) = 0 ↔
      Polynomial.eval (β : ZMod p) (Q p r) = 0 := by
    constructor
    · intro hF
      rw [hevalQr, hF, mul_zero]
    · intro hQ
      have hmul : (β : ZMod p) * Polynomial.eval (β : ZMod p) (QrFactor p r) = 0 := by
        rw [← hevalQr]
        exact hQ
      rcases mul_eq_zero.mp hmul with hβ0 | hF
      · exact (hβ_ne_zero hβ0).elim
      · exact hF
  have hG_iff_Qe : Polynomial.eval (β : ZMod p) (QeFactor p r) = 0 ↔
      Polynomial.eval (β : ZMod p) (Q p e) = 0 := by
    constructor
    · intro hG
      rw [hevalQe, hG, mul_zero]
    · intro hQ
      have hmul : ((β : ZMod p) - (r : ZMod p)) *
          Polynomial.eval (β : ZMod p) (QeFactor p r) = 0 := by
        rw [← hevalQe]
        exact hQ
      rcases mul_eq_zero.mp hmul with hβr0 | hG
      · have hsub : (β : ZMod p) - (r : ZMod p) = 0 := hβr0
        exact (hβ_ne_r_mod (sub_eq_zero.mp hsub)).elim
      · exact hG
  have hQr_iff_harm : Polynomial.eval (β : ZMod p) (Q p r) = 0 ↔
      harmonicSum p β = harmonicSum p (β + r) := by
    have hP_ne := eval_P_r_ne_zero_of_mem_Icc_one_two_mul_r p r β h3r hβIcc
    rw [eval_Q_p_r_eq_P_r_mul_sub p r β hβIcc hβr_lt]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hP0 | hsub
      · exact (hP_ne hP0).elim
      · exact (sub_eq_zero.mp hsub).symm
    · intro h
      rw [mul_eq_zero]
      right
      rw [h]
      simp
  have hQe_iff_harm : Polynomial.eval (β : ZMod p) (Q p e) = 0 ↔
      harmonicSum p β = harmonicSum p (2 * r - β) := by
    have h2r : 2 * r < p := by omega
    have hP_ne := eval_P_e_ne_zero_of_mem_Icc_one_two_mul_r p r β h2r hβIcc
    rw [eval_Q_p_e_eq_P_e_mul_sub p r β h2r hβIcc]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with hP0 | hsub
      · exact (hP_ne hP0).elim
      · exact (sub_eq_zero.mp hsub).symm
    · intro h
      rw [mul_eq_zero]
      right
      rw [h]
      simp
  constructor
  · intro h
    exact ⟨hQr_iff_harm.mp (hF_iff_Qr.mp h.1), hQe_iff_harm.mp (hG_iff_Qe.mp h.2)⟩
  · intro h
    exact ⟨hF_iff_Qr.mpr (hQr_iff_harm.mpr h.1), hG_iff_Qe.mpr (hQe_iff_harm.mpr h.2)⟩

/-! ## Priority 2: gcd/resultant reduction -/

/-- `P p e` factors as `P p r` times the tail product over `(r+1, e]`. -/
lemma P_e_eq_P_r_mul_midTailProduct (p r e : ℕ) (hr_le : r ≤ e) :
    P p e = P p r * midTailProduct p r e := by
  classical
  have hIcc : Finset.Icc 1 e = Finset.Icc 1 r ∪ Finset.Icc (r + 1) e := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 r) (Finset.Icc (r + 1) e) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hx1 : x ≤ r := (Finset.mem_Icc.mp hx).2
    have hx2 : r + 1 ≤ x := (Finset.mem_Icc.mp hx').1
    omega
  change (∏ i ∈ Finset.Icc 1 e, (Polynomial.X + Polynomial.C (i : ZMod p))) =
    (∏ i ∈ Finset.Icc 1 r, (Polynomial.X + Polynomial.C (i : ZMod p))) *
      (∏ i ∈ Finset.Icc (r + 1) e, (Polynomial.X + Polynomial.C (i : ZMod p)))
  rw [hIcc, Finset.prod_union hdisj]

/-- `Q p e = Q p r * S + P p r * S'` where `S` is the tail product. -/
lemma Q_e_eq_Q_r_mul_midTailProduct_add_P_r_mul_derivative (p r e : ℕ) (hr_le : r ≤ e) :
    Q p e = Q p r * midTailProduct p r e + P p r * Polynomial.derivative (midTailProduct p r e) := by
  have hP := P_e_eq_P_r_mul_midTailProduct p r e hr_le
  change Polynomial.derivative (P p e) = Q p r * midTailProduct p r e +
    P p r * Polynomial.derivative (midTailProduct p r e)
  rw [hP, Polynomial.derivative_mul]
  rfl

/-- `P p r` is separable: its roots `-1, …, -r` are distinct in `ZMod p` when `r < p`. -/
lemma P_separable (p r : ℕ) [Fact p.Prime] (hr : r < p) : (P p r).Separable := by
  classical
  have hp : Nat.Prime p := Fact.out
  rw [P]
  refine separable_prod' (ι := ℕ) (f := fun i : ℕ => Polynomial.X + Polynomial.C (i : ZMod p))
    (s := Finset.Icc 1 r) ?_ ?_
  · intro i hi j hj hij
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    have hj' : 1 ≤ j ∧ j ≤ r := Finset.mem_Icc.mp hj
    have hi_lt : i < p := lt_of_le_of_lt hi'.2 hr
    have hj_lt : j < p := lt_of_le_of_lt hj'.2 hr
    have hcij : (i : ZMod p) ≠ (j : ZMod p) := by
      intro hz
      have hmod : i % p = j % p := (ZMod.natCast_eq_natCast_iff' i j p).mp hz
      have heq : i = j := by
        rwa [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] at hmod
      exact hij heq
    have hneg : (-(i : ZMod p)) ≠ (-(j : ZMod p)) := by
      intro hneg
      exact hcij (neg_inj.mp hneg)
    have hfi : Polynomial.X + Polynomial.C (i : ZMod p) =
        Polynomial.X - Polynomial.C (-(i : ZMod p)) := by
      rw [Polynomial.C_neg, sub_eq_add_neg, neg_neg]
    have hfj : Polynomial.X + Polynomial.C (j : ZMod p) =
        Polynomial.X - Polynomial.C (-(j : ZMod p)) := by
      rw [Polynomial.C_neg, sub_eq_add_neg, neg_neg]
    rw [hfi, hfj]
    exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hneg).isUnit
  · intro i hi
    exact separable_X_add_C (i : ZMod p)

/-- `resultant (Q p r) (P p r) ≠ 0` in the intrinsic mid regime. -/
lemma resultant_Qr_Pr_ne_zero (p r : ℕ) [Fact p.Prime] (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (P p r) : ZMod p) ≠ 0 := by
  have hp : Nat.Prime p := Fact.out
  have hr_lt : r < p := by omega
  have hsep : (P p r).Separable := P_separable p r hr_lt
  have hcop : IsCoprime (P p r) (Q p r) := by
    simpa [Q, Separable] using hsep
  intro h0
  have hnotcop := (Polynomial.resultant_eq_zero_iff (f := Q p r) (g := P p r)).mp h0
  exact hnotcop.2 hcop.symm

/-- The middle resultant factors as `resultant (Q p r) (P p r)` times
`resultant (Q p r) (derivative (midTailProduct p r e))`. -/
lemma resultant_Qr_Qe_eq_resultant_Qr_Pr_mul_resultant_Qr_derivative_midTail
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) =
      (Polynomial.resultant (Q p r) (P p r) : ZMod p) *
        Polynomial.resultant (Q p r)
          (Polynomial.derivative (midTailProduct p r (p - 1 - 2 * r))) := by
  let e : ℕ := p - 1 - 2 * r
  let S : Polynomial (ZMod p) := midTailProduct p r e
  let T : Polynomial (ZMod p) := Polynomial.derivative S
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have he_ge : 1 ≤ e := by dsimp [e]; omega
  have he_lt : e < p := by dsimp [e]; omega
  have hre : r ≤ e := by dsimp [e]; omega
  have hd_pos : 0 < e - r := by dsimp [e]; omega
  have hd_lt : e - r < p := by dsimp [e]; omega
  have hQrdeg : (Q p r).natDegree = r - 1 := Q_natDegree p r h1r hr_lt
  have hQedeg : (Q p e).natDegree = e - 1 := Q_natDegree p e he_ge he_lt
  have hSdeg : S.natDegree = e - r := by
    dsimp [S, midTailProduct]
    rw [plusProduct_natDegree p (r + 1) e]
    omega
  have hSm : S.Monic := by dsimp [S]; exact midTailProduct_monic p r e
  have hS_ne : S ≠ 0 := hSm.ne_zero
  have hTle : T.natDegree ≤ e - r - 1 := by
    dsimp [T]
    exact (Polynomial.natDegree_derivative_le S).trans (by
      rw [hSdeg])
  have hd_ne : (e - r : ZMod p) ≠ 0 := by
    intro hz
    have hz' : ((e - r : ℕ) : ZMod p) = 0 := by
      simpa [Nat.cast_sub hre] using hz
    have hpdvd : p ∣ e - r := (ZMod.natCast_eq_zero_iff (e - r) p).mp hz'
    exact (not_lt_of_ge (Nat.le_of_dvd hd_pos hpdvd)) hd_lt
  have hcoeffS : coeff S (e - r) = 1 := by
    rw [← hSdeg, Polynomial.coeff_natDegree]
    exact hSm.leadingCoeff
  have hcoeffT : coeff T (e - r - 1) = (e - r : ZMod p) := by
    dsimp [T]
    have hd_succ : e - r - 1 + 1 = e - r := by omega
    calc
      coeff (Polynomial.derivative S) (e - r - 1)
          = coeff S (e - r - 1 + 1) * ((e - r - 1 + 1 : ℕ) : ZMod p) := by
              rw [Polynomial.coeff_derivative, Nat.cast_add, Nat.cast_one]
      _ = coeff S (e - r) * ((e - r : ℕ) : ZMod p) := by rw [hd_succ]
      _ = 1 * ((e - r : ℕ) : ZMod p) := by rw [hcoeffS]
      _ = (e - r : ZMod p) := by
          simp [Nat.cast_sub hre]
  have hcoeffT_ne : coeff T (e - r - 1) ≠ 0 := by
    rw [hcoeffT]
    exact hd_ne
  have hTdeg : T.natDegree = e - r - 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hTle hcoeffT_ne
  have hT_ne : T ≠ 0 := by
    intro hT0
    have hcoeff0 : coeff T (e - r - 1) = 0 := by rw [hT0, Polynomial.coeff_zero]
    exact hcoeffT_ne hcoeff0
  have hPdeg : (P p r).natDegree = r := P_natDegree p r
  have hPTdeg_add : (P p r * T).natDegree = (P p r).natDegree + T.natDegree :=
    (P_monic p r).natDegree_mul' hT_ne
  have hPTdeg : (P p r * T).natDegree = e - 1 := by
    rw [hPTdeg_add, hPdeg, hTdeg]
    omega
  have hp_add : S.natDegree + (Q p r).natDegree ≤ (P p r * T).natDegree := by
    rw [hSdeg, hQrdeg, hPTdeg]
    omega
  have hQe_decomp := Q_e_eq_Q_r_mul_midTailProduct_add_P_r_mul_derivative p r e hre
  have hQe' : Q p e = P p r * T + Q p r * S := by
    rw [hQe_decomp]
    ring
  have h_add := Polynomial.resultant_add_mul_right (f := Q p r) (g := P p r * T) (p := S)
    (m := (Q p r).natDegree) (n := (P p r * T).natDegree) hp_add le_rfl
  have hmain_add : Polynomial.resultant (Q p r) (Q p e) (Q p r).natDegree (P p r * T).natDegree =
      Polynomial.resultant (Q p r) (P p r * T) (Q p r).natDegree (P p r * T).natDegree := by
    rw [hQe']
    exact h_add
  have h_mul := Polynomial.resultant_mul_right (f := Q p r) (g₁ := P p r) (g₂ := T)
    (m := (Q p r).natDegree) le_rfl
  have hmain_mul : Polynomial.resultant (Q p r) (P p r * T) (Q p r).natDegree (P p r * T).natDegree =
      Polynomial.resultant (Q p r) (P p r) * Polynomial.resultant (Q p r) T := by
    rw [hPTdeg_add]
    simpa using h_mul
  have hmain : Polynomial.resultant (Q p r) (Q p e) =
      Polynomial.resultant (Q p r) (P p r) * Polynomial.resultant (Q p r) T := by
    have hmain' : Polynomial.resultant (Q p r) (Q p e) (Q p r).natDegree (P p r * T).natDegree =
        Polynomial.resultant (Q p r) (P p r) * Polynomial.resultant (Q p r) T := by
      rw [hmain_add, hmain_mul]
    simpa [hQedeg, hPTdeg] using hmain'
  simpa [e, S, T] using hmain

/-- The middle resultant vanishes iff `resultant (Q p r) (derivative (midTailProduct p r e))`
vanishes. -/
lemma resultant_Qr_Qe_eq_zero_iff_resultant_Qr_derivative_midTail_eq_zero
    (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    (Polynomial.resultant (Q p r) (Q p (p - 1 - 2 * r)) : ZMod p) = 0 ↔
      Polynomial.resultant (Q p r)
        (Polynomial.derivative (midTailProduct p r (p - 1 - 2 * r))) = 0 := by
  have h14 := resultant_Qr_Qe_eq_resultant_Qr_Pr_mul_resultant_Qr_derivative_midTail p r hrE hmid
  have h13 := resultant_Qr_Pr_ne_zero p r hmid
  constructor
  · intro h
    rw [h14] at h
    rcases mul_eq_zero.mp h with hP | hT
    · exact (h13 hP).elim
    · exact hT
  · intro h
    rw [h14, h, mul_zero]

/-! ## Priority 3: partial exclusions for small `β` -/

/-- The CR equation at `β = 1` would force `r = 0` in `ZMod p`, impossible. -/
lemma not_CR_beta_eq_one (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    harmonicSum p 1 = harmonicSum p (1 + r) → False := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have hr1_lt : r + 1 < p := by omega
  have h1 : harmonicSum p 1 = 1 := by
    simp [harmonicSum]
  have hsum : harmonicSum p (r + 1) = harmonicSum p r + ((r + 1 : ℕ) : ZMod p)⁻¹ := by
    have hsub := harmonicSum_sub_eq_sum_inv_Icc p r 1 hr1_lt
    calc
      harmonicSum p (r + 1) = harmonicSum p r + (harmonicSum p (r + 1) - harmonicSum p r) := by
        abel
      _ = harmonicSum p r + ∑ j ∈ Finset.Icc (r + 1) (r + 1), ((j : ZMod p)⁻¹) := by
        rw [hsub]
      _ = harmonicSum p r + ((r + 1 : ℕ) : ZMod p)⁻¹ := by simp
  have hr1_unit : IsUnit (((r + 1 : ℕ) : ZMod p)) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have hge : 1 ≤ r + 1 := by omega
    exact (not_lt_of_ge (Nat.le_of_dvd hge hd)) hr1_lt
  intro h
  have h_eq : 1 = harmonicSum p (r + 1) := by
    rw [h1] at h
    simpa [show 1 + r = r + 1 by omega] using h
  have h_inv_one : ((r + 1 : ℕ) : ZMod p)⁻¹ = 1 := by
    have h' := h_eq
    rw [hsum, harmonicSum_middle_pair_zero p r hrE hr_lt, zero_add] at h'
    exact h'.symm
  have h_r1 : ((r + 1 : ℕ) : ZMod p) = 1 := by
    have hmul := congrArg (fun t : ZMod p => ((r + 1 : ℕ) : ZMod p) * t) h_inv_one
    rw [mul_inv_cancel₀ hr1_unit.ne_zero, mul_one] at hmul
    exact hmul.symm
  have h_r0 : (r : ZMod p) = 0 := by
    have h' := congrArg (fun t : ZMod p => t - 1) h_r1
    simpa [Nat.cast_add, Nat.cast_one] using h'
  have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h_r0
  exact (not_lt_of_ge (Nat.le_of_dvd h1r hdvd)) hr_lt

/-- `H_{r-1} ≠ H_{r+1}` in the intrinsic mid regime: equality would force
`2r + 1 = 0` in `ZMod p`. -/
lemma harmonicSum_sub_one_ne_add_one (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    harmonicSum p (r - 1) = harmonicSum p (r + 1) → False := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  have hr1_lt : r + 1 < p := by omega
  have hsum_sub : harmonicSum p (r + 1) - harmonicSum p (r - 1) =
      ∑ j ∈ Finset.Icc (r - 1 + 1) (r - 1 + 2), ((j : ZMod p)⁻¹) := by
    simpa [show r - 1 + 2 = r + 1 by omega] using
      (harmonicSum_sub_eq_sum_inv_Icc p (r - 1) 2 (by omega : r - 1 + 2 < p))
  have hsum_two : (∑ j ∈ Finset.Icc (r - 1 + 1) (r - 1 + 2), ((j : ZMod p)⁻¹)) =
      ((r : ℕ) : ZMod p)⁻¹ + ((r + 1 : ℕ) : ZMod p)⁻¹ := by
    have harg1 : r - 1 + 1 = r := by omega
    have harg2 : r - 1 + 2 = r + 1 := by omega
    rw [harg1, harg2]
    rw [Finset.sum_Icc_succ_top (a := r) (b := r) (by omega) (fun j => ((j : ZMod p)⁻¹))]
    simp
  have hr_unit : IsUnit ((r : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact (not_lt_of_ge (Nat.le_of_dvd h1r hd)) hr_lt
  have hr1_unit : IsUnit (((r + 1 : ℕ) : ZMod p)) := by
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have hge : 1 ≤ r + 1 := by omega
    exact (not_lt_of_ge (Nat.le_of_dvd hge hd)) hr1_lt
  have hr_ne : (r : ZMod p) ≠ 0 := hr_unit.ne_zero
  have hr1_ne : ((r + 1 : ℕ) : ZMod p) ≠ 0 := hr1_unit.ne_zero
  intro h
  have hdiff_zero : harmonicSum p (r + 1) - harmonicSum p (r - 1) = 0 := by
    rw [h]
    simp
  have hsum_zero : ((r : ℕ) : ZMod p)⁻¹ + ((r + 1 : ℕ) : ZMod p)⁻¹ = 0 := by
    rw [← hsum_two]
    rw [← hsum_sub]
    exact hdiff_zero
  have hcross_zero : ((r : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p) *
        (((r : ℕ) : ZMod p)⁻¹ + ((r + 1 : ℕ) : ZMod p)⁻¹) = 0 := by
    rw [hsum_zero]
    simp
  have hcross_exp : ((r : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p) *
        (((r : ℕ) : ZMod p)⁻¹ + ((r + 1 : ℕ) : ZMod p)⁻¹)
        = ((r + 1 : ℕ) : ZMod p) + (r : ZMod p) := by
    rw [mul_add]
    have h1 : ((r : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p) * ((r : ℕ) : ZMod p)⁻¹
        = ((r + 1 : ℕ) : ZMod p) := by
      rw [mul_assoc, mul_comm (((r + 1 : ℕ) : ZMod p)) (((r : ℕ) : ZMod p)⁻¹),
        ← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul]
    have h2 : ((r : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p) * ((r + 1 : ℕ) : ZMod p)⁻¹
        = (r : ZMod p) := by
      rw [mul_assoc, mul_inv_cancel₀ hr1_ne, mul_one]
    rw [h1, h2]
  have hcast_zero : ((2 * r + 1 : ℕ) : ZMod p) = 0 := by
    have hsumcast : ((r + 1 : ℕ) : ZMod p) + (r : ZMod p) = 0 := by
      rw [← hcross_exp, hcross_zero]
    have hcomm : ((r + 1 : ℕ) : ZMod p) + (r : ZMod p) = ((2 * r + 1 : ℕ) : ZMod p) := by
      rw [show ((2 * r + 1 : ℕ) : ZMod p) = ((r + 1 : ℕ) : ZMod p) + (r : ZMod p) by
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring]
    rw [← hcomm, hsumcast]
  have hdvd : p ∣ 2 * r + 1 := (ZMod.natCast_eq_zero_iff (2 * r + 1) p).mp hcast_zero
  have hge : 1 ≤ 2 * r + 1 := by omega
  have hlt : 2 * r + 1 < p := by omega
  exact (not_lt_of_ge (Nat.le_of_dvd hge hdvd)) hlt

/-- The CR equation at `β = r - 1` would give `H_{r-1} = H_{r+1}`, impossible. -/
lemma not_CR_beta_r_sub_one (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    harmonicSum p (r - 1) = harmonicSum p (r + 1) → False := by
  exact harmonicSum_sub_one_ne_add_one p r hrE hmid

/-- The CR equation at `β = r + 1` would give `H_{r+1} = H_{r-1}`, impossible. -/
lemma not_CR_beta_r_add_one (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    harmonicSum p (r - 1) = harmonicSum p (r + 1) → False := by
  exact harmonicSum_sub_one_ne_add_one p r hrE hmid

end

end Erdos291
