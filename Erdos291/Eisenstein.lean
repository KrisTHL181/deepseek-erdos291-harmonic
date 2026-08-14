import Erdos291.Bernoulli
import Erdos291.DoubleCount
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.haveILetI false

/-!
# Erdős #291 — Eisenstein's congruence and the Wieferich middle-digit theorem (A1)

For an odd prime `p`, the "middle digit" `(p - 1) / 2` is a bad digit exactly when `p` is a
base-2 Wieferich prime, i.e. when `p ^ 2 ∣ 2 ^ (p - 1) - 1`. The proof is Eisenstein's
congruence: with `q = fermatQuotient p = (2 ^ (p - 1) - 1) / p` and `m = (p - 1) / 2`,

    ∑_{j = 1}^m j⁻¹ = -2 · q   (in `ZMod p`).

The route is the classical mod `p²` refinement of the binomial theorem for `2^(p-1) =
(1 + 1)^(p-1)`, followed by a double-count of the alternating harmonic sum.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

/-- The Fermat quotient `q_p(2) = (2^(p-1) - 1) / p`; an integer by Fermat's little theorem. -/
def fermatQuotient (p : ℕ) : ℕ := (2 ^ (p - 1) - 1) / p

/-- The integer `k! · H_k = ∑_{i=1}^k k!/i` (the "factorial harmonic number"). -/
def harmonicFactorial (k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 k, Nat.factorial k / i

/-! ## Fermat and the recurrence for `harmonicFactorial` -/

/-- Fermat's little theorem: for an odd prime `p`, `p ∣ 2^(p-1) - 1`. -/
lemma fermat_dvd (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : p ∣ 2 ^ (p - 1) - 1 := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  have hcop : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hodd
  exact Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card hp' (n := 2) hcop)

/-- `p * fermatQuotient p = 2^(p-1) - 1`. -/
lemma fermatQuotient_mul_self (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    p * fermatQuotient p = 2 ^ (p - 1) - 1 := by
  unfold fermatQuotient
  exact Nat.mul_div_cancel' (fermat_dvd p hp)

/-- The recurrence `harmonicFactorial (k+1) = (k+1)·harmonicFactorial k + k!`. -/
lemma harmonicFactorial_succ (k : ℕ) :
    harmonicFactorial (k + 1) = (k + 1) * harmonicFactorial k + Nat.factorial k := by
  unfold harmonicFactorial
  have hmain : (∑ x ∈ Finset.Icc 1 k, Nat.factorial (k + 1) / x) =
      (k + 1) * (∑ x ∈ Finset.Icc 1 k, Nat.factorial k / x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxle : x ≤ k := (Finset.mem_Icc.mp hx).2
    have hxpos : 0 < x := by
      have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
      omega
    have hdvd : x ∣ Nat.factorial k := Nat.dvd_factorial hxpos hxle
    rw [Nat.factorial_succ, Nat.mul_div_assoc (k + 1) hdvd]
  rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega : 1 ≤ k + 1)]
  rw [hmain]
  rw [Nat.factorial_succ, Nat.mul_div_cancel_left _ (by omega : 0 < k + 1)]

/-! ## The mod `p²` crux: `∏_{i=1}^k (p - i) ≡ (-1)^k (k! - p·k!·H_k)` -/

/-- `(p : ZMod (p^2)) * (p : ZMod (p^2)) = 0`. -/
lemma zmod_p_mul_p_eq_zero (p : ℕ) : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
  rw [← Nat.cast_mul, ← pow_two]
  exact ZMod.natCast_self (p ^ 2)

/-- `(p : ZMod (p^2)) ^ 2 = 0`. -/
lemma zmod_p_sq_eq_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self (p ^ 2)

/-- The exact ring identity `(P - a) * (b - P * c) = -(a * b - P * (a * c + b)) - P * P * c`. -/
lemma sub_mul_sub_identity {R : Type*} [CommRing R] (P a b c : R) :
    (P - a) * (b - P * c) = -(a * b - P * (a * c + b)) - P * P * c := by
  ring

/-- The descending factorial `(p-1)(p-2)⋯(p-k)` equals `(-1)^k (k! - p·k!·H_k)` modulo `p²`
(in `ZMod (p^2)`), for `k < p`. -/
lemma descFactorial_pred_eq_zmod (p k : ℕ) [Fact p.Prime] (_hp : 3 ≤ p) (hk : k < p) :
    (Nat.descFactorial (p - 1) k : ZMod (p ^ 2)) =
      ((-1 : ZMod (p ^ 2)) ^ k) *
        ((Nat.factorial k : ZMod (p ^ 2)) - (p : ZMod (p ^ 2)) *
          (harmonicFactorial k : ZMod (p ^ 2))) := by
  induction k with
  | zero => simp [harmonicFactorial]
  | succ k ih =>
      have hklt : k < p := by omega
      have ih' := ih hklt
      rw [Nat.descFactorial_succ, Nat.cast_mul]
      rw [show ((p - 1 - k : ℕ) : ZMod (p ^ 2)) =
          (p : ZMod (p ^ 2)) - (k + 1 : ZMod (p ^ 2)) by
        rw [show p - 1 - k = p - (k + 1) by omega]
        rw [Nat.cast_sub (by omega : k + 1 ≤ p)]
        simp]
      rw [ih']
      rw [harmonicFactorial_succ k, Nat.factorial_succ]
      have hpow : (-1 : ZMod (p ^ 2)) ^ (k + 1) =
          (-1 : ZMod (p ^ 2)) ^ k * (-1 : ZMod (p ^ 2)) := pow_succ (-1 : ZMod (p ^ 2)) k
      rw [hpow]
      push_cast
      ring_nf
      rw [zmod_p_sq_eq_zero p]
      ring

/-- Eisenstein's descending-factorial congruence, in integer `ZMOD (p^2)` form. -/
lemma choose_descFactorial_mod_p2 (p k : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hk : k < p) :
    (Nat.descFactorial (p - 1) k : ℤ) ≡
      ((-1 : ℤ) ^ k) * ((Nat.factorial k : ℤ) - (p : ℤ) * (harmonicFactorial k : ℤ))
        [ZMOD (p : ℤ) ^ 2] := by
  have h := descFactorial_pred_eq_zmod p k hp hk
  have h' : (((Nat.descFactorial (p - 1) k : ℤ) : ZMod (p ^ 2))) =
      ((((-1 : ℤ) ^ k) * ((Nat.factorial k : ℤ) - (p : ℤ) * (harmonicFactorial k : ℤ)) : ℤ) :
        ZMod (p ^ 2)) := by
    simpa using h
  have hm : ((Nat.descFactorial (p - 1) k : ℤ) ≡
      ((-1 : ℤ) ^ k) * ((Nat.factorial k : ℤ) - (p : ℤ) * (harmonicFactorial k : ℤ))
        [ZMOD (p ^ 2 : ℕ)]) := (ZMod.intCast_eq_intCast_iff _ _ (p ^ 2)).mp h'
  simpa [pow_two] using hm

/-! ## Summing the binomial refinement modulo `p²` -/

/-- For `k < p`, `Nat.factorial k` is coprime to `p²`. -/
lemma factorial_coprime_sq (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    Nat.Coprime (Nat.factorial k) (p ^ 2) := by
  have hp : Nat.Prime p := Fact.out
  have hcop : Nat.Coprime (Nat.factorial k) p := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (by
      intro hdvd
      have hle : p ≤ k := (Nat.Prime.dvd_factorial hp).mp hdvd
      omega)
  rw [pow_two]
  exact hcop.mul_right hcop

/-- For `k < p`, `k!` is a unit in `ZMod (p²)`. -/
lemma factorial_unit (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    IsUnit ((Nat.factorial k : ℕ) : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact factorial_coprime_sq p k hk

/-- `∑_{k < p} (-1)^k = 1` in any ring, for odd `p`. -/
lemma sum_neg_one_pow_range_odd {R : Type*} [Ring R] (p : ℕ) (hp : Odd p) :
    (∑ k ∈ Finset.range p, ((-1 : R) ^ k)) = 1 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => (-1 : R) ^ k)]
  simpa [Nat.not_even_iff_odd.mpr hp] using (Fin.sum_neg_one_pow R p)

/-- For `k < p`, `C(p-1,k) ≡ (-1)^k (1 - p·H_k) (mod p²)`, in `ZMod (p²)`. -/
lemma choose_pred_eq_zmod (p k : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (hk : k < p) :
    ((p - 1).choose k : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ k -
        (p : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
          ((Nat.factorial k : ZMod (p ^ 2))⁻¹)) := by
  have hd := descFactorial_pred_eq_zmod p k hp hk
  have hdesc : (Nat.descFactorial (p - 1) k : ZMod (p ^ 2)) =
      (Nat.factorial k : ZMod (p ^ 2)) * ((p - 1).choose k : ZMod (p ^ 2)) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hunit : IsUnit ((Nat.factorial k : ℕ) : ZMod (p ^ 2)) := factorial_unit p k hk
  have hinv : (Nat.factorial k : ZMod (p ^ 2))⁻¹ * (Nat.factorial k : ZMod (p ^ 2)) = 1 :=
    ZMod.inv_mul_of_unit (Nat.factorial k : ZMod (p ^ 2)) hunit
  have hmain : (Nat.factorial k : ZMod (p ^ 2)) * ((p - 1).choose k : ZMod (p ^ 2)) =
      (-1 : ZMod (p ^ 2)) ^ k * ((Nat.factorial k : ZMod (p ^ 2)) -
        (p : ZMod (p ^ 2)) * (harmonicFactorial k : ZMod (p ^ 2))) := by
    rw [← hdesc, hd]
  calc
    ((p - 1).choose k : ZMod (p ^ 2))
        = (Nat.factorial k : ZMod (p ^ 2))⁻¹ *
            ((Nat.factorial k : ZMod (p ^ 2)) * ((p - 1).choose k : ZMod (p ^ 2))) := by
            rw [← mul_assoc, hinv, one_mul]
    _ = (Nat.factorial k : ZMod (p ^ 2))⁻¹ *
            ((-1 : ZMod (p ^ 2)) ^ k * ((Nat.factorial k : ZMod (p ^ 2)) -
              (p : ZMod (p ^ 2)) * (harmonicFactorial k : ZMod (p ^ 2)))) := by
            rw [hmain]
    _ = (-1 : ZMod (p ^ 2)) ^ k -
          (p : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
            ((Nat.factorial k : ZMod (p ^ 2))⁻¹)) := by
            calc
              (Nat.factorial k : ZMod (p ^ 2))⁻¹ *
                  ((-1 : ZMod (p ^ 2)) ^ k * ((Nat.factorial k : ZMod (p ^ 2)) -
                    (p : ZMod (p ^ 2)) * (harmonicFactorial k : ZMod (p ^ 2))))
                  = (-1 : ZMod (p ^ 2)) ^ k *
                      ((Nat.factorial k : ZMod (p ^ 2))⁻¹ * (Nat.factorial k : ZMod (p ^ 2)) -
                        (Nat.factorial k : ZMod (p ^ 2))⁻¹ * (p : ZMod (p ^ 2)) *
                          (harmonicFactorial k : ZMod (p ^ 2))) := by ring
              _ = (-1 : ZMod (p ^ 2)) ^ k *
                      (1 - (p : ZMod (p ^ 2)) * (harmonicFactorial k : ZMod (p ^ 2)) *
                        ((Nat.factorial k : ZMod (p ^ 2))⁻¹)) := by
                    rw [hinv]
                    ring
              _ = (-1 : ZMod (p ^ 2)) ^ k -
                    (p : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
                      ((Nat.factorial k : ZMod (p ^ 2))⁻¹)) := by ring

/-- The binomial refinement, summed: `2^(p-1) - 1 ≡ -p · Σ (-1)^k k!·H_k·(k!)⁻¹ (mod p²)`. -/
lemma two_pow_pred_sub_one_eq_zmod (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((2 ^ (p - 1) - 1 : ℕ) : ZMod (p ^ 2)) =
      -(p : ZMod (p ^ 2)) *
        (∑ k ∈ Finset.range p,
          (-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
            ((Nat.factorial k : ZMod (p ^ 2))⁻¹)) := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  have hsum : ((2 ^ (p - 1) : ℕ) : ZMod (p ^ 2)) = ∑ k ∈ Finset.range p, ((p - 1).choose k : ZMod (p ^ 2)) := by
    rw [← Nat.sum_range_choose (p - 1), Nat.cast_sum]
    rw [show p - 1 + 1 = p by omega]
  calc
    ((2 ^ (p - 1) - 1 : ℕ) : ZMod (p ^ 2))
        = (∑ k ∈ Finset.range p, ((p - 1).choose k : ZMod (p ^ 2))) - 1 := by
            rw [Nat.cast_sub (Nat.one_le_pow' (p - 1) 1), hsum]
            norm_num
    _ = (∑ k ∈ Finset.range p, ((-1 : ZMod (p ^ 2)) ^ k -
            (p : ZMod (p ^ 2)) * ((-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
              ((Nat.factorial k : ZMod (p ^ 2))⁻¹)))) - 1 := by
            refine congrArg (fun x => x - 1) ?_
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hkp : k < p := Finset.mem_range.mp hk
            exact choose_pred_eq_zmod p k hp hkp
    _ = -(p : ZMod (p ^ 2)) *
            (∑ k ∈ Finset.range p,
              (-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
                ((Nat.factorial k : ZMod (p ^ 2))⁻¹)) := by
            rw [Finset.sum_sub_distrib]
            rw [sum_neg_one_pow_range_odd (R := ZMod (p ^ 2)) p hodd]
            rw [← Finset.mul_sum]
            ring

/-! ## Dividing by `p`: the reduction `ZMod (p²) → ZMod p` -/

/-- The canonical reduction `ZMod (p²) → ZMod p` (a ring hom since `p ∣ p²`). -/
def zmodSquareReduce (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (show p ∣ p ^ 2 by rw [pow_two]; exact dvd_mul_right p p) (ZMod p)

@[simp]
lemma zmodSquareReduce_natCast (p n : ℕ) :
    zmodSquareReduce p (n : ZMod (p ^ 2)) = (n : ZMod p) := by
  simp [zmodSquareReduce]

@[simp]
lemma zmodSquareReduce_val (p : ℕ) [NeZero (p ^ 2)] (x : ZMod (p ^ 2)) :
    zmodSquareReduce p x = (x.val : ZMod p) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact zmodSquareReduce_natCast p x.val

/-- For `k < p`, `k!` is a unit in `ZMod p`. -/
lemma factorial_unit_p (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    IsUnit ((Nat.factorial k : ℕ) : ZMod p) := by
  rw [ZMod.isUnit_iff_coprime]
  rw [Nat.coprime_comm]
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr (by
    intro hdvd
    have hle : p ≤ k := (Nat.Prime.dvd_factorial (Fact.out : Nat.Prime p)).mp hdvd
    omega)

@[simp]
lemma zmodSquareReduce_inv_natCast (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    zmodSquareReduce p (((Nat.factorial k : ℕ) : ZMod (p ^ 2))⁻¹) =
      ((Nat.factorial k : ℕ) : ZMod p)⁻¹ := by
  have hunit : IsUnit ((Nat.factorial k : ℕ) : ZMod (p ^ 2)) := factorial_unit p k hk
  have hunit_p : IsUnit ((Nat.factorial k : ℕ) : ZMod p) := factorial_unit_p p k hk
  have hmul : zmodSquareReduce p (((Nat.factorial k : ℕ) : ZMod (p ^ 2))⁻¹) *
        ((Nat.factorial k : ℕ) : ZMod p) = 1 := by
    have h := congrArg (zmodSquareReduce p) (ZMod.inv_mul_of_unit (Nat.factorial k : ZMod (p ^ 2)) hunit)
    rw [map_mul, map_one] at h
    simpa [zmodSquareReduce_natCast] using h
  apply mul_right_cancel₀ hunit_p.ne_zero
  rw [hmul, ZMod.inv_mul_of_unit ((Nat.factorial k : ℕ) : ZMod p) hunit_p]

/-- In `ZMod (p²)`, `p · x = 0` exactly when `x` reduces to `0` in `ZMod p`. -/
lemma p_mul_eq_zero_iff_reduce_eq_zero (p : ℕ) [Fact p.Prime] (x : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * x = 0 ↔ zmodSquareReduce p x = 0 := by
  haveI : NeZero (p ^ 2) := ⟨by
    intro h
    rw [pow_two] at h
    exact (Fact.out : Nat.Prime p).ne_zero ((Nat.mul_eq_zero.mp h).elim id id)⟩
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  rw [zmodSquareReduce_val p x]
  rw [ZMod.natCast_eq_zero_iff x.val p]
  constructor
  · intro h
    have h' : ((p * x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [← ZMod.natCast_zmod_val x] at h
      simpa [Nat.cast_mul] using h
    have hdvd : p ^ 2 ∣ p * x.val := (ZMod.natCast_eq_zero_iff (p * x.val) (p ^ 2)).mp h'
    have hpp : p * p ∣ p * x.val := by simpa [pow_two] using hdvd
    exact (Nat.mul_dvd_mul_iff_left hp0).mp hpp
  · intro hdvd
    have hdvd2 : p ^ 2 ∣ p * x.val := by
      simpa [pow_two] using (Nat.mul_dvd_mul_left p hdvd)
    have h' : ((p * x.val : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (p * x.val) (p ^ 2)).mpr hdvd2
    rw [← ZMod.natCast_zmod_val x]
    simpa [Nat.cast_mul] using h'

/-- Dividing the mod-`p²` sum by `p`: `q ≡ -∑ (-1)^k k!·H_k·(k!)⁻¹ (mod p)`. -/
lemma fermatQuotient_eq_neg_sum (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((fermatQuotient p : ℕ) : ZMod p) =
      -(∑ k ∈ Finset.range p,
          (-1 : ZMod p) ^ k * (harmonicFactorial k : ZMod p) * ((Nat.factorial k : ZMod p)⁻¹)) := by
  have h2 := two_pow_pred_sub_one_eq_zmod p hp
  have hq : p * fermatQuotient p = 2 ^ (p - 1) - 1 := fermatQuotient_mul_self p hp
  let S2 : ZMod (p ^ 2) := ∑ k ∈ Finset.range p,
    (-1 : ZMod (p ^ 2)) ^ k * (harmonicFactorial k : ZMod (p ^ 2)) *
      ((Nat.factorial k : ZMod (p ^ 2))⁻¹)
  have hpq : (p : ZMod (p ^ 2)) * (fermatQuotient p : ZMod (p ^ 2)) =
      ((2 ^ (p - 1) - 1 : ℕ) : ZMod (p ^ 2)) := by
    rw [← Nat.cast_mul, hq]
  have hzero : (p : ZMod (p ^ 2)) * ((fermatQuotient p : ZMod (p ^ 2)) + S2) = 0 := by
    rw [mul_add]
    rw [hpq, h2]
    ring
  have hred : zmodSquareReduce p ((fermatQuotient p : ZMod (p ^ 2)) + S2) = 0 :=
    (p_mul_eq_zero_iff_reduce_eq_zero p ((fermatQuotient p : ZMod (p ^ 2)) + S2)).mp hzero
  have hredS : zmodSquareReduce p S2 = ∑ k ∈ Finset.range p,
      (-1 : ZMod p) ^ k * (harmonicFactorial k : ZMod p) * ((Nat.factorial k : ZMod p)⁻¹) := by
    dsimp [S2]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : k < p := Finset.mem_range.mp hk
    rw [map_mul, map_mul, map_pow, map_neg, map_one, zmodSquareReduce_natCast,
      zmodSquareReduce_inv_natCast p k hkp]
  rw [map_add, zmodSquareReduce_natCast, hredS] at hred
  exact eq_neg_of_add_eq_zero_left hred

/-! ## The double count of the alternating harmonic sum -/

/-- `k!·H_k·(k!)⁻¹ = H_k = ∑_{j=1}^k j⁻¹` in `ZMod p`, for `k < p`. -/
lemma harmonicFactorial_cast_mul_inv (p k : ℕ) [Fact p.Prime] (hk : k < p) :
    (harmonicFactorial k : ZMod p) * ((Nat.factorial k : ZMod p)⁻¹) =
      ∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹ := by
  have hsum : (harmonicFactorial k : ZMod p) =
      ∑ j ∈ Finset.Icc 1 k, ((Nat.factorial k / j : ℕ) : ZMod p) := by
    rw [harmonicFactorial, Nat.cast_sum]
  have hterm : (∑ j ∈ Finset.Icc 1 k, ((Nat.factorial k / j : ℕ) : ZMod p)) =
      ∑ j ∈ Finset.Icc 1 k, (Nat.factorial k : ZMod p) * (j : ZMod p)⁻¹ := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjunit : IsUnit (j : ZMod p) := by
      rw [ZMod.isUnit_iff_coprime]
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr (by
        intro hdvd
        have hjp : j < p := by omega
        exact (not_lt_of_ge (Nat.le_of_dvd (by omega : 0 < j) hdvd)) hjp)
    exact zmod_div_mul_inv (p := p) (j := j) (m := Nat.factorial k)
      (Nat.dvd_factorial (by omega : 0 < j) (by omega : j ≤ k)) hjunit
  have hunit : IsUnit ((Nat.factorial k : ℕ) : ZMod p) := factorial_unit_p p k hk
  calc
    (harmonicFactorial k : ZMod p) * ((Nat.factorial k : ZMod p)⁻¹)
        = (∑ j ∈ Finset.Icc 1 k, (Nat.factorial k : ZMod p) * (j : ZMod p)⁻¹) *
            ((Nat.factorial k : ZMod p)⁻¹) := by rw [hsum, hterm]
    _ = ∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          rw [mul_assoc, mul_comm (j : ZMod p)⁻¹ ((Nat.factorial k : ZMod p)⁻¹),
            ← mul_assoc, ZMod.mul_inv_of_unit (Nat.factorial k : ZMod p) hunit, one_mul]

/-- `∑_{k=0}^{2m} (-1)^k H_k = (1/2) H_m` in `ZMod p`, where `H_k = ∑_{j=1}^k j⁻¹`. -/
lemma sum_neg_one_harmonic_sum_eq_two_mul_add_one (p m : ℕ) [Fact p.Prime] :
    (∑ k ∈ Finset.range (2 * m + 1), ((-1 : ZMod p) ^ k) *
        (∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹)) =
      (2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 m, (j : ZMod p)⁻¹) := by
  let f : ℕ → ZMod p := fun k => ∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹
  have hf_succ : ∀ k, f (k + 1) = f k + ((k + 1 : ℕ) : ZMod p)⁻¹ := by
    intro k
    dsimp [f]
    rw [Finset.sum_Icc_succ_top (a := 1) (b := k) (by omega : 1 ≤ k + 1)]
  induction m with
  | zero => simp
  | succ m ih =>
      have hneg1 : (-1 : ZMod p) ^ (2 * m + 1) = -1 := Odd.neg_one_pow (by exact ⟨m, rfl⟩)
      have hone1 : (-1 : ZMod p) ^ (2 * m + 2) = 1 := Even.neg_one_pow (by exact ⟨m + 1, by omega⟩)
      have hf1 : f (2 * m + 2) = f (2 * m + 1) + ((2 * m + 2 : ℕ) : ZMod p)⁻¹ := hf_succ (2 * m + 1)
      have hfm : f (m + 1) = f m + ((m + 1 : ℕ) : ZMod p)⁻¹ := hf_succ m
      have hinv : ((2 * m + 2 : ℕ) : ZMod p)⁻¹ =
          (2 : ZMod p)⁻¹ * ((m + 1 : ℕ) : ZMod p)⁻¹ := by
        rw [show 2 * m + 2 = 2 * (m + 1) by omega]
        rw [Nat.cast_mul]
        rw [mul_inv_rev, mul_comm]
        norm_num
      calc
        (∑ k ∈ Finset.range (2 * (m + 1) + 1), ((-1 : ZMod p) ^ k) * f k)
            = (∑ k ∈ Finset.range (2 * m + 1), ((-1 : ZMod p) ^ k) * f k) +
                ((-1 : ZMod p) ^ (2 * m + 1)) * f (2 * m + 1) +
                ((-1 : ZMod p) ^ (2 * m + 2)) * f (2 * m + 2) := by
              rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 m, (j : ZMod p)⁻¹) +
                (-1 : ZMod p) * f (2 * m + 1) + (1 : ZMod p) * f (2 * m + 2) := by
              rw [ih, hneg1, hone1]
        _ = (2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 (m + 1), (j : ZMod p)⁻¹) := by
              dsimp [f] at hf1 hfm ⊢
              rw [hf1, hfm, hinv]
              ring

/-- For an odd prime `p`, `2` is a unit in `ZMod p`. -/
lemma two_isUnit (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) : IsUnit (2 : ZMod p) := by
  rw [isUnit_iff_ne_zero]
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Eisenstein's congruence**: `∑_{j=1}^m j⁻¹ = -2 · q_p(2) (mod p)`. -/
theorem eisenstein_congruence (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (∑ j ∈ Finset.Icc 1 ((p - 1) / 2), ((j : ZMod p)⁻¹)) =
      -((2 : ZMod p)) * ((fermatQuotient p : ℕ) : ZMod p) := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  rcases hodd with ⟨m, hm⟩
  have hm2 : (p - 1) / 2 = m := by omega
  rw [hm2]
  have hq := fermatQuotient_eq_neg_sum p hp
  have hsum : (∑ k ∈ Finset.range p,
        (-1 : ZMod p) ^ k * (harmonicFactorial k : ZMod p) * ((Nat.factorial k : ZMod p)⁻¹)) =
      ∑ k ∈ Finset.range p, ((-1 : ZMod p) ^ k) * (∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : k < p := Finset.mem_range.mp hk
    rw [mul_assoc]
    rw [harmonicFactorial_cast_mul_inv p k hkp]
  have hpair := sum_neg_one_harmonic_sum_eq_two_mul_add_one p m
  have hq' : ((fermatQuotient p : ℕ) : ZMod p) =
      -((2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 m, (j : ZMod p)⁻¹)) := by
    rw [hq, hsum]
    rw [show (∑ k ∈ Finset.range p, ((-1 : ZMod p) ^ k) * (∑ j ∈ Finset.Icc 1 k, (j : ZMod p)⁻¹)) =
        (2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 m, (j : ZMod p)⁻¹) by
      simpa [hm] using hpair]
  have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp
  calc
    (∑ j ∈ Finset.Icc 1 m, (j : ZMod p)⁻¹)
        = (2 : ZMod p) * (2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 m, (j : ZMod p)⁻¹) := by
            rw [htwo, one_mul]
    _ = -((2 : ZMod p) * ((fermatQuotient p : ℕ) : ZMod p)) := by
            rw [hq']
            ring
    _ = -((2 : ZMod p)) * ((fermatQuotient p : ℕ) : ZMod p) := by ring

/-! ## The Wieferich middle-digit theorem (A1) -/

/-- **The middle-digit theorem (A1)**: for an odd prime `p`, the middle digit `(p - 1) / 2`
is a bad digit exactly when `p` is a base-2 Wieferich prime (`p² ∣ 2^(p-1) - 1`). -/
theorem mid_digit_mem_E_iff_wieferich (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    ((p - 1) / 2 ∈ E p) ↔ p ^ 2 ∣ 2 ^ (p - 1) - 1 := by
  have hp' : Nat.Prime p := Fact.out
  have h1m : 1 ≤ (p - 1) / 2 := by omega
  have hmp : (p - 1) / 2 < p := by omega
  rw [mem_E_iff_dvd_num p ((p - 1) / 2) hp' h1m hmp]
  rw [num_dvd_iff_sum_inv_zero p ((p - 1) / 2) hmp]
  rw [eisenstein_congruence p hp]
  have hneg_two_unit : IsUnit (-(2 : ZMod p)) := (two_isUnit p hp).neg
  have hiff1 : (-(2 : ZMod p)) * ((fermatQuotient p : ℕ) : ZMod p) = 0 ↔
      ((fermatQuotient p : ℕ) : ZMod p) = 0 := by
    constructor
    · intro h
      rw [mul_eq_zero] at h
      rcases h with h1 | h2
      · exfalso
        exact hneg_two_unit.ne_zero h1
      · exact h2
    · intro h
      rw [h, mul_zero]
  rw [hiff1]
  rw [ZMod.natCast_eq_zero_iff (fermatQuotient p) p]
  dsimp [fermatQuotient]
  rw [Nat.dvd_div_iff_mul_dvd (fermat_dvd p hp)]
  rw [pow_two]

end

end Erdos291
