import Erdos291.Eisenstein
import Erdos291.MidAttackLine3
import Erdos291.MidAttackLine4
import Erdos291.MidCriticalSeparation

/-!
# Erdős #291 — the two halves of the middle harmonic: `h_r` and `c_r`

For a natural number `r` define the two integer "half" quantities

* `hN r = harmonicFactorial r = ∑_{i=1}^r r!/i`, the integer representative of the
  first half `H_r` (it vanishes mod `p` exactly when `r ∈ E p`);
* `cN r = ∑_{j=r+1}^{2r} ∏_{i∈[r+1,2r]\{j}} i`, the integer representative of the
  second half `H_{2r} - H_r` multiplied by the unit `∏_{i=r+1}^{2r} i` (it vanishes
  mod `p` exactly when `H_{2r} = H_r`, i.e. together with `r ∈ E p` when `H_{2r}=0`).

The quartic `A_poly r = X (X - r) (X + r + 1) (X + 2r + 1)` and the remainder
`RemainderR r = Qd r %ₘ A_poly r` connect the two halves over `ℤ`:

1. `Qd r` evaluates to the two halves at the four roots of `A_poly r`:
   `Qd r(0) = h_r`, `Qd r(r) = c_r`,
   `Qd r(-r-1) = (-1)^{r+1} h_r`, `Qd r(-2r-1) = (-1)^{r+1} c_r`.

2. Since `RemainderR r` agrees with `Qd r` at `0` and `r` (the other two roots of
   `A_poly r` vanish), the content of `RemainderR r` divides
   `gcd(hN r, cN r)`: `content(RemainderR r).natAbs ∣ Nat.gcd (hN r) (cN r)`.

3. For a prime `p`, `p` divides `content(RemainderR r)` iff the reduction
   `A_poly_mod p r` divides `Q p r` in `ZMod p[X]`.

4. For a middle pair `(p,r)` (`r ∈ E p`, `4r+1 < p`) the divisibility
   `A_poly_mod p r ∣ Q p r` is equivalent to `H_{2r} = 0`: the forward direction
   uses the root `r`; the backward direction uses the four distinct roots
   `0, r, -r-1, -2r-1` of `A_poly_mod`.

Together these reduce (B) `H_{2r} ≠ 0` to the single missing arithmetic identity
`gcd(h_r, c_r) | (4r+1)!`, and hence the full frontier
(`HA_mid_resultant_Qr_midTailDerivative_ne_zero`, therefore
`H_{2r} ≠ 0`, `res(F,G) ≠ 0` and CR-freeness) to the three hypotheses
(gcd identity, CR-free, no-extension-root).
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- The first half: `h_r = ∑_{i=1}^r r!/i = harmonicFactorial r`. -/
def hN (r : ℕ) : ℕ := harmonicFactorial r

/-- The second half: `c_r = ∑_{j=r+1}^{2r} ∏_{i∈[r+1,2r]\{j}} i`. -/
def cN (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc (r + 1) (2 * r),
    ∏ i ∈ (Finset.Icc (r + 1) (2 * r)).erase j, i

/-- The single missing integer identity: `gcd(h_r, c_r) | (4r+1)!`.
Evidence: sympy-verified `r ≤ 300`; sharp at `r = 273` (`1093 = 4·273+1`
divides the gcd). -/
def HA_arithmetic_gcd_hN_cN_dvd_factorial : Prop :=
  ∀ r : ℕ, 1 ≤ r → Nat.gcd (hN r) (cN r) ∣ Nat.factorial (4 * r + 1)

/-! ## Evaluation identities for `Qd r` -/

/-- Evaluating `Qd r` at an integer `x` gives the derivative-product sum. -/
lemma Qd_eval_eq_sum_prod_erase (r : ℕ) (x : ℤ) :
    Polynomial.eval x (Qd r) =
      ∑ i ∈ Finset.Icc 1 r, ∏ j ∈ (Finset.Icc 1 r).erase i, (x + (j : ℤ)) := by
  classical
  rw [Qd, Pd, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_mul]
  have hder : Polynomial.eval x (Polynomial.derivative (Polynomial.X + Polynomial.C (i : ℤ))) = 1 := by
    rw [Polynomial.derivative_X_add_C, Polynomial.eval_one]
  rw [hder, mul_one, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

/-- The product `∏_{j=1}^r j` is `r!`. -/
lemma prod_Icc_one_eq_factorial (r : ℕ) :
    (∏ j ∈ Finset.Icc 1 r, j) = Nat.factorial r := by
  classical
  rw [← Finset.prod_range_add_one_eq_factorial r]
  refine Finset.prod_bij (fun i hi => i - 1) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range]
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ r := Finset.mem_Icc.mp hi₁
    have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ r := Finset.mem_Icc.mp hi₂
    omega
  · intro j hj
    have hj' : j < r := Finset.mem_range.mp hj
    refine ⟨j + 1, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    omega

/-- For `i ∈ [1,r]`, the product of all `j ∈ [1,r]` except `i` is `r!/i`. -/
lemma prod_Icc_one_erase_eq_factorial_div (r i : ℕ) (hi : i ∈ Finset.Icc 1 r) :
    (∏ j ∈ (Finset.Icc 1 r).erase i, j) = Nat.factorial r / i := by
  classical
  have hpos : i ≠ 0 := by
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    omega
  have hmul : i * (∏ j ∈ (Finset.Icc 1 r).erase i, j) = Nat.factorial r := by
    rw [Finset.mul_prod_erase (Finset.Icc 1 r) (fun j => j) hi]
    exact prod_Icc_one_eq_factorial r
  exact Nat.eq_div_of_mul_eq_right hpos hmul

/-- `Qd r` evaluated at `0` is the integer `h_r`. -/
lemma Qd_eval_zero_eq_hN (r : ℕ) :
    Polynomial.eval (0 : ℤ) (Qd r) = (hN r : ℤ) := by
  classical
  rw [Qd_eval_eq_sum_prod_erase r 0]
  simp only [zero_add]
  change (∑ i ∈ Finset.Icc 1 r, ∏ j ∈ (Finset.Icc 1 r).erase i, (j : ℤ)) = (hN r : ℤ)
  rw [hN, harmonicFactorial, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.cast_prod]
  exact congrArg (fun n : ℕ => (n : ℤ)) (prod_Icc_one_erase_eq_factorial_div r i hi)

/-- `Qd r` evaluated at `r` is the integer `c_r`. -/
lemma Qd_eval_r_eq_cN (r : ℕ) :
    Polynomial.eval (r : ℤ) (Qd r) = (cN r : ℤ) := by
  classical
  rw [Qd_eval_eq_sum_prod_erase r (r : ℤ)]
  simp only [← Nat.cast_add]
  rw [cN, Nat.cast_sum]
  simp only [Nat.cast_prod]
  refine Finset.sum_bij (fun i hi => r + i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_Icc]
    have hi' : 1 ≤ i ∧ i ≤ r := Finset.mem_Icc.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ h
    have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ r := Finset.mem_Icc.mp hi₁
    have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ r := Finset.mem_Icc.mp hi₂
    omega
  · intro t ht
    have ht' : r + 1 ≤ t ∧ t ≤ 2 * r := Finset.mem_Icc.mp ht
    refine ⟨t - r, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    refine Finset.prod_bij (fun j hj => r + j) ?_ ?_ ?_ ?_
    · intro j hj
      rcases Finset.mem_erase.mp hj with ⟨hji, hjI⟩
      rw [Finset.mem_Icc] at hjI
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h
        apply hji
        omega
      · rw [Finset.mem_Icc]
        constructor <;> omega
    · intro j₁ hj₁ j₂ hj₂ h
      omega
    · intro t ht
      rcases Finset.mem_erase.mp ht with ⟨htne, htI⟩
      rw [Finset.mem_Icc] at htI
      refine ⟨t - r, ?_, ?_⟩
      · rw [Finset.mem_erase]
        refine ⟨?_, ?_⟩
        · intro h
          apply htne
          omega
        · rw [Finset.mem_Icc]
          constructor <;> omega
      · omega
    · intro j hj
      rfl

/-- For `i ∈ [1,k+1]`, the derivative-product summand at `-(2k+3)` factors as
`(-1)^k` times the corresponding product for `c_{k+1}`. -/
private lemma prod_erase_eval_neg_two_r_add_one (k : ℕ) (i : ℕ)
    (hi : i ∈ Finset.Icc 1 (k + 1)) :
    (∏ j ∈ (Finset.Icc 1 (k + 1)).erase i,
        (-(2 * ((k + 1 : ℕ) : ℤ) + 1) + (j : ℤ))) =
      (-1 : ℤ) ^ k *
        (∏ t ∈ (Finset.Icc (k + 2) (2 * (k + 1))).erase (2 * (k + 1) + 1 - i),
          (t : ℤ)) := by
  classical
  have hprodNeg : (∏ j ∈ (Finset.Icc 1 (k + 1)).erase i,
      (-(2 * ((k + 1 : ℕ) : ℤ) + 1) + (j : ℤ))) =
      ∏ j ∈ (Finset.Icc 1 (k + 1)).erase i, (-((2 * (k + 1) + 1 - j : ℕ) : ℤ)) := by
    apply Finset.prod_congr rfl
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji, hjI⟩
    rw [Finset.mem_Icc] at hjI
    have hjN : j ≤ 2 * (k + 1) + 1 := by omega
    have hcast : (-(2 * ((k + 1 : ℕ) : ℤ) + 1) + (j : ℤ)) =
        -((2 * (k + 1) + 1 - j : ℕ) : ℤ) := by
      rw [show -(2 * ((k + 1 : ℕ) : ℤ) + 1) + (j : ℤ) =
          -((2 * ((k + 1 : ℕ) : ℤ) + 1) - (j : ℤ)) by ring]
      rw [Nat.cast_sub hjN]
      norm_num [Nat.cast_add, Nat.cast_mul]
    exact hcast
  rw [hprodNeg, Finset.prod_neg]
  have hcard : ((Finset.Icc 1 (k + 1)).erase i).card = k := by
    rw [Finset.card_erase_of_mem hi]
    rw [Nat.card_Icc]
    omega
  rw [hcard]
  congr 1
  refine Finset.prod_bij (fun j hj => 2 * (k + 1) + 1 - j) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji, hjI⟩
    rw [Finset.mem_Icc] at hjI
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro h
      apply hji
      omega
    · rw [Finset.mem_Icc]
      constructor <;> omega
  · intro j₁ hj₁ j₂ hj₂ h
    rcases Finset.mem_erase.mp hj₁ with ⟨hj₁ne, hj₁I⟩
    rcases Finset.mem_erase.mp hj₂ with ⟨hj₂ne, hj₂I⟩
    rw [Finset.mem_Icc] at hj₁I hj₂I
    omega
  · intro t ht
    rcases Finset.mem_erase.mp ht with ⟨htne, htI⟩
    rw [Finset.mem_Icc] at htI
    refine ⟨2 * (k + 1) + 1 - t, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro h
        apply htne
        omega
      · rw [Finset.mem_Icc]
        constructor <;> omega
    · omega
  · intro j hj
    rfl

/-- `Qd r` evaluated at `-(2r+1)` is `(-1)^{r+1} c_r`. -/
lemma Qd_eval_neg_two_r_add_one_eq_sign_cN (r : ℕ) :
    Polynomial.eval (-(2 * (r : ℤ) + 1)) (Qd r) = (-1 : ℤ) ^ (r + 1) * (cN r : ℤ) := by
  classical
  rcases r with _ | k
  · simp [Qd, Pd, cN]
  · rw [Qd_eval_eq_sum_prod_erase (k + 1) (-(2 * ((k + 1 : ℕ) : ℤ) + 1))]
    have hsumTerms :
        (∑ i ∈ Finset.Icc 1 (k + 1),
            ∏ j ∈ (Finset.Icc 1 (k + 1)).erase i,
              (-(2 * ((k + 1 : ℕ) : ℤ) + 1) + (j : ℤ))) =
          (-1 : ℤ) ^ k *
            (∑ i ∈ Finset.Icc 1 (k + 1),
              ∏ t ∈ (Finset.Icc (k + 2) (2 * (k + 1))).erase (2 * (k + 1) + 1 - i),
                (t : ℤ)) := by
      calc
        (∑ i ∈ Finset.Icc 1 (k + 1),
            ∏ j ∈ (Finset.Icc 1 (k + 1)).erase i,
              (-(2 * ((k + 1 : ℕ) : ℤ) + 1) + (j : ℤ))) =
            ∑ i ∈ Finset.Icc 1 (k + 1),
              ((-1 : ℤ) ^ k *
                (∏ t ∈ (Finset.Icc (k + 2) (2 * (k + 1))).erase (2 * (k + 1) + 1 - i),
                  (t : ℤ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [prod_erase_eval_neg_two_r_add_one k i hi]
        _ = (-1 : ℤ) ^ k *
            (∑ i ∈ Finset.Icc 1 (k + 1),
              ∏ t ∈ (Finset.Icc (k + 2) (2 * (k + 1))).erase (2 * (k + 1) + 1 - i),
                (t : ℤ)) := by
              rw [Finset.mul_sum]
    have hsumReindex :
        (∑ i ∈ Finset.Icc 1 (k + 1),
            ∏ t ∈ (Finset.Icc (k + 2) (2 * (k + 1))).erase (2 * (k + 1) + 1 - i), (t : ℤ)) =
          (cN (k + 1) : ℤ) := by
      rw [cN, Nat.cast_sum]
      simp only [Nat.cast_prod]
      refine Finset.sum_bij (fun i hi => 2 * (k + 1) + 1 - i) ?_ ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_Icc]
        have hi' : 1 ≤ i ∧ i ≤ k + 1 := Finset.mem_Icc.mp hi
        omega
      · intro i₁ hi₁ i₂ hi₂ h
        have hi₁' : 1 ≤ i₁ ∧ i₁ ≤ k + 1 := Finset.mem_Icc.mp hi₁
        have hi₂' : 1 ≤ i₂ ∧ i₂ ≤ k + 1 := Finset.mem_Icc.mp hi₂
        omega
      · intro t ht
        rw [Finset.mem_Icc] at ht
        refine ⟨2 * (k + 1) + 1 - t, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          omega
        · omega
      · intro i hi
        rfl
    rw [hsumTerms, hsumReindex]
    have hsign : (-1 : ℤ) ^ (k + 1 + 1) = (-1 : ℤ) ^ k := by
      rw [show k + 1 + 1 = k + 2 by omega, pow_add]
      norm_num
    rw [hsign]

/-- `Qd r` evaluated at `-(r+1)` is `(-1)^{r+1} h_r`. -/
lemma Qd_eval_neg_r_add_one_eq_sign_hN (r : ℕ) :
    Polynomial.eval (-((r : ℤ) + 1)) (Qd r) = (-1 : ℤ) ^ (r + 1) * (hN r : ℤ) := by
  have hsym := Qd_comp_neg_X_sub_C_add_one r
  have heval := congrArg (fun f : Polynomial ℤ => Polynomial.eval (0 : ℤ) f) hsym
  rw [Polynomial.eval_comp] at heval
  have hq0 : Polynomial.eval (0 : ℤ) (-Polynomial.X - Polynomial.C ((r : ℤ) + 1)) =
      -((r : ℤ) + 1) := by
    rw [Polynomial.eval_sub, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_C]
    simp
  rw [hq0] at heval
  rw [Polynomial.eval_mul, Polynomial.eval_pow] at heval
  simp at heval
  rw [Qd_eval_zero_eq_hN r] at heval
  simpa using heval

/-! ## The remainder `RemainderR r` and its content -/

/-- The content of an integer polynomial divides every integer evaluation. -/
lemma content_dvd_eval (p : Polynomial ℤ) (x : ℤ) :
    p.content ∣ p.eval x := by
  rw [p.eval_eq_sum_range x]
  exact Finset.dvd_sum (fun i hi => dvd_mul_of_dvd_left (Polynomial.content_dvd_coeff i) (x ^ i))

/-- `RemainderR r` agrees with `Qd r` at `0`: both equal `h_r`. -/
lemma RemainderR_eval_zero_eq_hN (r : ℕ) :
    Polynomial.eval (0 : ℤ) (RemainderR r) = (hN r : ℤ) := by
  change Polynomial.eval (0 : ℤ) (Qd r %ₘ A_poly r) = (hN r : ℤ)
  have hdiv := Polynomial.modByMonic_add_div (Qd r) (A_poly r)
  have heval := congrArg (fun f : Polynomial ℤ => Polynomial.eval (0 : ℤ) f) hdiv
  rw [Polynomial.eval_add, Polynomial.eval_mul] at heval
  have hA0 : Polynomial.eval (0 : ℤ) (A_poly r) = 0 := by
    rw [A_poly]
    simp
  rw [hA0, zero_mul, add_zero] at heval
  exact heval.trans (Qd_eval_zero_eq_hN r)

/-- `RemainderR r` agrees with `Qd r` at `r`: both equal `c_r`. -/
lemma RemainderR_eval_r_eq_cN (r : ℕ) :
    Polynomial.eval (r : ℤ) (RemainderR r) = (cN r : ℤ) := by
  change Polynomial.eval (r : ℤ) (Qd r %ₘ A_poly r) = (cN r : ℤ)
  have hdiv := Polynomial.modByMonic_add_div (Qd r) (A_poly r)
  have heval := congrArg (fun f : Polynomial ℤ => Polynomial.eval (r : ℤ) f) hdiv
  rw [Polynomial.eval_add, Polynomial.eval_mul] at heval
  have hAr : Polynomial.eval (r : ℤ) (A_poly r) = 0 := by
    rw [A_poly]
    simp
  rw [hAr, zero_mul, add_zero] at heval
  exact heval.trans (Qd_eval_r_eq_cN r)

/-- The content of `RemainderR r` divides `gcd(h_r, c_r)`. -/
lemma content_RemainderR_natAbs_dvd_gcd_hN_cN (r : ℕ) (hr1 : 1 ≤ r) :
    (Polynomial.content (RemainderR r)).natAbs ∣ Nat.gcd (hN r) (cN r) := by
  have h0 : (Polynomial.content (RemainderR r) : ℤ) ∣ (hN r : ℤ) := by
    rw [← RemainderR_eval_zero_eq_hN r]
    exact content_dvd_eval (RemainderR r) 0
  have hr : (Polynomial.content (RemainderR r) : ℤ) ∣ (cN r : ℤ) := by
    rw [← RemainderR_eval_r_eq_cN r]
    exact content_dvd_eval (RemainderR r) (r : ℤ)
  rw [Nat.dvd_gcd_iff]
  constructor
  · simpa [Int.natAbs_natCast] using (Int.natAbs_dvd_natAbs.mpr h0)
  · simpa [Int.natAbs_natCast] using (Int.natAbs_dvd_natAbs.mpr hr)

/-! ## Reduction of `RemainderR r` modulo `p` -/

/-- The reduction of `RemainderR r` modulo `p` is the remainder of `Q p r` modulo
`A_poly_mod p r`. -/
lemma RemainderR_map (p r : ℕ) :
    (RemainderR r).map (Int.castRingHom (ZMod p)) = Q p r %ₘ A_poly_mod p r := by
  rw [RemainderR, A_poly_mod]
  rw [Polynomial.map_modByMonic (Int.castRingHom (ZMod p)) (A_poly_monic r)]
  rw [Qd_map p r]

/-- `A_poly_mod p r` is monic. -/
lemma A_poly_mod_monic (p r : ℕ) : (A_poly_mod p r).Monic := by
  rw [A_poly_mod]
  exact (A_poly_monic r).map (Int.castRingHom (ZMod p))

/-- For a prime `p`, `p` divides the content of `RemainderR r` iff
`A_poly_mod p r` divides `Q p r` in `ZMod p[X]`. -/
lemma prime_dvd_content_RemainderR_iff_A_poly_mod_dvd_Q (p r : ℕ) [Fact p.Prime] :
    p ∣ (Polynomial.content (RemainderR r)).natAbs ↔ A_poly_mod p r ∣ Q p r := by
  have hmapZero :
      (RemainderR r).map (Int.castRingHom (ZMod p)) = 0 ↔ A_poly_mod p r ∣ Q p r := by
    rw [RemainderR_map p r]
    rw [Polynomial.modByMonic_eq_zero_iff_dvd (A_poly_mod_monic p r)]
  rw [← hmapZero]
  constructor
  · intro hpdvd
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_map]
    change (((coeff (RemainderR r) n : ℤ) : ZMod p) = 0)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcontent : (p : ℤ) ∣ (Polynomial.content (RemainderR r)) :=
      (Int.natCast_dvd (m := p) (n := Polynomial.content (RemainderR r))).mpr hpdvd
    exact hcontent.trans (Polynomial.content_dvd_coeff n)
  · intro hmap
    have hcoeff : ∀ n : ℕ, (p : ℤ) ∣ coeff (RemainderR r) n := by
      intro n
      have hcoeff0 : (((coeff (RemainderR r) n : ℤ) : ZMod p) = 0) := by
        have h := congrArg (fun q : Polynomial (ZMod p) => q.coeff n) hmap
        simpa [Polynomial.coeff_map] using h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff (RemainderR r) n) p).mp hcoeff0
    have hcontent : (p : ℤ) ∣ (Polynomial.content (RemainderR r)) := by
      rw [Polynomial.content]
      exact Finset.dvd_gcd_iff.mpr (fun n hn => hcoeff n)
    exact (Int.natCast_dvd (m := p) (n := Polynomial.content (RemainderR r))).mp hcontent

/-! ## Casting the two halves modulo `p` -/

/-- `h_r` is `r! · H_r` in `ZMod p`. -/
lemma hN_cast_eq_factorial_mul_harmonicSum (p r : ℕ) [Fact p.Prime] (hrlt : r < p) :
    (hN r : ZMod p) = (Nat.factorial r : ZMod p) * harmonicSum p r := by
  have hunit : IsUnit ((Nat.factorial r : ℕ) : ZMod p) := factorial_unit_p p r hrlt
  calc
    (hN r : ZMod p) = (hN r : ZMod p) *
        ((Nat.factorial r : ZMod p) * (Nat.factorial r : ZMod p)⁻¹) := by
          rw [ZMod.mul_inv_of_unit ((Nat.factorial r : ℕ) : ZMod p) hunit, mul_one]
    _ = (Nat.factorial r : ZMod p) * ((hN r : ZMod p) * (Nat.factorial r : ZMod p)⁻¹) := by
          ring
    _ = (Nat.factorial r : ZMod p) * harmonicSum p r := by
          rw [hN]
          rw [harmonicFactorial_cast_mul_inv p r hrlt]
          rfl

/-- If `r ∈ E p` and `r < p`, then `h_r` vanishes modulo `p`. -/
lemma hN_cast_eq_zero_of_mem_E (p r : ℕ) [Fact p.Prime] (hrE : r ∈ E p) (hrlt : r < p) :
    (hN r : ZMod p) = 0 := by
  rw [hN_cast_eq_factorial_mul_harmonicSum p r hrlt, harmonicSum_middle_pair_zero p r hrE hrlt,
    mul_zero]

/-- `c_r` is `(∏_{j=r+1}^{2r} j) · H_{2r}` in `ZMod p` for a middle pair. -/
lemma cN_cast_eq_prod_mul_harmonicSum_two_mul (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (h2r1 : 2 * r + 1 < p) :
    (cN r : ZMod p) =
      (∏ i ∈ Finset.Icc (r + 1) (2 * r), ((i : ℕ) : ZMod p)) * harmonicSum p (2 * r) := by
  have hp : Nat.Prime p := Fact.out
  have hunits : ∀ i ∈ Finset.Icc (r + 1) (2 * r), IsUnit ((i : ℕ) : ZMod p) := by
    intro i hi
    have hi' : r + 1 ≤ i ∧ i ≤ 2 * r := Finset.mem_Icc.mp hi
    rw [ZMod.isUnit_iff_coprime]
    rw [Nat.coprime_comm]
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    have hge : 1 ≤ i := by omega
    have hlt : i < p := by omega
    exact (not_lt_of_ge (Nat.le_of_dvd hge hdvd)) hlt
  have hcast : (cN r : ZMod p) = ∑ j ∈ Finset.Icc (r + 1) (2 * r),
      ∏ i ∈ (Finset.Icc (r + 1) (2 * r)).erase j, ((i : ℕ) : ZMod p) := by
    rw [cN, Nat.cast_sum]
    simp only [Nat.cast_prod]
  rw [hcast]
  rw [sum_prod_erase_eq_mul_inv (Finset.Icc (r + 1) (2 * r)) (fun i => ((i : ℕ) : ZMod p)) hunits]
  rw [sum_inv_Icc_add_eq_harmonicSum_two_mul_of_middle_pair p r hrE h2r1]

/-- If `H_{2r} = 0` for a middle pair, then `c_r` vanishes modulo `p`. -/
lemma cN_cast_eq_zero_of_harmonicSum_two_mul_r_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) (hH2r : harmonicSum p (2 * r) = 0) :
    (cN r : ZMod p) = 0 := by
  rw [cN_cast_eq_prod_mul_harmonicSum_two_mul p r hrE (by omega : 2 * r + 1 < p), hH2r,
    mul_zero]

/-! ## The middle-pair root equivalence -/

/-- For a middle pair, `A_poly_mod p r ∣ Q p r` iff `H_{2r} = 0`. -/
lemma A_poly_mod_dvd_Q_iff_harmonicSum_two_mul_r_eq_zero (p r : ℕ) [Fact p.Prime]
    (hrE : r ∈ E p) (hmid : 4 * r + 1 < p) :
    A_poly_mod p r ∣ Q p r ↔ harmonicSum p (2 * r) = 0 := by
  have hp : Nat.Prime p := Fact.out
  have h1r : 1 ≤ r := mem_E_ge_one p r hrE
  have hr_lt : r < p := by omega
  constructor
  · intro hdvd
    have hfactor : (Polynomial.X - Polynomial.C (r : ZMod p)) ∣ A_poly_mod p r := by
      rw [A_poly_mod_eq]
      rw [show Polynomial.X * (Polynomial.X - Polynomial.C (r : ZMod p)) *
          (Polynomial.X + Polynomial.C ((r : ZMod p) + 1)) *
          (Polynomial.X + Polynomial.C (2 * (r : ZMod p) + 1)) =
          (Polynomial.X - Polynomial.C (r : ZMod p)) *
            (Polynomial.X * (Polynomial.X + Polynomial.C ((r : ZMod p) + 1)) *
              (Polynomial.X + Polynomial.C (2 * (r : ZMod p) + 1))) by ring]
      exact dvd_mul_right _ _
    have hdvdQ : (Polynomial.X - Polynomial.C (r : ZMod p)) ∣ Q p r := hfactor.trans hdvd
    have hroot : (Q p r).IsRoot (r : ZMod p) := (Polynomial.dvd_iff_isRoot).mp hdvdQ
    rw [Polynomial.IsRoot,
      eval_Q_p_r_eq_ascFactorial_mul_harmonicSum_two_mul_of_mem_E p r hrE
        (by omega : 2 * r + 1 < p)] at hroot
    have hasc_ne : ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) ≠ 0 := by
      have hprod : ((Nat.ascFactorial (r + 1) r : ℕ) : ZMod p) =
          ∏ i ∈ Finset.range r, (((r + 1 + i : ℕ) : ZMod p)) := by
        rw [Nat.ascFactorial_eq_prod_range]
        simp
      rw [hprod]
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have hi' : i < r := Finset.mem_range.mp hi
      have hge : 1 ≤ r + 1 + i := by omega
      have hle : r + 1 + i ≤ 2 * r := by omega
      have hlt : r + 1 + i < p := by omega
      intro hz
      have hpdvd : p ∣ r + 1 + i := (ZMod.natCast_eq_zero_iff (r + 1 + i) p).mp hz
      exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
    exact (mul_eq_zero.mp hroot).resolve_left hasc_ne
  · intro hH2r
    let p0 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (0 : ZMod p)
    let pr : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (r : ZMod p)
    let pn1 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (-((r : ZMod p) + 1))
    let pn2 : Polynomial (ZMod p) := Polynomial.X - Polynomial.C (-(2 * (r : ZMod p) + 1))
    have hA : A_poly_mod p r = p0 * pr * pn1 * pn2 := by
      dsimp [p0, pr, pn1, pn2]
      rw [A_poly_mod_eq]
      simp only [Polynomial.C_0, Polynomial.C_neg, sub_eq_add_neg, neg_neg]
      ring
    have hroot0 : (Q p r).IsRoot 0 := by
      rw [Polynomial.IsRoot, eval_zero_Q_eq_factorial_mul_harmonic p r hr_lt,
        harmonicSum_middle_pair_zero p r hrE hr_lt, mul_zero]
    have hrootr : (Q p r).IsRoot (r : ZMod p) := by
      rw [Polynomial.IsRoot,
        eval_Q_p_r_eq_ascFactorial_mul_harmonicSum_two_mul_of_mem_E p r hrE
          (by omega : 2 * r + 1 < p), hH2r, mul_zero]
    have hrootn1 : (Q p r).IsRoot (-((r : ZMod p) + 1)) := by
      rw [Polynomial.IsRoot]
      rw [← Qd_map p r]
      have hval : Int.castRingHom (ZMod p) (-((r : ℤ) + 1)) = -((r : ZMod p) + 1) := by
        simp
      rw [← hval]
      rw [Polynomial.eval_map_apply, Qd_eval_neg_r_add_one_eq_sign_hN r]
      simp only [map_mul, map_pow, map_neg, map_one]
      have hmap : (Int.castRingHom (ZMod p)) (hN r : ℤ) = (hN r : ZMod p) := by simp
      rw [hmap]
      rw [hN_cast_eq_zero_of_mem_E p r hrE hr_lt]
      simp
    have hrootn2 : (Q p r).IsRoot (-(2 * (r : ZMod p) + 1)) := by
      rw [Polynomial.IsRoot]
      rw [← Qd_map p r]
      have hval : Int.castRingHom (ZMod p) (-(2 * (r : ℤ) + 1)) = -(2 * (r : ZMod p) + 1) := by
        simp
      rw [← hval]
      rw [Polynomial.eval_map_apply, Qd_eval_neg_two_r_add_one_eq_sign_cN r]
      simp only [map_mul, map_pow, map_neg, map_one]
      have hmap : (Int.castRingHom (ZMod p)) (cN r : ℤ) = (cN r : ZMod p) := by simp
      rw [hmap]
      rw [cN_cast_eq_zero_of_harmonicSum_two_mul_r_zero p r hrE hmid hH2r]
      simp
    have hdvd0 : p0 ∣ Q p r := by
      dsimp [p0]
      rw [Polynomial.dvd_iff_isRoot]
      exact hroot0
    have hdvdr : pr ∣ Q p r := by
      dsimp [pr]
      rw [Polynomial.dvd_iff_isRoot]
      exact hrootr
    have hdvdn1 : pn1 ∣ Q p r := by
      dsimp [pn1]
      rw [Polynomial.dvd_iff_isRoot]
      exact hrootn1
    have hdvdn2 : pn2 ∣ Q p r := by
      dsimp [pn2]
      rw [Polynomial.dvd_iff_isRoot]
      exact hrootn2
    have hne_0r : (0 : ZMod p) ≠ (r : ZMod p) := by
      intro h
      exact natCast_r_ne_zero p r h1r hr_lt h.symm
    have hne_0n1 : (0 : ZMod p) ≠ -((r : ZMod p) + 1) := by
      intro h
      have hz : ((r : ZMod p) + 1) = 0 := neg_eq_zero.mp h.symm
      have hznat : (((r + 1 : ℕ) : ZMod p) = 0) := by
        simpa [Nat.cast_add] using hz
      have hpdvd : p ∣ r + 1 := (ZMod.natCast_eq_zero_iff (r + 1) p).mp hznat
      have hge : 1 ≤ r + 1 := by omega
      have hlt : r + 1 < p := by omega
      exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
    have hne_0n2 : (0 : ZMod p) ≠ -(2 * (r : ZMod p) + 1) := by
      intro h
      have hz : (2 * (r : ZMod p) + 1) = 0 := neg_eq_zero.mp h.symm
      have hznat : (((2 * r + 1 : ℕ) : ZMod p) = 0) := by
        simpa [Nat.cast_add, Nat.cast_mul] using hz
      have hpdvd : p ∣ 2 * r + 1 := (ZMod.natCast_eq_zero_iff (2 * r + 1) p).mp hznat
      have hge : 1 ≤ 2 * r + 1 := by omega
      have hlt : 2 * r + 1 < p := by omega
      exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
    have hne_rn1 : (r : ZMod p) ≠ -((r : ZMod p) + 1) := by
      intro h
      have hsum : (r : ZMod p) + ((r : ZMod p) + 1) = 0 := by
        nth_rewrite 1 [h]
        simp
      have hznat : (((2 * r + 1 : ℕ) : ZMod p) = 0) := by
        have hcast : (((2 * r + 1 : ℕ) : ZMod p) = (r : ZMod p) + ((r : ZMod p) + 1)) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring
        rw [hcast, hsum]
      have hpdvd : p ∣ 2 * r + 1 := (ZMod.natCast_eq_zero_iff (2 * r + 1) p).mp hznat
      have hge : 1 ≤ 2 * r + 1 := by omega
      have hlt : 2 * r + 1 < p := by omega
      exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
    have hne_rn2 : (r : ZMod p) ≠ -(2 * (r : ZMod p) + 1) := by
      intro h
      have hsum : (r : ZMod p) + (2 * (r : ZMod p) + 1) = 0 := by
        nth_rewrite 1 [h]
        simp
      have hznat : (((3 * r + 1 : ℕ) : ZMod p) = 0) := by
        have hcast : (((3 * r + 1 : ℕ) : ZMod p) = (r : ZMod p) + (2 * (r : ZMod p) + 1)) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring
        rw [hcast, hsum]
      have hpdvd : p ∣ 3 * r + 1 := (ZMod.natCast_eq_zero_iff (3 * r + 1) p).mp hznat
      have hge : 1 ≤ 3 * r + 1 := by omega
      have hlt : 3 * r + 1 < p := by omega
      exact (not_lt_of_ge (Nat.le_of_dvd hge hpdvd)) hlt
    have hne_n1n2 : (-((r : ZMod p) + 1)) ≠ -(2 * (r : ZMod p) + 1) := by
      intro h
      have hinj : (r : ZMod p) + 1 = 2 * (r : ZMod p) + 1 := neg_inj.mp h
      have hz : (r : ZMod p) = 0 := by
        have h' := congrArg (fun t : ZMod p => t - ((r : ZMod p) + 1)) hinj
        have hmain : (2 * (r : ZMod p) + 1) - ((r : ZMod p) + 1) = (r : ZMod p) := by ring
        have hzero : ((r : ZMod p) + 1) - ((r : ZMod p) + 1) = 0 := by ring
        simpa [hmain, hzero] using h'.symm
      exact natCast_r_ne_zero p r h1r hr_lt hz
    have hcop (u v : ZMod p) (hne : u ≠ v) :
        IsCoprime (Polynomial.X - Polynomial.C u) (Polynomial.X - Polynomial.C v) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hne).isUnit
    have hcop_0r : IsCoprime p0 pr := by
      dsimp [p0, pr]
      exact hcop (0 : ZMod p) (r : ZMod p) hne_0r
    have hcop_0n1 : IsCoprime p0 pn1 := by
      dsimp [p0, pn1]
      exact hcop (0 : ZMod p) (-((r : ZMod p) + 1)) hne_0n1
    have hcop_0n2 : IsCoprime p0 pn2 := by
      dsimp [p0, pn2]
      exact hcop (0 : ZMod p) (-(2 * (r : ZMod p) + 1)) hne_0n2
    have hcop_rn1 : IsCoprime pr pn1 := by
      dsimp [pr, pn1]
      exact hcop (r : ZMod p) (-((r : ZMod p) + 1)) hne_rn1
    have hcop_rn2 : IsCoprime pr pn2 := by
      dsimp [pr, pn2]
      exact hcop (r : ZMod p) (-(2 * (r : ZMod p) + 1)) hne_rn2
    have hcop_n1n2 : IsCoprime pn1 pn2 := by
      dsimp [pn1, pn2]
      exact hcop (-((r : ZMod p) + 1)) (-(2 * (r : ZMod p) + 1)) hne_n1n2
    have hdvd01 : p0 * pr ∣ Q p r := hcop_0r.mul_dvd hdvd0 hdvdr
    have hcop01_n1 : IsCoprime (p0 * pr) pn1 := hcop_0n1.mul_left hcop_rn1
    have hdvd012 : (p0 * pr) * pn1 ∣ Q p r := hcop01_n1.mul_dvd hdvd01 hdvdn1
    have hcop01_n2 : IsCoprime (p0 * pr) pn2 := hcop_0n2.mul_left hcop_rn2
    have hcop012_n2 : IsCoprime ((p0 * pr) * pn1) pn2 := hcop01_n2.mul_left hcop_n1n2
    have hdvdFinal : ((p0 * pr) * pn1) * pn2 ∣ Q p r := hcop012_n2.mul_dvd hdvd012 hdvdn2
    rwa [hA]

/-! ## Reductions to the gcd identity -/

/-- The arithmetic remainder-content statement follows from the gcd identity. -/
theorem HA_arithmetic_remainder_content_of_HA_arithmetic_gcd_hN_cN_dvd_factorial
    (h : HA_arithmetic_gcd_hN_cN_dvd_factorial) : HA_arithmetic_remainder_content := by
  intro r hr1 p hp hpdvd
  have hgcd_dvd : (Polynomial.content (RemainderR r)).natAbs ∣ Nat.gcd (hN r) (cN r) :=
    content_RemainderR_natAbs_dvd_gcd_hN_cN r hr1
  have hp_dvd_gcd : p ∣ Nat.gcd (hN r) (cN r) := hpdvd.trans hgcd_dvd
  have hp_dvd_fact : p ∣ Nat.factorial (4 * r + 1) := hp_dvd_gcd.trans (h r hr1)
  exact (hp.dvd_factorial).mp hp_dvd_fact

/-- (B) `H_{2r} ≠ 0` follows from the arithmetic remainder-content statement. -/
theorem HA_mid_harmonicSum_two_mul_r_ne_zero_of_HA_arithmetic_remainder_content
    (h : HA_arithmetic_remainder_content) : HA_mid_harmonicSum_two_mul_r_ne_zero := by
  intro p r hp hmid hrE
  haveI : Fact p.Prime := ⟨hp⟩
  intro hH2r
  have hdvd : A_poly_mod p r ∣ Q p r :=
    (A_poly_mod_dvd_Q_iff_harmonicSum_two_mul_r_eq_zero p r hrE hmid).mpr hH2r
  have hp_dvd_content : p ∣ (Polynomial.content (RemainderR r)).natAbs :=
    (prime_dvd_content_RemainderR_iff_A_poly_mod_dvd_Q p r).mpr hdvd
  have hr1 : 1 ≤ r := mem_E_ge_one p r hrE
  have hle : p ≤ 4 * r + 1 := h r hr1 p hp hp_dvd_content
  omega

/-- The single gcd identity implies (B). -/
theorem HA_mid_harmonicSum_two_mul_r_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial
    (hGCD : HA_arithmetic_gcd_hN_cN_dvd_factorial) :
    HA_mid_harmonicSum_two_mul_r_ne_zero :=
  HA_mid_harmonicSum_two_mul_r_ne_zero_of_HA_arithmetic_remainder_content
    (HA_arithmetic_remainder_content_of_HA_arithmetic_gcd_hN_cN_dvd_factorial hGCD)

/-- The single gcd identity plus CR-freeness and the extension-free hypothesis imply
`res(F,G) ≠ 0`. -/
theorem HA_mid_resultant_F_G_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial_of_CR_free_of_no_extension
    (hGCD : HA_arithmetic_gcd_hN_cN_dvd_factorial)
    (hCR : HA_mid_CR_free)
    (hNoExt : HA_mid_no_extension_common_root_Qr_midTailDerivative) :
    HA_mid_resultant_F_G_ne_zero :=
  HA_mid_resultant_F_G_ne_zero_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
    (HA_mid_harmonicSum_two_mul_r_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial hGCD)
    hCR hNoExt

/-- The single gcd identity plus CR-freeness and the extension-free hypothesis imply
the separation lemma `HA_mid_remainder_coprime_Qr`. -/
theorem HA_mid_remainder_coprime_Qr_of_HA_arithmetic_gcd_hN_cN_dvd_factorial_of_CR_free_of_no_extension
    (hGCD : HA_arithmetic_gcd_hN_cN_dvd_factorial)
    (hCR : HA_mid_CR_free)
    (hNoExt : HA_mid_no_extension_common_root_Qr_midTailDerivative) :
    HA_mid_remainder_coprime_Qr := by
  have hH : HA_mid_harmonicSum_two_mul_r_ne_zero :=
    HA_mid_harmonicSum_two_mul_r_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial hGCD
  have hFG : HA_mid_resultant_F_G_ne_zero :=
    HA_mid_resultant_F_G_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial_of_CR_free_of_no_extension
      hGCD hCR hNoExt
  exact HA_mid_remainder_coprime_Qr_of_frontier hH hFG

/-- The full frontier follows from the gcd identity, CR-freeness and the
extension-free hypothesis. -/
theorem HA_frontier_of_HA_arithmetic_gcd_hN_cN_dvd_factorial_of_CR_free_of_no_extension
    (hGCD : HA_arithmetic_gcd_hN_cN_dvd_factorial)
    (hCR : HA_mid_CR_free)
    (hNoExt : HA_mid_no_extension_common_root_Qr_midTailDerivative) :
    HA_mid_harmonicSum_two_mul_r_ne_zero ∧ HA_mid_resultant_F_G_ne_zero ∧
      (∀ p r : ℕ, Nat.Prime p → 4 * r + 1 < p → r ∈ E p →
        ∀ β : ℕ, 1 ≤ β → β ≤ 2 * r → β ≠ r →
          ¬ (harmonicSum p β = harmonicSum p (β + r) ∧
            harmonicSum p β = harmonicSum p (2 * r - β))) := by
  have hB : HA_mid_harmonicSum_two_mul_r_ne_zero :=
    HA_mid_harmonicSum_two_mul_r_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial hGCD
  have hFG : HA_mid_resultant_F_G_ne_zero :=
    HA_mid_resultant_F_G_ne_zero_of_HA_arithmetic_gcd_hN_cN_dvd_factorial_of_CR_free_of_no_extension
      hGCD hCR hNoExt
  have hRes : HA_mid_resultant_Qr_midTailDerivative_ne_zero :=
    HA_mid_resultant_Qr_midTailDerivative_ne_zero_of_harmonicSum_two_mul_r_ne_zero_of_CR_free_of_no_extension
      hB hCR hNoExt
  exact HA_frontier_of_HA_mid_resultant_Qr_midTailDerivative_ne_zero hRes

end

end Erdos291
