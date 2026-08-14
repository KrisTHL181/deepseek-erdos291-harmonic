import Erdos291.BadSet
import Erdos291.Eisenstein
import Erdos291.SymmetryOrbits
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

/-!
# Erdős #291 — the odd-harmonic walk coordinate

For an odd prime `p`, let `m := (p - 1) / 2`.  This file introduces the *odd-harmonic
walk*

    `C_t = ∑_{j=0}^{t-1} (2j+1)⁻¹  (mod p)`,

the partial sums of the inverses of the odd residues.  The two main facts are:

1. The endpoint `C_m` is the Fermat quotient `q_p(2) = (2^(p-1) - 1) / p`.  This follows
   from the split `H_{p-1} = C_m + (1/2) H_m` (separate the even and odd indices of the
   full harmonic sum), together with Wolstenholme's `H_{p-1} ≡ 0` and Eisenstein's
   `H_m ≡ -2 · q_p(2)`.

2. The lower-half bad digits are exactly the *return times* of the walk: for
   `1 ≤ r ≤ m`,

       `r ∈ E p  ↔  C_{m-r} = C_m`.

   The crux is the shift identity `C_m - C_{m-r} = -(1/2) H_r`, obtained by reindexing
   the tail `∑_{j=m-r}^{m-1} (2j+1)⁻¹` with `k = m - j` and using `2j + 1 = p - 2k`.
-/

open scoped BigOperators

namespace Erdos291

noncomputable section

/-- The odd-harmonic walk `C_t = ∑_{j=0}^{t-1} 1/(2j+1) (mod p)`. -/
noncomputable def oddWalk (p t : ℕ) : ZMod p :=
  ∑ j ∈ Finset.range t, ((2 * j + 1 : ℕ) : ZMod p)⁻¹

/-! ## Two elementary reindexings -/

/-- The even/odd split of `Icc 1 (2m)`: the odd indices are `2i+1` for `i ∈ range m` and
the even indices are `2i` for `i ∈ Icc 1 m`. -/
lemma sum_Icc_one_mul_two {α : Type*} [AddCommMonoid α] (m : ℕ) (f : ℕ → α) :
    (∑ j ∈ Finset.Icc 1 (2 * m), f j) =
      (∑ i ∈ Finset.range m, f (2 * i + 1)) + (∑ i ∈ Finset.Icc 1 m, f (2 * i)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        (∑ j ∈ Finset.Icc 1 (2 * (m + 1)), f j)
            = (∑ j ∈ Finset.Icc 1 (2 * m), f j) + f (2 * m + 1) + f (2 * m + 2) := by
                rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
                rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (2 * m + 1) + 1)]
                rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 2 * m + 1)]
        _ = ((∑ i ∈ Finset.range m, f (2 * i + 1)) + (∑ i ∈ Finset.Icc 1 m, f (2 * i)))
              + f (2 * m + 1) + f (2 * m + 2) := by rw [ih]
        _ = (∑ i ∈ Finset.range (m + 1), f (2 * i + 1))
              + (∑ i ∈ Finset.Icc 1 (m + 1), f (2 * i)) := by
                rw [Finset.sum_range_succ]
                rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
                rw [show 2 * m + 2 = 2 * (m + 1) by omega]
                ac_rfl

/-- Reindex `Ico (m-r) m` onto `Icc 1 r` via the involution `j ↦ m - j`. -/
lemma sum_Ico_sub_eq_sum_Icc {α : Type*} [AddCommMonoid α] (m r : ℕ) (hr : r ≤ m) (f : ℕ → α) :
    (∑ j ∈ Finset.Ico (m - r) m, f j) = ∑ k ∈ Finset.Icc 1 r, f (m - k) := by
  refine Finset.sum_bij (fun j _ => m - j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_Icc]
    have hj' : m - r ≤ j ∧ j < m := Finset.mem_Ico.mp hj
    constructor <;> omega
  · intro j₁ hj₁ j₂ hj₂ h
    have hj₁' : j₁ < m := (Finset.mem_Ico.mp hj₁).2
    have hj₂' : j₂ < m := (Finset.mem_Ico.mp hj₂).2
    omega
  · intro k hk
    have hk' : 1 ≤ k ∧ k ≤ r := Finset.mem_Icc.mp hk
    refine ⟨m - k, ?_, ?_⟩
    · rw [Finset.mem_Ico]
      constructor <;> omega
    · omega
  · intro j hj
    have hj' : m - r ≤ j ∧ j < m := Finset.mem_Ico.mp hj
    have hmj : m - (m - j) = j := by omega
    rw [hmj]

/-- The unit identity behind the shift: for `k ≤ m` with `p = 2m + 1`,
`(2(m-k)+1)⁻¹ = -(1/2) · k⁻¹` in `ZMod p`, because `2(m-k)+1 = p - 2k`. -/
lemma term_shift_inv (p m k : ℕ) [Fact p.Prime] (hp_eq : p = 2 * m + 1) (hk : k ≤ m) :
    ((2 * (m - k) + 1 : ℕ) : ZMod p)⁻¹ = -((2 : ZMod p)⁻¹) * ((k : ℕ) : ZMod p)⁻¹ := by
  have h2k : 2 * k ≤ p := by omega
  have hnat : 2 * (m - k) + 1 = p - 2 * k := by omega
  rw [hnat]
  have hcast : ((p - 2 * k : ℕ) : ZMod p) = -((2 * k : ℕ) : ZMod p) := by
    rw [Nat.cast_sub h2k]
    simp
  rw [hcast, inv_neg, Nat.cast_mul, mul_inv_rev, mul_comm, neg_mul]
  simp

/-! ## The split `H_{p-1} = C_m + (1/2) H_m` -/

/-- The full harmonic sum `H_{p-1} = ∑_{j=1}^{p-1} j⁻¹` splits into the odd-harmonic walk
`C_m` plus half of the half-harmonic sum `H_m`. -/
lemma sum_inv_pred_eq_oddWalk_add_half_H (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    (∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod p)⁻¹)) =
      oddWalk p ((p - 1) / 2) +
        (2 : ZMod p)⁻¹ * (∑ j ∈ Finset.Icc 1 ((p - 1) / 2), ((j : ZMod p)⁻¹)) := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  have hdiv : 2 ∣ p - 1 := by
    rcases hodd with ⟨k, hk⟩
    use k
    omega
  have hp_eq : 2 * ((p - 1) / 2) = p - 1 := by
    have hmul : ((p - 1) / 2) * 2 = p - 1 := Nat.div_mul_cancel hdiv
    omega
  have hsplit := sum_Icc_one_mul_two ((p - 1) / 2) (fun j => ((j : ZMod p)⁻¹))
  have hsplit' : (∑ j ∈ Finset.Icc 1 (p - 1), ((j : ZMod p)⁻¹)) =
      (∑ i ∈ Finset.range ((p - 1) / 2), ((2 * i + 1 : ℕ) : ZMod p)⁻¹) +
        (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), ((2 * i : ℕ) : ZMod p)⁻¹) := by
    simpa [hp_eq] using hsplit
  have heven : (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), ((2 * i : ℕ) : ZMod p)⁻¹) =
      (2 : ZMod p)⁻¹ * (∑ i ∈ Finset.Icc 1 ((p - 1) / 2), ((i : ℕ) : ZMod p)⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_mul, mul_inv_rev, mul_comm]
    simp
  rw [hsplit', oddWalk, heven]

/-! ## The shift `C_m - C_{m-r} = -(1/2) H_r` -/

/-- The shift identity: `C_m - C_{m-r} = -(1/2) H_r` for `r ≤ m`. -/
lemma oddWalk_sub_eq_neg_half_H (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hrle : r ≤ (p - 1) / 2) :
    oddWalk p ((p - 1) / 2) - oddWalk p ((p - 1) / 2 - r) =
      -((2 : ZMod p)⁻¹) * (∑ k ∈ Finset.Icc 1 r, ((k : ZMod p)⁻¹)) := by
  have hp' : Nat.Prime p := Fact.out
  have hodd : Odd p := Nat.Prime.odd_of_ne_two hp' (by omega : p ≠ 2)
  have hp_eq : p = 2 * ((p - 1) / 2) + 1 := by
    rcases hodd with ⟨k, rfl⟩
    omega
  have htail : oddWalk p ((p - 1) / 2) - oddWalk p ((p - 1) / 2 - r) =
      ∑ j ∈ Finset.Ico ((p - 1) / 2 - r) ((p - 1) / 2), ((2 * j + 1 : ℕ) : ZMod p)⁻¹ := by
    unfold oddWalk
    symm
    exact Finset.sum_Ico_eq_sub (fun j => ((2 * j + 1 : ℕ) : ZMod p)⁻¹)
      (Nat.sub_le ((p - 1) / 2) r)
  have hreindex : (∑ j ∈ Finset.Ico ((p - 1) / 2 - r) ((p - 1) / 2),
      ((2 * j + 1 : ℕ) : ZMod p)⁻¹) =
      ∑ k ∈ Finset.Icc 1 r, ((2 * ((p - 1) / 2 - k) + 1 : ℕ) : ZMod p)⁻¹ :=
    sum_Ico_sub_eq_sum_Icc ((p - 1) / 2) r hrle (fun j => ((2 * j + 1 : ℕ) : ZMod p)⁻¹)
  have hterms : (∑ k ∈ Finset.Icc 1 r, ((2 * ((p - 1) / 2 - k) + 1 : ℕ) : ZMod p)⁻¹) =
      ∑ k ∈ Finset.Icc 1 r, (-((2 : ZMod p)⁻¹) * ((k : ℕ) : ZMod p)⁻¹) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk_le : k ≤ (p - 1) / 2 := by
      have hkr : k ≤ r := (Finset.mem_Icc.mp hk).2
      omega
    exact term_shift_inv p ((p - 1) / 2) k hp_eq hk_le
  have hfactor : (∑ k ∈ Finset.Icc 1 r, (-((2 : ZMod p)⁻¹) * ((k : ℕ) : ZMod p)⁻¹)) =
      -((2 : ZMod p)⁻¹) * (∑ k ∈ Finset.Icc 1 r, ((k : ℕ) : ZMod p)⁻¹) := by
    rw [← Finset.mul_sum]
  calc
    oddWalk p ((p - 1) / 2) - oddWalk p ((p - 1) / 2 - r)
        = ∑ j ∈ Finset.Ico ((p - 1) / 2 - r) ((p - 1) / 2), ((2 * j + 1 : ℕ) : ZMod p)⁻¹ := htail
    _ = ∑ k ∈ Finset.Icc 1 r, ((2 * ((p - 1) / 2 - k) + 1 : ℕ) : ZMod p)⁻¹ := hreindex
    _ = ∑ k ∈ Finset.Icc 1 r, (-((2 : ZMod p)⁻¹) * ((k : ℕ) : ZMod p)⁻¹) := hterms
    _ = -((2 : ZMod p)⁻¹) * (∑ k ∈ Finset.Icc 1 r, ((k : ℕ) : ZMod p)⁻¹) := hfactor

/-! ## The endpoint `C_m = q_p(2)` -/

/-- The endpoint of the walk is the Fermat quotient: `C_m ≡ q_p(2) (mod p)`. -/
theorem oddWalk_mid_eq_fermatQuotient (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) :
    oddWalk p ((p - 1) / 2) = (fermatQuotient p : ZMod p) := by
  have hsplit := sum_inv_pred_eq_oddWalk_add_half_H p hp
  have hwolsten := sum_inv_Icc_one_pred_eq_zero p hp
  have heis := eisenstein_congruence p hp
  have htwo : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := by
    rw [ZMod.mul_inv_of_unit (2 : ZMod p)]
    exact two_isUnit p hp
  have hzero : oddWalk p ((p - 1) / 2) + (2 : ZMod p)⁻¹ *
      (∑ j ∈ Finset.Icc 1 ((p - 1) / 2), ((j : ZMod p)⁻¹)) = 0 := by
    rw [← hsplit, hwolsten]
  rw [heis] at hzero
  have hq : (2 : ZMod p)⁻¹ * (-(2 : ZMod p) * ((fermatQuotient p : ℕ) : ZMod p)) =
      -((fermatQuotient p : ℕ) : ZMod p) := by
    rw [← mul_assoc (2 : ZMod p)⁻¹ (-(2 : ZMod p)) ((fermatQuotient p : ℕ) : ZMod p)]
    rw [mul_neg (2 : ZMod p)⁻¹ (2 : ZMod p)]
    rw [mul_comm (2 : ZMod p)⁻¹ (2 : ZMod p)]
    rw [htwo]
    ring
  rw [hq] at hzero
  have hsub : oddWalk p ((p - 1) / 2) - ((fermatQuotient p : ℕ) : ZMod p) = 0 := by
    simpa [sub_eq_add_neg] using hzero
  exact sub_eq_zero.mp hsub

/-! ## The main result: bad digits are return times -/

/-- The lower-half bad digits are exactly the return times of the odd-harmonic walk: for
`1 ≤ r ≤ (p-1)/2`, one has `r ∈ E p` iff `C_{(p-1)/2 - r} = C_{(p-1)/2}`. -/
theorem mem_E_iff_oddWalk_eq (p r : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hr : 1 ≤ r) (hrle : r ≤ (p - 1) / 2) :
    r ∈ E p ↔ oddWalk p ((p - 1) / 2 - r) = oddWalk p ((p - 1) / 2) := by
  have hrp : r < p := by
    apply lt_of_le_of_lt hrle
    apply lt_of_le_of_lt (Nat.div_le_self (p - 1) 2)
    omega
  constructor
  · intro hrE
    have hdvd : (p : ℤ) ∣ (harmonic r).num := by
      rw [E] at hrE
      exact (Finset.mem_filter.mp hrE).2
    have hH0 : (∑ k ∈ Finset.Icc 1 r, ((k : ZMod p)⁻¹)) = 0 :=
      (num_dvd_iff_sum_inv_zero p r hrp).mp hdvd
    have hshift := oddWalk_sub_eq_neg_half_H p r hp hrle
    have hdiff : oddWalk p ((p - 1) / 2) - oddWalk p ((p - 1) / 2 - r) = 0 := by
      rw [hshift, hH0, mul_zero]
    exact (sub_eq_zero.mp hdiff).symm
  · intro hwalk
    have hshift := oddWalk_sub_eq_neg_half_H p r hp hrle
    have hshift0 : oddWalk p ((p - 1) / 2) - oddWalk p ((p - 1) / 2 - r) = 0 := by
      rw [hwalk]
      exact sub_self (oddWalk p ((p - 1) / 2))
    have hH0mul : -(2 : ZMod p)⁻¹ * (∑ k ∈ Finset.Icc 1 r, ((k : ZMod p)⁻¹)) = 0 := by
      rw [← hshift, hshift0]
    have hunit : IsUnit (-(2 : ZMod p)⁻¹) := (two_isUnit p hp).inv.neg
    have hH0 : (∑ k ∈ Finset.Icc 1 r, ((k : ZMod p)⁻¹)) = 0 := by
      rw [mul_eq_zero] at hH0mul
      rcases hH0mul with h1 | h2
      · exfalso
        exact hunit.ne_zero h1
      · exact h2
    have hdvd : (p : ℤ) ∣ (harmonic r).num := (num_dvd_iff_sum_inv_zero p r hrp).mpr hH0
    rw [E]
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hr, le_trans hrle (Nat.div_le_self (p - 1) 2)⟩
    · exact hdvd

end

end Erdos291
