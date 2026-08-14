import Erdos291.GapPolynomial
import Erdos291.BadSet
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Erdős #291 — the "finite exceptional primes" structure

For each fixed pair of distances `d ≠ e`, only finitely many primes can realize a triple
bad-position pattern `r, r + d, r + e ∈ E p`.  The mechanism is the *resultant*: over `ℤ` we form
the integer distance polynomial

    `Qd d = (∏_{i=1}^d (X + i))'`

whose reduction mod `p` is exactly the polynomial `Q p d` of `GapPolynomial`.  If `r, r + d,
r + e ∈ E p` then (by `eval_Q_eq_zero_of_mem_E_add`) both `Q p d` and `Q p e` vanish at `r` mod
`p`, i.e. they have a common root in the field `ZMod p`; a common root forces the resultant to
vanish, and `Polynomial.resultant_map_map` transports that to `p ∣ resultant (Qd d) (Qd e)`.
Since `resultant (Qd d) (Qd e)` is a fixed integer, only finitely many primes are exceptional.

This file provides:

* the integer distance polynomial `Qd d` and the reduction lemma `Qd_map`;
* the general fact that two polynomials over a field sharing a root have zero resultant
  (`resultant_eq_zero_of_commonRoot`);
* the main result `resultant_eq_zero_of_triple_bad`: a triple bad position forces
  `resultant (Qd d) (Qd e) ≡ 0 (mod p)`.

The companion *coprimality* statement (`d ≠ e ⟹ resultant (Qd d) (Qd e) ≠ 0`), which would
turn this into a genuine finiteness statement, is not yet formalized here (it needs a real-root
interlacing argument).
-/

open scoped BigOperators

namespace Erdos291

open Polynomial

/-- The integer distance polynomial `∏_{i=1}^d (X + i)` over `ℤ`. -/
noncomputable def Pd (d : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.Icc 1 d, (Polynomial.X + Polynomial.C (i : ℤ))

/-- The derivative `(Pd d)'` of the integer distance polynomial. -/
noncomputable def Qd (d : ℕ) : Polynomial ℤ :=
  Polynomial.derivative (Pd d)

/-! ## Reduction to `ZMod p` -/

/-- `Pd d` is monic. -/
lemma Pd_monic (d : ℕ) : (Pd d).Monic := by
  rw [Pd]
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_add_C (i : ℤ)

/-- `Pd d` has degree `d`. -/
lemma Pd_natDegree (d : ℕ) : (Pd d).natDegree = d := by
  rw [Pd]
  have hmonic : ∀ i ∈ Finset.Icc 1 d, Monic (Polynomial.X + Polynomial.C (i : ℤ)) := by
    intro i hi
    exact Polynomial.monic_X_add_C (i : ℤ)
  rw [Polynomial.natDegree_prod_of_monic (Finset.Icc 1 d)
    (fun i => Polynomial.X + Polynomial.C (i : ℤ)) hmonic]
  simp only [Polynomial.natDegree_X_add_C]
  rw [← Finset.card_eq_sum_ones, Nat.card_Icc]
  omega

/-- The reduction of `Pd d` mod `p` is `P p d`. -/
lemma Pd_map (p d : ℕ) : (Pd d).map (Int.castRingHom (ZMod p)) = P p d := by
  rw [Pd, P]
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  simp

/-- The reduction of `Qd d` mod `p` is `Q p d`. -/
lemma Qd_map (p d : ℕ) : (Qd d).map (Int.castRingHom (ZMod p)) = Q p d := by
  rw [Qd, Q]
  rw [← Polynomial.derivative_map (Pd d) (Int.castRingHom (ZMod p))]
  exact congrArg Polynomial.derivative (Pd_map p d)

/-! ## Degree of `Qd` -/

/-- `Qd d` has degree `d - 1`. -/
lemma Qd_natDegree (d : ℕ) : (Qd d).natDegree = d - 1 := by
  rw [Qd, Polynomial.natDegree_derivative, Pd_natDegree d]

/-! ## Common roots force zero resultant -/

/-- Over a field, if two polynomials share a common root then their resultant vanishes, at any
degree parameters at least the true degrees (and with `m + n` positive). -/
lemma resultant_eq_zero_of_commonRoot {K : Type*} [Field K] (f g : K[X]) (m n : ℕ) (a : K)
    (hm : f.natDegree ≤ m) (hn : g.natDegree ≤ n)
    (haf : f.IsRoot a) (hag : g.IsRoot a) (hmn : 0 < m + n) :
    resultant f g m n = 0 := by
  by_cases hf : f = 0
  · by_cases hg : g = 0
    · rw [hf, hg, Polynomial.resultant_zero_zero]
      exact zero_pow (by omega : m + n ≠ 0)
    · have hgn : n ≠ 0 := by
        have hgdeg : 1 ≤ g.natDegree := by
          by_contra hneg
          have hdeg : g.natDegree = 0 := by omega
          obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
          have hc0 : c = 0 := by
            rw [← hc] at hag
            rw [Polynomial.IsRoot, Polynomial.eval_C] at hag
            exact hag
          rw [← hc, hc0] at hg
          simp at hg
        omega
      rw [hf, Polynomial.resultant_zero_left, zero_pow hgn]
      simp
  · have hdf : X - C a ∣ f := (Polynomial.dvd_iff_isRoot).mpr haf
    obtain ⟨fcoef, rfl⟩ := hdf
    have hfcoef : fcoef ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hf
      exact hf rfl
    have hlc : leadingCoeff (X - C a : K[X]) * leadingCoeff fcoef ≠ 0 := by
      rw [(Polynomial.monic_X_sub_C a).leadingCoeff, one_mul]
      exact mt Polynomial.leadingCoeff_eq_zero.mp hfcoef
    have hdegmul : ((X - C a : K[X]) * fcoef).natDegree =
        (X - C a : K[X]).natDegree + fcoef.natDegree :=
      Polynomial.natDegree_mul' hlc
    have hres0 : resultant ((X - C a : K[X]) * fcoef) g
        ((X - C a : K[X]) * fcoef).natDegree n = 0 := by
      rw [hdegmul, Polynomial.resultant_mul_left (X - C a) fcoef g n hn]
      rw [Polynomial.natDegree_X_sub_C]
      rw [Polynomial.resultant_X_sub_C_left g n a hn]
      rw [hag.eq_zero]
      simp
    have hbump : resultant ((X - C a : K[X]) * fcoef) g m n = 0 := by
      have hk : ((X - C a : K[X]) * fcoef).natDegree +
          (m - ((X - C a : K[X]) * fcoef).natDegree) = m := by omega
      rw [← hk]
      rw [Polynomial.resultant_add_left_deg (f := (X - C a : K[X]) * fcoef) (g := g)
        (m := ((X - C a : K[X]) * fcoef).natDegree) (n := n)
        (k := m - ((X - C a : K[X]) * fcoef).natDegree) le_rfl]
      rw [hres0]
      simp
    exact hbump

/-! ## The main resultant implication -/

/-- **The resultant implication.**  If `r, r + d, r + e` are all bad digits mod `p` (with
`r + max d e ≤ p - 1`), then the integer resultant `resultant (Qd d) (Qd e)` is divisible by
`p`.  Equivalently, its reduction in `ZMod p` is zero. -/
theorem resultant_eq_zero_of_triple_bad (p d e r : ℕ) [Fact p.Prime]
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (hr : r ∈ E p) (hradd : r + d ∈ E p) (hre : r + e ∈ E p)
    (hle : r + max d e ≤ p - 1) :
    ((Polynomial.resultant (Qd d) (Qd e) : ℤ) : ZMod p) = 0 := by
  by_cases hde1 : d = 1 ∧ e = 1
  · rcases hde1 with ⟨rfl, rfl⟩
    have hle' : r + 1 ≤ p - 1 := by simpa using hle
    have hp2 : 2 ≤ p := by omega
    have hnot : r + 1 ∉ E p := not_mem_E_succ p r hp2 hr
    exact False.elim (hnot hradd)
  · have hle_d : r + d ≤ p - 1 :=
      le_trans (Nat.add_le_add_left (Nat.le_max_left d e) r) hle
    have hle_e : r + e ≤ p - 1 :=
      le_trans (Nat.add_le_add_left (Nat.le_max_right d e) r) hle
    have hQdr : Polynomial.eval (r : ZMod p) (Q p d) = 0 :=
      eval_Q_eq_zero_of_mem_E_add p d r hd hr hradd hle_d
    have hQer : Polynomial.eval (r : ZMod p) (Q p e) = 0 :=
      eval_Q_eq_zero_of_mem_E_add p e r he hr hre hle_e
    have hroot_d : ((Qd d).map (Int.castRingHom (ZMod p))).IsRoot (r : ZMod p) := by
      change ((Qd d).map (Int.castRingHom (ZMod p))).eval (r : ZMod p) = 0
      rw [Qd_map p d]
      exact hQdr
    have hroot_e : ((Qd e).map (Int.castRingHom (ZMod p))).IsRoot (r : ZMod p) := by
      change ((Qd e).map (Int.castRingHom (ZMod p))).eval (r : ZMod p) = 0
      rw [Qd_map p e]
      exact hQer
    have hm_d : ((Qd d).map (Int.castRingHom (ZMod p))).natDegree ≤ (Qd d).natDegree :=
      Polynomial.natDegree_map_le
    have hm_e : ((Qd e).map (Int.castRingHom (ZMod p))).natDegree ≤ (Qd e).natDegree :=
      Polynomial.natDegree_map_le
    have hmn : 0 < (Qd d).natDegree + (Qd e).natDegree := by
      rw [Qd_natDegree d, Qd_natDegree e]
      have hde : d ≠ 1 ∨ e ≠ 1 := by
        by_cases hd1 : d = 1
        · right
          intro he1
          exact hde1 ⟨hd1, he1⟩
        · left
          exact hd1
      omega
    have hres : Polynomial.resultant ((Qd d).map (Int.castRingHom (ZMod p)))
        ((Qd e).map (Int.castRingHom (ZMod p))) (Qd d).natDegree (Qd e).natDegree = 0 :=
      resultant_eq_zero_of_commonRoot ((Qd d).map (Int.castRingHom (ZMod p)))
        ((Qd e).map (Int.castRingHom (ZMod p)))
        (Qd d).natDegree (Qd e).natDegree (r : ZMod p)
        hm_d hm_e hroot_d hroot_e hmn
    rw [Polynomial.resultant_map_map] at hres
    simpa using hres

end Erdos291
