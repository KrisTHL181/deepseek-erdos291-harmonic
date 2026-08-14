# Erdos291 — Formalization of Erdős problem #291

100% DeepSeek v4 Pro GA proof — every theorem, proof, and piece of exposition
in this repository was generated end-to-end by the DeepSeek v4 Pro GA model.

A Lean 4 / Mathlib formalization of [Erdős problem #291](https://www.erdosproblems.com/291).

## Problem

Let

- `L n = lcm(1, …, n)`,
- `a n = ∑_{k=1}^n L n / k`,

so that the harmonic number satisfies `H_n = a_n / L_n`. Erdős #291 asks whether both

- `gcd(a_n, L_n) = 1`, and
- `gcd(a_n, L_n) > 1`

occur infinitely often.

The `gcd > 1` direction is fully resolved: this repository proves it unconditionally via the
infinite family `n = 2 · 3^(e+1)`. The `gcd = 1` direction is the open Shiu (2016) conjecture;
this repository formalizes several conditional derivations and a large body of supporting
structure for the bad-digit sets involved.

## Status

- `lake build` succeeds with Lean 4.34.0-rc1 / Mathlib.
- There are no `sorry`, `admit`, `axiom`, or `unsafe` declarations in `Erdos291/`; all statements are proved.
- 31 Lean modules, roughly 9000 lines, over 70 named theorems.

## Core definitions

| Name | Definition |
|---|---|
| `L n` | `Nat.lcmUpto n`, the lcm of `1, …, n` |
| `a n` | `∑_{k=1}^n L n / k`, the numerator of `H_n` over the common denominator `L n` |
| `E p` | bad base-`p` digits: `r ∈ [1, p-1]` such that `p ∣ numerator(H_r)` |
| `G x` | number of `n ≤ x` with `gcd(a n, L n) = 1` |
| `c p` | bad-digit density `|E p| / (p-1)` |

## Formalized results

### Unconditional direction

- `GcdPositive.gcd_gt_one_infinitely_often`:
  `gcd(a n, L n) > 1` for infinitely many `n`, witnessed by `n = 2 · 3^(e+1)`.
- `GcdPositive.three_dvd_gcd_two_mul_pow_three`:
  `3 ∣ gcd(a_{2·3^(e+1)}, L_{2·3^(e+1)})`.

### Core characterization

- `Characterization.dvd_a_iff_sum_inv_eq_zero`:
  for a prime `p ≤ n`, `p ∣ a n` iff the leading base-`p` digit inverse sum
  `∑_{j=1}^{r_p} j⁻¹` vanishes in `ZMod p`, where `r_p = n / p ^ Nat.log p n`.

### Bad-set structure

- `BadSet.wolstenholme_mem_E`: `p - 1 ∈ E p` for every odd prime `p`.
- `BadSet.mem_E_iff_pm_sub`: symmetry `r ∈ E p ↔ p - 1 - r ∈ E p`.
- `BadSet.not_mem_E_succ`: no two adjacent bad digits.
- `BadSet.E_card_le_half` and `GcdOne.c_le_one_half`:
  `|E p| ≤ (p-1)/2`, i.e. `c p ≤ 1/2`, for every prime `p`.
- `DoubleCount.sum_E_card_eq_double_count`: double-count identity for `∑ |E p|`.
- `DoubleCount.E_card_odd_iff_mid_not_mem`: parity law for `|E p|`.
- `DoubleCount.E_eleven`, `E_twentynine`, `E_hundred_nine`, `E_thousand_ninety_three`: computed tables.
- `HAProgress.c_ge_inv_pred`: `1/(p-1) ≤ c p` from Wolstenholme.
- `HAProgress.count_pbad_in_decade`: in a base-`p` decade, the count of `p`-bad `n` is exactly `|E p| · p^e`.

### Distance polynomials and bad-set growth

- `GapPolynomial.eval_Q_eq_zero_of_mem_E_add`: if `r, r+d ∈ E p`, then the distance polynomial `Q p d` vanishes at `r`.
- `GapPolynomial.E_add_count_le_pred`: `#{r | r, r+d ∈ E p} ≤ d-1`.
- `BadSetGrowth.E_card_cube_le`: `|E p|³ ≤ 64 p²`, hence `|E p| ≪ p^(2/3)` unconditionally.
- `GapResultant.resultant_eq_zero_of_triple_bad`: a triple bad position forces the resultant to vanish mod `p`.
- `GapCoprime.resultant_Qd_ne_zero` and `GapCoprime.finite_exceptional_primes`: for fixed `d ≠ e`, only finitely many primes admit `r, r+d, r+e ∈ E p`.
- `GapResultantHeight.exceptional_prime_mass_le`: quantitative bound on the reciprocal mass of those exceptional primes.

### Bernoulli / Eisenstein / Wieferich

- `Bernoulli.num_dvd_iff_bernoulli`: `p ∣ numerator(H_r)` iff `B_{p-1}(r+1) - B_{p-1} ≡ 0` in `ZMod p`.
- `Eisenstein.eisenstein_congruence`: Eisenstein's congruence relating the half harmonic sum to the Fermat quotient.
- `Eisenstein.mid_digit_mem_E_iff_wieferich`: `(p-1)/2 ∈ E p` iff `p² ∣ 2^(p-1) - 1` (base-2 Wieferich prime).
- `OddHarmonicWalk.oddWalk_mid_eq_fermatQuotient`: the odd-harmonic walk endpoint is the Fermat quotient.
- `OddHarmonicWalk.mem_E_iff_oddWalk_eq`: lower-half bad digits are return times of the odd-harmonic walk.

### Analytic number theory

- `Mertens.sum_inv_pred_tendsto_atTop` and `Mertens.sum_c_tendsto_atTop`: divergence of the bad-density sums.
- `MertensUpper.sum_one_div_primes_le_loglog`: explicit Mertens upper bound `∑ 1/p = O(log log x)`.
- `BulkRemoval.tail_sum_p_gt_r_sq_le_loglog`: unconditional removal of the `p > r²` bulk from a weighted double sum.

### Conditional `gcd = 1` direction

The following theorems all derive the open Shiu conjecture conclusion under explicit hypotheses:

- `GcdOne.gcd_eq_one_infinite`: `HA_dist` + `HA_arith` ⇒ infinitely many `n` with `gcd(a n, L n) = 1`.
- `GcdOneWeak.gcd_eq_one_infinite_of_S_o_log`: `HA_dist` + `HA_arith_weak` ⇒ infinitely many good `n`.
- `HAShell.HA_shell_implies_infinite`: the shell hypothesis `HA_shell` ⇒ infinitely many good `n`.
- `HAShell.HA_shell_weak_iff_infinite`: `HA_shell_weak` is exactly equivalent to infinitely many good `n`.
- `HABrun.HA_Brun_implies_infinite`: the finite-order Brun condition `HA_Brun` ⇒ infinitely many good `n`.

### Moment and reduction machinery

- `SecondMoment.HA_arith_of_HA_second_moment`: `M x = O(log log x)` ⇒ `HA_arith`.
- `WeakSecondMoment.HA_arith_weak_of_HA_second_weak`: `M x = o(log x)` ⇒ `HA_arith_weak`.
- `Reductions.HA_arith_implies_HA_arith_weak` and `Reductions.HA_second_moment_implies_HA_arith_weak`.
- `SecondMomentDoubleCount.M_eq_two_mul_sum_dist`: second moment as a double sum over distances.
- `SecondMomentDoubleCount.M_le_pair_wall`: the spacing bound alone gives a polynomial wall.
- `ShortGapMoment.MleD_le` and `MleD_le_loglog`: unconditional short-gap second-moment bound.
- `SymmetryOrbits.E_card_eq_one_add_w_add_two_mul_T_card`: orbit decomposition `|E p| = 1 + w p + 2|T p|`.
- `SymmetryOrbits.HA_arith_weak_iff_Aextra_o_log`: `HA_arith_weak` is equivalent to `Aextra x = o(log x)`.
- `PairGCD.A_shift`: `A_{r+d} = P_d(r) A_r + r! Q_d(r)`.
- `PairGCD.pair_bad_iff_prime_dvd_gcd`: `r, r+d ∈ E p` iff `p ∣ gcd(A_r, Q_d(r))`.
- `ShellMoments.mu_one_eq_lambda` and `mu_eq_factorialMoment_div`: shell factorial moments and the Bonferroni bridge.
- `SecondMomentBridge.two_mul_mu_two_eq_lambda_sq_sub_sum_beta_sq_add_crossCov`: exact decomposition of the order-2 Brun error.

## Hypotheses used for the open direction

These are `Prop` definitions in the code; none is proved in this repository. They are the
explicit assumptions under which the open `gcd = 1` direction is derived.

| Hypothesis | Meaning |
|---|---|
| `HA_dist` | `G x ≥ (1 - ε x) · x · ∏_{p≤x} (1 - c p)` for some `ε x → 0` |
| `HA_arith` | `∑_{p≤x} c p = O(log log x)` |
| `HA_arith_weak` | `S x = o(log x)`, where `S x = ∑_{p≤x} c p` |
| `HA_second_moment` | `M x = O(log log x)` |
| `HA_second_weak` | `M x = o(log x)` |
| `HA_shell` | infinitely many dyadic shells have positive `ΔG(X)` at a quantitative level |
| `HA_shell_weak` | infinitely many dyadic shells have `ΔG(X) > 0` |
| `HA_Brun` | a finite-order Brun error bound holds at infinitely many `X` |

The `gcd > 1` direction and all bad-set structural results are unconditional.

## Module index

| Module | Contents |
|---|---|
| `Basic` | Definitions of `L n` and `a n` |
| `Characterization` | Leading-digit characterization `p ∣ a n ⟺ Σ j⁻¹ = 0` |
| `GcdPositive` | Unconditional `gcd > 1` infinitely often |
| `BadSet` | Bad set `E`, count `G`, density `c`; Wolstenholme, symmetry, no-adjacent bound |
| `DoubleCount` | Double-count identity, parity law, finite tables |
| `Bernoulli` | Bernoulli characterization of bad digits |
| `Mertens` | Divergence of `∑ c p` |
| `MertensUpper` | Explicit Mertens upper bound |
| `HAProgress` | Lower bound `c p ≥ 1/(p-1)`; decade bad-count formula |
| `GcdOne` | Conditional `gcd = 1` from `HA_dist` + `HA_arith` |
| `GcdOneWeak` | Conditional `gcd = 1` from `HA_dist` + `HA_arith_weak` |
| `HAShell` | Shell hypothesis and equivalence to the conclusion |
| `BulkRemoval` | Unconditional `p > r²` bulk removal |
| `Bonferroni` | Factorial-moment inclusion-exclusion |
| `ShellMoments` | Shell factorial moments `μ_j`, `λ_X`, `β_p` |
| `SecondMoment` | `HA_second_moment` ⇒ `HA_arith` |
| `GapPolynomial` | Distance polynomial and spacing bound |
| `GapResultant` | Resultant bridge for triple bad patterns |
| `BadSetGrowth` | `|E p|³ ≤ 64 p²` |
| `HABrun` | Brun condition ⇒ infinitely many good `n` |
| `GapCoprime` | Coprimality of distance polynomials via Rolle |
| `SecondMomentDoubleCount` | Second moment as a distance double sum |
| `SecondMomentBridge` | Shell row/column bridge for order-2 moments |
| `WeakSecondMoment` | `HA_second_weak` ⇒ `HA_arith_weak` |
| `ShortGapMoment` | Unconditional short-gap second-moment bound |
| `PairGCD` | Pair gcd criterion via `A_r = r! H_r` |
| `SymmetryOrbits` | Involution orbit decomposition; `Aextra = o(log x)` equivalence |
| `GapResultantHeight` | Quantitative exceptional-prime mass bound |
| `OddHarmonicWalk` | Odd-harmonic walk and return-time characterization |
| `Reductions` | Hypothesis implication bookkeeping |
| `Eisenstein` | Eisenstein congruence and Wieferich middle-digit theorem |

## Building

```bash
lake build
```

The root library module `Erdos291.lean` imports all modules. The executable target `erdos291`
is defined in `Main.lean` and just prints `Erdos291`.
