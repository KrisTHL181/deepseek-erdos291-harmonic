# Erdos291 — formalization of Erdős problem #291

100% DeepSeek v4 Pro GA proof — every theorem, proof, and piece of exposition
in this repository was generated end-to-end by the DeepSeek v4 Pro GA model.

A Lean 4 / Mathlib formalization of the *resolved direction* of [Erdős problem #291](https://www.erdosproblems.com/291).

## The problem

Let `L_n = lcm(1, …, n)` and let `a_n` be defined by `∑_{k=1}^n 1/k = a_n / L_n`
(i.e. `a_n = ∑_{k=1}^n L_n / k`, the numerator of the harmonic number `H_n` over the
common denominator `L_n`). Erdős #291 asks: do both `gcd(a_n, L_n) = 1` and
`gcd(a_n, L_n) > 1` occur infinitely often?

* **`gcd > 1` infinitely often** — **formalized here** (this is the easy direction).
* **`gcd = 1` infinitely often** — the open Shiu (2016) conjecture, not resolved.

## What is proved

The module `Erdos291.GcdPositive` proves

```lean
theorem three_dvd_gcd_two_mul_pow_three (e : ℕ) :
    3 ∣ Nat.gcd (a (2 * 3 ^ (e + 1))) (L (2 * 3 ^ (e + 1)))
```

so `gcd(a_n, L_n) > 1` for the infinite family `n = 2 · 3^(e+1)`.

Its main input is the characterization in `Erdos291.Characterization`:

```lean
theorem dvd_a_iff_sum_inv_eq_zero (p n : ℕ) [Fact p.Prime] (hpn : p ≤ n) :
    p ∣ a n ↔
      (∑ j ∈ Finset.Icc 1 (n / p ^ Nat.log p n), ((j : ZMod p)⁻¹)) = 0
```

i.e. `p` divides `a_n` iff the "leading-digit" harmonic sum `Σ_{j=1}^{r_p} j⁻¹`
vanishes modulo `p`, where `r_p = n / p^⌊log_p n⌋` is the leading base-`p` digit of `n`.
For `n = 2 · 3^(e+1)` the leading base-3 digit is `2`, and `1 + 1/2 = 3/2 ≡ 0 (mod 3)`.

## Key ingredients (from Mathlib)

* `Nat.lcmUpto` and `Nat.factorization_lcmUpto` — the lcm `lcm(1..n)` and the identity
  `v_p(lcm(1..n)) = ⌊log_p n⌋` (in `Mathlib.NumberTheory.Chebyshev`).
* `harmonic : ℕ → ℚ` (in `Mathlib.NumberTheory.Harmonic.Defs`).
* `ZMod p` with its field structure for prime `p`, and `padicValNat`.

## Building

```
lake build
```
