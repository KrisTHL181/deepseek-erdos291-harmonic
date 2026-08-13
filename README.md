# Erdos291 — formalization of Erdős problem #291

100% DeepSeek v4 Pro GA proof — every theorem, proof, and piece of exposition
in this repository was generated end-to-end by the DeepSeek v4 Pro GA model.

A Lean 4 / Mathlib formalization of [Erdős problem #291](https://www.erdosproblems.com/291):
the fully-resolved `gcd > 1` direction, plus the **conditional** `gcd = 1` direction
(the open Shiu conjecture) under two explicit hypotheses.

## The problem

Let `L_n = lcm(1, …, n)` and let `a_n` be defined by `∑_{k=1}^n 1/k = a_n / L_n`
(i.e. `a_n = ∑_{k=1}^n L_n / k`, the numerator of the harmonic number `H_n` over the
common denominator `L_n`). Erdős #291 asks: do both `gcd(a_n, L_n) = 1` and
`gcd(a_n, L_n) > 1` occur infinitely often?

* **`gcd > 1` infinitely often** — **formalized here** (the easy direction, fully resolved).
* **`gcd = 1` infinitely often** — the open Shiu (2016) conjecture; formalized here
  **conditionally** on two hypotheses `HA_dist` and `HA_arith`.

## What is proved

### `gcd > 1` infinitely often (`Erdos291.GcdPositive`)

```lean
theorem three_dvd_gcd_two_mul_pow_three (e : ℕ) :
    3 ∣ Nat.gcd (a (2 * 3 ^ (e + 1))) (L (2 * 3 ^ (e + 1)))

theorem gcd_gt_one_infinitely_often :
    Set.Infinite {n : ℕ | 1 < Nat.gcd (a n) (L n)}
```

So `gcd(a_n, L_n) > 1` for the infinite family `n = 2 · 3^(e+1)`.

### The characterization (`Erdos291.Characterization`)

```lean
theorem dvd_a_iff_sum_inv_eq_zero (p n : ℕ) [Fact p.Prime] (hpn : p ≤ n) :
    p ∣ a n ↔
      (∑ j ∈ Finset.Icc 1 (n / p ^ Nat.log p n), ((j : ZMod p)⁻¹)) = 0
```

i.e. `p` divides `a_n` iff the "leading-digit" harmonic sum `Σ_{j=1}^{r_p} j⁻¹`
vanishes modulo `p`, where `r_p = n / p^⌊log_p n⌋` is the leading base-`p` digit of `n`.
For `n = 2 · 3^(e+1)` the leading base-3 digit is `2`, and `1 + 1/2 = 3/2 ≡ 0 (mod 3)`.

### The bad set `E p` (`Erdos291.BadSet`)

`E p` collects the *bad* base-`p` digits `r ∈ [1, p-1]` with `p ∣ numerator(H_r)`; the
count of good `n ≤ x` is `G x`, and `c p = |E p| / (p - 1)` is the bad-digit density.

* **Wolstenholme** (`wolstenholme_mem_E`): `p - 1 ∈ E p` for every odd prime `p`.
* **Pairing symmetry** (`mem_E_iff_pm_sub`): `r ∈ E p ↔ p - 1 - r ∈ E p`.
* **No two adjacent bad digits** (`not_mem_E_succ`): `r ∈ E p` implies `r + 1 ∉ E p`.
* **`|E p| ≤ (p - 1) / 2`, i.e. `c p ≤ 1/2`** (`E_card_le_half`): the `(p - 1) / 2`
  consecutive pairs `{1, 2}, {3, 4}, …` each hold at most one bad digit. This bound is
  **unconditional for every prime** `p` and is the elementary input that makes the
  product estimate in `GcdOne` uniform.

### The `gcd = 1` direction, conditionally (`Erdos291.GcdOne`)

The open Shiu conjecture is proved here from two hypotheses:

```lean
def HA_dist  : Prop :=  -- G x ≥ (1 - ε x) · x · ∏_{p ≤ x} (1 - c p),  ε x → 0
def HA_arith : Prop :=  -- ∑_{p ≤ x} c p ≤ C · log (log x)
```

```lean
theorem gcd_eq_one_infinite (hdist : HA_dist) (harith : HA_arith) :
    Set.Infinite {n : ℕ | Nat.gcd (a n) (L n) = 1}
```

The chain is fully proved: `c p ≤ 1/2` (`c_le_one_half`) gives the elementary
`log(1 - t) ≥ -2t`, so `HA_arith` forces `∏_{p≤x} (1 - c p) ≥ K · (log x)^{-M}`,
which together with `HA_dist` gives `G x ≥ (K/2) · x / (log x)^M → ∞`. Neither
hypothesis is currently known unconditionally; see the full report
`erdos_291_full_report.md` for why (the missing "uniform Kronecker bound" `H_A`).

## Key ingredients (from Mathlib)

* `Nat.lcmUpto` and `Nat.factorization_lcmUpto` — the lcm `lcm(1..n)` and the identity
  `v_p(lcm(1..n)) = ⌊log_p n⌋` (in `Mathlib.NumberTheory.Chebyshev`).
* `harmonic : ℕ → ℚ` (in `Mathlib.NumberTheory.Harmonic.Defs`).
* `ZMod p` with its field structure for prime `p`, and `padicValNat`.

## Building

```
lake build
```
