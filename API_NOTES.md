# Mathlib API inventory for Erdős #291

All signatures below were verified with `#check` in scratch files under `/tmp/`
run via `cd /mnt/Data/erdos/Erdos291 && lake env lean /tmp/checkN.lean`
(Lean 4.34.0-rc1, mathlib `.lake/packages/mathlib`). Names marked
`✗ DOES NOT EXIST` produced `unknownIdentifier` errors and must NOT be used.

Notation: `n.lcmUpto` is `Nat.lcmUpto n` (dot notation), `p.log n` is `Nat.log p n`.

---

## 0. Top-level definitions for the theorem

Let `p` be prime, `p ≤ n`, `e := Nat.log p n`, `r := n / p ^ e`.

- `L n  := Nat.lcmUpto n`  (already exists; `= (Finset.Icc 1 n).lcm id`)
- `a n  := ∑ k ∈ Finset.Icc 1 n, L n / k`   (NEW definition; an integer)
- `harmonic n : ℚ` is the harmonic number (already exists).

Then `harmonic n = (a n : ℚ) / (L n : ℚ)`, and the main theorem is
`p ∣ a n ↔ (∑ j ∈ Finset.Icc 1 r, (j : ZMod p)⁻¹) = 0`.

---

## 1. lcm of 1..n

Import: `Mathlib.Algebra.GCDMonoid.Finset` (Finset.lcm), `Mathlib.Data.Nat.GCD.Basic`
(Nat.lcm), `Mathlib.NumberTheory.Chebyshev` (Nat.lcmUpto).

```
Finset.lcm {α β} [CommMonoidWithZero α] [NormalizedGCDMonoid α] (s : Finset β) (f : β → α) : α
Finset.lcm_dvd_iff {s f a} : s.lcm f ∣ a ↔ ∀ b ∈ s, f b ∣ a
Finset.lcm_dvd     {s f a} : (∀ b ∈ s, f b ∣ a) → s.lcm f ∣ a
Finset.dvd_lcm     {s f b} (hb : b ∈ s) : f b ∣ s.lcm f
Finset.lcm_insert  {s f b} [DecidableEq β] : (insert b s).lcm f = GCDMonoid.lcm (f b) (s.lcm f)
Finset.lcm_singleton {f b} : {b}.lcm f = normalize (f b)
Finset.lcm_mono    (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f
Finset.lcm_congr / Finset.lcm_image / Finset.lcm_eq_lcm_image   (in same file; for reindexing)

Nat.lcm (m n : ℕ) : ℕ
Nat.lcm_dvd_iff {m n k} : m.lcm n ∣ k ↔ m ∣ k ∧ n ∣ k
Nat.lcm_dvd      {m n k} (H1 : m ∣ k) (H2 : n ∣ k) : m.lcm n ∣ k
Nat.dvd_lcm_left (m n) : m ∣ m.lcm n
Nat.dvd_lcm_right (m n) : n ∣ m.lcm n

Nat.lcmUpto (n : ℕ) : ℕ                       -- == (Finset.Icc 1 n).lcm id   <-- USE THIS FOR L n
Nat.lcmUpto_ne_zero (n) : n.lcmUpto ≠ 0
Nat.lcmUpto_pos (n) : 0 < n.lcmUpto
Nat.lcmUpto_dvd_factorial (n) : n.lcmUpto ∣ n !
Nat.lcmUpto_eq_prod_pow_log (n) : n.lcmUpto = ∏ p ∈ n.primesLE, p ^ log p n
```

`(Finset.Icc 1 n).lcm id` typechecks; `Nat.lcmUpto n` is exactly that, so the
cleanest `L n` is **`Nat.lcmUpto n`** (it already has all the lemmas).

---

## 2. Nat.log

Import: `Mathlib.Data.Nat.Log`.

```
Nat.log (b n : ℕ) : ℕ
(a) Nat.pow_log_le_self (b : ℕ) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x
(b) Nat.lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) (x : ℕ) : x < b ^ (log b x).succ
(c) Nat.log_monotone {b : ℕ} : Monotone (log b)
    Nat.log_mono_right {b n m} (h : n ≤ m) : log b n ≤ log b m
    Nat.log_mono {b c m n} (hc : 1 < c) (hb : c ≤ b) (hmn : m ≤ n) : log b m ≤ log c n
(d) Nat.log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x
    Nat.log_mul_base {b n} (hb : 1 < b) (hn : n ≠ 0) : log b (n * b) = log b n + 1

Nat.log_eq_iff {b m n} (h : m ≠ 0 ∨ 1 < b ∧ n ≠ 0) : log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1)
Nat.le_log_of_pow_le {b x y} (hb : 1 < b) (h : b ^ x ≤ y) : x ≤ log b y
Nat.log_of_lt {b n} (hb : n < b) : log b n = 0
Nat.log_le_self (b x) : log b x ≤ x
Nat.log_pos {b n} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n
Nat.log_eq_zero_iff {b n} : log b n = 0 ↔ n < b ∨ b ≤ 1
```

✗ DOES NOT EXIST: `Nat.log_mul`, `Nat.log_add`, `Nat.log_div`, `Nat.log_floor`,
`Nat.log_le_log`, `Nat.le_log_iff`, `Nat.log_one`, `Nat.log_base`.
(The only "log of product" lemma is `Nat.log_mul_base`.)

---

## 3. p-adic valuation / factorization

Imports: `Mathlib.Data.Nat.Factorization.Defs` / `.Basic`,
`Mathlib.NumberTheory.Padics.PadicVal.Basic`,
`Mathlib.Algebra.GCDMonoid.FinsetLemmas` (Finset.factorization_lcm),
`Mathlib.NumberTheory.Chebyshev` (factorization_lcmUpto).

```
Nat.factorization (n : ℕ) : ℕ →₀ ℕ
Nat.factorization_def (n : ℕ) {p : ℕ} (pp : Nat.Prime p) : n.factorization p = padicValNat p n
Nat.factorization_lcm {a b} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).factorization = a.factorization ⊔ b.factorization
Nat.factorization_gcd {a b} (ha_pos : a ≠ 0) (hb_pos : b ≠ 0) :
    (a.gcd b).factorization = a.factorization ⊓ b.factorization
Nat.factorization_mul {a b} (ha : a ≠ 0) (hb : b ≠ 0) : (a * b).factorization = a.factorization + b.factorization
Nat.factorization_pow (n k) : (n ^ k).factorization = k • n.factorization
Nat.factorization_prod {S g} (hS : ∀ x ∈ S, g x ≠ 0) : (S.prod g).factorization = ∑ x ∈ S, (g x).factorization

Finset.factorization_lcm {f : ι → ℕ} {s : Finset ι} (hf : ∀ k ∈ s, f k ≠ 0) (p : ℕ) :
    (s.lcm f).factorization p = s.sup fun a => (f a).factorization p

Nat.Prime.pow_dvd_iff_le_factorization {p k n} (pp : Nat.Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p
Nat.Prime.dvd_iff_one_le_factorization {p n} (pp : Nat.Prime p) (hn : n ≠ 0) :
    p ∣ n ↔ 1 ≤ n.factorization p
Nat.factorization_le_iff_dvd {d n} (hd : d ≠ 0) (hn : n ≠ 0) : d.factorization ≤ n.factorization ↔ d ∣ n
Nat.factorization_eq_zero_of_not_dvd {n p} (h : ¬p ∣ n) : n.factorization p = 0
Nat.factorization_eq_zero_iff (n p) : n.factorization p = 0 ↔ ¬Nat.Prime p ∨ ¬p ∣ n ∨ n = 0

padicValNat (p n : ℕ) : ℕ
padicValNat_def [Fact p.Prime] {n} (hn : n ≠ 0) : padicValNat p n = multiplicity p n
padicValNat_dvd_iff_le {p} [Fact p.Prime] {a n} (ha : a ≠ 0) : p ^ n ∣ a ↔ n ≤ padicValNat p a
padicValNat_dvd_iff (n : ℕ) [Fact p.Prime] (a : ℕ) : p ^ n ∣ a ↔ a = 0 ∨ n ≤ padicValNat p a
padicValNat_le_nat_log {p} (n) : padicValNat p n ≤ log p n
padicValNat.mul {p a b} [Fact p.Prime] : a ≠ 0 → b ≠ 0 → padicValNat p (a * b) = padicValNat p a + padicValNat p b
padicValNat.pow {p} [Fact p.Prime] (a n) : padicValNat p (a ^ n) = n * padicValNat p a
padicValNat.self {p} (hp : 1 < p) : padicValNat p p = 1
padicValNat.prime_pow {p} [Fact p.Prime] (n) : padicValNat p (p ^ n) = n
padicValNat.eq_zero_of_not_dvd {p n} (h : ¬p ∣ n) : padicValNat p n = 0
```

### KEY LEMMA: `v_p (lcm 1..n) = Nat.log p n`  — **already in mathlib**

```
Nat.factorization_lcmUpto (n : ℕ) {p : ℕ} (hp : Nat.Prime p) : n.lcmUpto.factorization p = log p n
```

Convert to `padicValNat` with one rewrite:
```lean
have h : (Nat.lcmUpto n).factorization p = Nat.log p n := Nat.factorization_lcmUpto n hp
rw [Nat.factorization_def (Nat.lcmUpto n) hp] at h   -- h : padicValNat p (Nat.lcmUpto n) = Nat.log p n
```
So this key lemma does NOT need to be proved from scratch.

---

## 4. ZMod p

Imports: `Mathlib.Data.ZMod.Basic` (type), `Mathlib.Algebra.Field.ZMod` (Field instance).

```
ZMod : ℕ → Type
instance : Field (ZMod p)     -- with variable (p : ℕ) [hp : Fact p.Prime]  (ANONYMOUS instance)
-- verified: inferInstance : Field (ZMod 3)  and  inferInstance : Fact (Nat.Prime 3)
ZMod.natCast_eq_zero_iff (a b : ℕ) : ↑a = 0 ↔ b ∣ a        -- (a : ZMod p) = 0 ↔ p ∣ a
CharP.cast_eq_zero_iff (ZMod p) p a : ↑a = 0 ↔ p ∣ a
ZMod.intCast_zmod_eq_zero_iff_dvd (a : ℤ) (b : ℕ) : (a : ZMod b) = 0 ↔ (b : ℤ) ∣ a
ZMod.val {n} : ZMod n → ℕ
ZMod.val_natCast (n a) : (↑a).val = a % n
ZMod.natCast_zmod_val {n} [NeZero n] (a : ZMod n) : ↑a.val = a
ZMod.natCast_self (n) : ↑n = 0
ZMod.mul_inv_eq_gcd {n} (a : ZMod n) : a * a⁻¹ = ↑(a.val.gcd n)
ZMod.mul_inv_of_unit {n} (a : ZMod n) (h : IsUnit a) : a * a⁻¹ = 1
ZMod.inv_eq_of_mul_eq_one (n) (a b : ZMod n) (h : a * b = 1) : a⁻¹ = b
ZMod.unitOfCoprime {n} (x : ℕ) (h : x.Coprime n) : (ZMod n)ˣ
ZMod.inv_zero (n) : (0 : ZMod n)⁻¹ = 0
```

- Inverse notation `(x : ZMod p)⁻¹` works (Field gives `Inv`); `((2 : ZMod 3)⁻¹ = 2)`
  is provable by `native_decide`.
- `Finset.sum` over `ZMod p` works generically (any `AddCommMonoid`).
- `∑ j ∈ Finset.Icc 1 r, (j : ZMod p)⁻¹` typechecks.
- ✗ DOES NOT EXIST: `ZMod.field`, `ZMod.instField`, `ZMod.natCast_zmod_eq_zero_iff_dvd`,
  `ZMod.val_inv`, `ZMod.inv_val` (use the anonymous instance and the names above).

Important side fact (from `Nat.lt_pow_succ_log_self`): `r = n / p^e < p`, so every
`j ∈ Icc 1 r` is a unit in `ZMod p`.

---

## 5. Prime / gcd / coprime / divisibility

Imports: `Mathlib.Data.Nat.Prime.Defs` / `.Basic`, `Mathlib.Data.Nat.GCD.Basic`.

```
Nat.Prime (p : ℕ) : Prop
Nat.Prime.dvd_of_dvd_pow {p m n} (pp : Nat.Prime p) (h : p ∣ m ^ n) : p ∣ m
Nat.Prime.not_dvd_one {p} (pp : Nat.Prime p) : ¬p ∣ 1
Nat.Prime.one_lt : Nat.Prime p → 1 < p
Nat.Prime.pos (pp) : 0 < p
Nat.Prime.dvd_mul {p m n} (pp) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n
Nat.Prime.dvd_or_dvd {p m n} (pp) : p ∣ m * n → p ∣ m ∨ p ∣ n
Nat.Prime.dvd_iff_one_le_factorization {p n} (pp) (hn : n ≠ 0) : p ∣ n ↔ 1 ≤ n.factorization p

Nat.Coprime (m n : ℕ) : Prop
Nat.Coprime.symm {n m} : n.Coprime m → m.Coprime n
Nat.coprime_iff_gcd_eq_one {m n} : m.Coprime n ↔ m.gcd n = 1
Nat.Coprime.dvd_mul_right {m n k} (H : k.Coprime n) : k ∣ m * n ↔ k ∣ m
Nat.Coprime.dvd_mul_left  {m n k} (H : k.Coprime m) : k ∣ m * n ↔ k ∣ n
Nat.Prime.coprime_iff_not_dvd {p n} (pp : Nat.Prime p) : p.Coprime n ↔ ¬p ∣ n

Nat.dvd_gcd_iff {k m n} : k ∣ m.gcd n ↔ k ∣ m ∧ k ∣ n
Nat.gcd_dvd_left (m n) : m.gcd n ∣ m
Nat.gcd_dvd_right (m n) : m.gcd n ∣ n
Nat.dvd_gcd {k m n} : k ∣ m → k ∣ n → k ∣ m.gcd n
Nat.dvd_mul_right (a b) : a ∣ a * b
Nat.dvd_mul_left (a b) : a ∣ b * a
```

✗ DOES NOT EXIST: `Nat.coprime` (lowercase def), `Nat.Prime.not_dvd_iff`,
`Nat.Coprime.coprime_iff_not_dvd`, `Nat.gcd_eq_one_iff_coprime`.
Replacements: `Nat.Coprime`, `Nat.Prime.coprime_iff_not_dvd`, `Nat.coprime_iff_gcd_eq_one`.

---

## 6. Rat numerator / denominator

Imports: `Mathlib.Data.Rat.Defs` / `.Lemmas`, `Mathlib.Algebra.GCDMonoid.FinsetLemmas`.

```
Rat.num (self : ℚ) : ℤ
Rat.den (self : ℚ) : ℕ
Rat.num_div_den (r : ℚ) : ↑r.num / ↑r.den = r
Rat.normalize (num : ℤ) (den : ℕ := 1) (den_nz : den ≠ 0 := by decide) : ℚ
mkRat (num : ℤ) (den : ℕ) : ℚ                       -- root-level, NOT Rat.mkRat
Rat.normalize_eq {num : ℤ} {den : ℕ} (den_nz) :
    Rat.normalize num den den_nz =
      { num := num / ↑(num.natAbs.gcd den), den := den / num.natAbs.gcd den, den_nz := ⋯, reduced := ⋯ }
Rat.den_ne_zero (q) : q.den ≠ 0
Rat.num_zero : Rat.num 0 = 0
Rat.den_zero : Rat.den 0 = 1
Rat.den_one : Rat.den 1 = 1
Rat.num_one : Rat.num 1 = 1
Rat.num_natCast (n : ℕ) : (↑n).num = ↑n
Rat.num_intCast (a : ℤ) : (↑a).num = a
Rat.den_natCast (n : ℕ) : (↑n).den = 1
Rat.add_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den
Rat.mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den
Rat.isInt (a : ℚ) : Bool

Finset.Rat.den_sum_dvd_lcm_den {ι} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ s.lcm fun i => (f i).den
Finset.Rat.den_sum_dvd_prod_den {ι} (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ ∏ i ∈ s, (f i).den
```

`Mathlib/NumberTheory/Harmonic/Int.lean` proves only:
`harmonic_not_int {n} (h : 2 ≤ n) : ¬(harmonic n).isInt = true` and
`padicValRat_two_harmonic (n) : padicValRat 2 (harmonic n) = -↑(Nat.log 2 n)`.
It does **not** state anything about the numerator structure `a_n/L_n`;
that bridge (below) is new.

Bridging `a_n` to the numerator (padic route, all lemmas verified):
```
padicValRat (p : ℕ) (q : ℚ) : ℤ
padicValRat_def (p : ℕ) (q : ℚ) : padicValRat p q = ↑(padicValInt p q.num) - ↑(padicValNat p q.den)
padicValInt (p : ℕ) (z : ℤ) : ℕ
padicValInt.of_nat {p n} : padicValInt p ↑n = padicValNat p n
padicValRat.of_nat {p n} : padicValRat p ↑n = ↑(padicValNat p n)
padicValRat.inv {p} [Fact p.Prime] (q) : padicValRat p q⁻¹ = -padicValRat p q
padicValRat.add_eq_min {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hval : padicValRat p q ≠ padicValRat p r) : padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r)
```

---

## 7. Bernoulli & Wolstenholme

Imports: `Mathlib.NumberTheory.Bernoulli`, `Mathlib.NumberTheory.BernoulliPolynomials`.

```
bernoulli (n : ℕ) : ℚ
bernoulli' (n : ℕ) : ℚ
bernoulli_zero : bernoulli 0 = 1
bernoulli_one  : bernoulli 1 = -1 / 2
bernoulli_two  : bernoulli 2 = 6⁻¹
bernoulli_eq_zero_of_odd {n} (h_odd : Odd n) (hlt : 1 < n) : bernoulli n = 0
bernoulli'_eq_bernoulli (n) : bernoulli' n = (-1) ^ n * bernoulli n
Polynomial.bernoulli (n : ℕ) : Polynomial ℚ
bernoulliPowerSeries (A) [CommRing A] [Algebra ℚ A] : PowerSeries A
```

- `Bernoulli` (bare) ✗ DOES NOT EXIST; the def is lowercase `bernoulli`.
- **Wolstenholme's theorem is NOT in mathlib**: `grep -ri wolstenholme Mathlib/` returns nothing.
  (An external Lean 4 proof exists: A. Linhares, "Deep Vision: A Formal Proof of
  Wolstenholme's Theorem in Lean 4", arXiv:2604.16507.)

---

## 8. Existing formalizations (search results)

- `Mathlib.NumberTheory.Harmonic.Defs` — harmonic numbers `harmonic : ℕ → ℚ`.
- `Mathlib.NumberTheory.Harmonic.Int` — H_n not an integer (Kürschák); `padicValRat_two_harmonic`.
- `Mathlib.NumberTheory.Harmonic.Bounds` — log bounds.
- `Mathlib.NumberTheory.Chebyshev` — **`Nat.lcmUpto` and `Nat.factorization_lcmUpto`**
  i.e. lcm(1..n) and its p-adic valuation are already formalized in mathlib.
- Wolstenholme: not in mathlib; external arXiv:2604.16507 (Lean 4 + Mathlib).
- Erdős #291: not formalized (erdosproblems.com lists "Formalised statement? No").
  Related OEIS sequence A110566 (n with gcd(a_n, L_n) = 1).

---

## What must be proved from scratch

1. **Definition of `a n`** and the identity `harmonic n = (a n : ℚ) / (n.lcmUpto : ℚ)`.
   (Small: unfold, use `Finset.sum` over `Icc 1 n` and `Nat.lcmUpto_dvd` / `Finset.dvd_lcm`.)
2. **The bridge** `p ∣ a n ↔ ...` in terms of `harmonic n`: from
   `padicValRat_def` + `padicValRat p (harmonic n)` and `v_p(L n) = e`
   (via `Nat.factorization_lcmUpto` + `Nat.factorization_def`, one rewrite).
3. **The main characterization** `p ∣ a n ↔ ∑_{j=1}^r j⁻¹ ≡ 0 (mod p)`
   (group `H_n = ∑_{k=1}^n 1/k` by `v_p(k)`; uses `padicValRat.add_eq_min`,
   `padicValRat.inv`, `padicValRat.of_nat`, and the ZMod lemmas above).
4. **The corollary** `3 ∣ Nat.gcd (a (2*3^e)) ((2*3^e).lcmUpto)` (n = 2·3^e ⇒ r = 2).
5. Any missing `Nat.log` product lemmas (`Nat.log_mul` etc.) if needed — avoid by
   working with `Nat.log_pow`, `Nat.log_mul_base`, and `Nat.log_eq_iff` instead.
