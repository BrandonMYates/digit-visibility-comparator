/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Challenge: cyclotomic divisors of repunits, and the degeneration of a Jacobi sum

This file is the human-auditable statement. It imports only Mathlib.

## The arithmetic set-up

Fix an integer base `q ≥ 2` and a block length `k`. The base-`q` repunit of length `k` is
`R_k(q) = 1 + q + ⋯ + q^{k-1}`, and `q^k - 1 = ∏_{d ∣ k} Φ_d(q)`, where `Φ_d` is the `d`-th
cyclotomic polynomial and `Φ_d(q)` denotes its value at the integer `q` (a *specialized
cyclotomic integer*, not a field). Everything below is a statement about that integer and about
character sums over a finite field; no cyclotomic field extension and no Kummer field extension
appears anywhere.

Five statements are compared. The four that carry the mathematics are listed first, in
the order in which they build on one another.

1. `orderOf_eval_cyclotomic`: the multiplicative order of `q` modulo `Φ_d(q)` is exactly `d`,
   for all `q ≥ 2` and `d ≥ 2`, with the single exception `(q, d) = (2, 6)`, where
   `Φ₆(2) = 3 = Φ₂(2)` and the order is `2`. This is a restatement, in specialized-cyclotomic
   form, of the primitive-divisor theorem of Bang and Zsigmondy (Birkhoff and Vandiver,
   *On the integral divisors of `a^n - b^n`*, Ann. of Math. (2) **5** (1904), 173-180).

2. `dvd_repunit_iff`: consequently `Φ_d(q) ∣ R_k(q) ↔ d ∣ k`, away from `(q, d) = (2, 6)`.
   In the source manuscript the left-hand side is named "level `d` is visible at block
   length `k`"; that name is not used in any statement here, and nothing below depends on it.

3. `jacobiSumK_norm_dichotomy`: let `K` be a finite field with `#K = q ^ d` and let `θ` be a
   multiplicative character of `K` of order exactly `Φ_d(q)`. For `j` coprime to that order,
   the `k`-fold Jacobi sum of the Frobenius-twisted tuple
   `(θ^j, θ^{jq}, …, θ^{jq^{k-1}})` has squared absolute value `(#K)^{k-1}` when `d ∤ k`, and
   `(#K)^{k-2}` when `d ∣ k`. So the divisibility criterion of (2) is exactly the locus on
   which this Jacobi sum degenerates by one power of `#K`.

   The exponent tuple `(1, q, …, q^{k-1})` is not chosen: it is the vector of place values of
   a length-`k` block of base-`q` digits, and the modulus `Φ_d(q)` is the level-`d` factor of
   `q^k - 1` in the same base. The two classical inputs -- the order of `q` modulo `Φ_d(q)`,
   and the Gauss-Jacobi product formula -- collide precisely because the product character of
   that tuple is `θ^{j R_k(q)}`.

4. `jacobiSumK_even_level_eval`: for even `d` and prime `p`, that Jacobi sum has an exact
   closed value, uniform in the block length `k` and independent of which primitive character
   of order `Φ_d(p)` is chosen: `p^{(d/2)(k-1)}` when `d ∤ k`, and `-p^{(d/2)(k-2)}` when
   `d ∣ k`. Here `d/2` is exact because `d` is even. The hypothesis driving this is the
   semiprimitive (uniform-cyclotomy) condition `p^{d/2} ≡ -1 (mod Φ_d(p))`, which is a
   consequence of statement (1).

The fifth compared statement, `jacobiSumK_two`, records that the one new definition in this
file agrees with Mathlib's `jacobiSum` at `k = 2`. It is included as auditable evidence that
the definition is the classical object rather than a convenient surrogate, and it is not a
theorem of the source manuscript.

## Scope, stated plainly

The source manuscript states (3) and (4) as facts about the compactly supported etale
cohomology of a cyclic cover of the open simplex `{x ∈ 𝔾_m^k : ∑ xᵢ = 1}`, where the Jacobi
sums are Frobenius eigenvalues and the dichotomy is a drop of one in cohomological weight.
**None of that geometry is asserted anywhere in this file**, and no statement below depends on
it: the compared theorems are the underlying statements about the specialized cyclotomic
integer `Φ_d(q)`, about divisibility of repunits, and about character sums over a finite
field. The cohomological reading is recorded here only to identify the source.

**This file makes no claim concerning the Riemann hypothesis, in either direction, and no
statement below mentions the Riemann zeta function or any `L`-function.**
-/

namespace CyclotomicRepunit

open Finset

/-- The **`k`-fold Jacobi sum** of multiplicative characters `χ 0, …, χ (k-1)` on a finite
commutative ring `F`:
`J(χ₀, …, χ_{k-1}) = ∑_{x₀ + ⋯ + x_{k-1} = 1} χ₀(x₀) ⋯ χ_{k-1}(x_{k-1})`,
the sum running over all `k`-tuples of elements of `F` summing to `1`, with each
multiplicative character extended by `0` at `0` (Mathlib's `MulChar` convention).

This is the classical Jacobi sum of A. Weil, *Numbers of solutions of equations in finite
fields*, Bull. Amer. Math. Soc. **55** (1949), 497-508. For `k = 2` it is Mathlib's
`jacobiSum`, since `x₀ + x₁ = 1` reparametrizes as `x₁ = 1 - x₀`; that identification is
recorded below as `jacobiSumK_two`. In the degenerate low cases: at `k = 0` the defining
equation reads `0 = 1`, which has no solution in a nontrivial `F`, so the sum is empty; at
`k = 1` the only admissible tuple is `x₀ = 1`, so the sum is `χ₀ 1 = 1`. -/
def jacobiSumK {F R : Type*} [CommRing F] [Fintype F] [DecidableEq F] [CommRing R] {k : ℕ}
    (χ : Fin k → MulChar F R) : R :=
  ∑ x ∈ univ.filter fun x : Fin k → F => ∑ i, x i = 1, ∏ i, χ i (x i)

/-- The `k`-fold Jacobi sum reduces to Mathlib's two-variable `jacobiSum` at `k = 2`.

This is the fidelity check on the definition above: `jacobiSumK` is not a new notion, it is
the standard extension of `jacobiSum` from two characters to `k` of them. -/
theorem jacobiSumK_two {F R : Type*} [CommRing F] [Fintype F] [DecidableEq F] [CommRing R]
    (χ ψ : MulChar F R) : jacobiSumK ![χ, ψ] = jacobiSum χ ψ := by
  sorry

/-- **The exact order of `q` modulo the specialized cyclotomic integer `Φ_d(q)`.**

For every integer base `q ≥ 2` and every level `d ≥ 2`, the multiplicative order of `q` in
`ZMod |Φ_d(q)|` is exactly `d`, with the single exception `(q, d) = (2, 6)`. At that
exception `Φ₆(2) = 3 = Φ₂(2)` and the order is `2`, so level six is a duplicate of the
period-two level rather than an unexplained failure.

The inequality `orderOf q ∣ d` is immediate from `Φ_d(q) ∣ q^d - 1`. The content is the
reverse divisibility, which is the primitive-divisor theorem of Bang and Zsigmondy in the
form given by Birkhoff and Vandiver (1904): outside the classical exceptions `q^d - 1` has a
prime factor dividing no `q^e - 1` with `e < d`, and such a prime divides `Φ_d(q)`. -/
theorem orderOf_eval_cyclotomic {q d : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d)
    (hexc : ¬(q = 2 ∧ d = 6)) :
    orderOf (q : ZMod ((Polynomial.cyclotomic d ℤ).eval (q : ℤ)).natAbs) = d := by
  sorry

/-- **The divisibility criterion.**

For an integer base `q ≥ 2` and a level `d ≥ 2` other than `(q, d) = (2, 6)`, the specialized
cyclotomic integer `Φ_d(q)` divides the base-`q` repunit `R_k(q) = 1 + q + ⋯ + q^{k-1}` if and
only if `d` divides the block length `k`.

The repunit is written here as `∑_{i < k} q^i` in `ℤ`, and `Φ_d(q)` as the evaluation of the
`d`-th cyclotomic polynomial at `q` in `ℤ`. No hypothesis on `k` is needed: at `k = 0` both
sides hold, and at `k = 1` both fail.

In the source manuscript the left-hand side is the definition of "level `d` is visible at
block length `k`". The statement here is the divisibility itself. -/
theorem dvd_repunit_iff {q d : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d) (hexc : ¬(q = 2 ∧ d = 6))
    (k : ℕ) :
    (Polynomial.cyclotomic d ℤ).eval (q : ℤ) ∣ ∑ i ∈ range k, (q : ℤ) ^ i ↔ d ∣ k := by
  sorry

/-- **Divisibility is Jacobi-sum degeneration.**

Let `q ≥ 2`, `d ≥ 2`, `k ≥ 2`, with `(q, d) ≠ (2, 6)`. Let `K` be a finite field with
`#K = q ^ d` (this forces `q` to be a prime power), and let `θ` be a multiplicative character
of `K` with values in `ℂ` whose order is exactly the specialized cyclotomic integer
`|Φ_d(q)|`. Let `j` be coprime to that order, so that `θ ^ j` is again of exact order
`|Φ_d(q)|`.

Then the `k`-fold Jacobi sum of the Frobenius-twisted tuple
`(θ^j, θ^{jq}, θ^{jq²}, …, θ^{jq^{k-1}})` satisfies
`‖J‖² = (#K)^{k-1} = q^{d(k-1)}` when `d ∤ k`, and `‖J‖² = (#K)^{k-2} = q^{d(k-2)}` when
`d ∣ k`.

Combined with `dvd_repunit_iff`, this says exactly: the level-`d` cyclotomic integer divides
the length-`k` base-`q` repunit precisely when this Jacobi sum degenerates by one power of
`#K`. The mechanism is that the product of the tuple is `θ^{j R_k(q)}`, which is trivial
exactly when `|Φ_d(q)| ∣ R_k(q)`; off that locus the Gauss-Jacobi product formula and
`‖g(χ)‖² = #K` give the full weight, and on it the degenerate identity for a product-trivial
Jacobi sum gives one power less.

The hypotheses are satisfiable, so the statement is not vacuous: `Φ_d(q)` divides `q^d - 1`,
which is `#K - 1`, and `ℂ` has primitive roots of unity of every order, so a character `θ` of
the required order exists for every such `K` by `MulChar.exists_mulChar_orderOf`. -/
theorem jacobiSumK_norm_dichotomy {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q d k j : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d) (hk : 2 ≤ k) (hexc : ¬(q = 2 ∧ d = 6))
    (hcard : Fintype.card K = q ^ d) (θ : MulChar K ℂ)
    (hθ : orderOf θ = ((Polynomial.cyclotomic d ℤ).eval (q : ℤ)).natAbs)
    (hj : Nat.Coprime j (orderOf θ)) :
    ‖jacobiSumK fun i : Fin k => θ ^ (j * q ^ (i : ℕ))‖ ^ 2
      = (q : ℝ) ^ (d * (if d ∣ k then k - 2 else k - 1)) := by
  sorry

/-- **Exact evaluation at every even level.**

Let `p` be a prime, let `d ≥ 2` be **even**, let `k ≥ 2`, and assume `(p, d) ≠ (2, 6)`. Let
`K` be a finite field with `#K = p ^ d`, let `θ` be a multiplicative character of `K` with
values in `ℂ` of exact order `|Φ_d(p)|`, and let `j` be coprime to that order.

Then the `k`-fold Jacobi sum of `(θ^j, θ^{jp}, …, θ^{jp^{k-1}})` is not merely of the
absolute value given by `jacobiSumK_norm_dichotomy`: it is the exact value
`p^{(d/2)(k-1)}` when `d ∤ k`, and `-p^{(d/2)(k-2)}` when `d ∣ k`. Since `d` is even, the
halving `d / 2` is exact. The value does not depend on `j`, that is, it is the same for every
primitive character of order `|Φ_d(p)|`.

The input is that `d` even and `orderOf p = d` modulo `Φ_d(p)` force
`p^{d/2} ≡ -1 (mod Φ_d(p))`: this is the *semiprimitive*, or *uniform cyclotomy*, condition,
under which every nontrivial Gauss sum `g(θ^a)` over `K` is `±(#K)^{1/2}` with an explicitly
known sign (Carlitz 1956; Baumert-McEliece 1972; Evans 1981; Baumert-Mills-Ward 1982). The
signs cancel along the tuple, which is what makes the value uniform in `k` and independent
of `j`. -/
theorem jacobiSumK_even_level_eval {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p d k j : ℕ} (hp : p.Prime) (hd : 2 ≤ d) (hd2 : Even d) (hk : 2 ≤ k)
    (hexc : ¬(p = 2 ∧ d = 6)) (hcard : Fintype.card K = p ^ d) (θ : MulChar K ℂ)
    (hθ : orderOf θ = ((Polynomial.cyclotomic d ℤ).eval (p : ℤ)).natAbs)
    (hj : Nat.Coprime j (orderOf θ)) :
    (jacobiSumK fun i : Fin k => θ ^ (j * p ^ (i : ℕ)))
      = if d ∣ k then -(p : ℂ) ^ (d / 2 * (k - 2)) else (p : ℂ) ^ (d / 2 * (k - 1)) := by
  sorry

end CyclotomicRepunit
