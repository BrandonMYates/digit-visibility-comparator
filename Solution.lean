/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DigitVis

/-!
# Solution

The proof development lives in the `DigitVis` library, pinned by commit in
`lakefile.toml`. This file restates the Challenge's one definition and five statements
verbatim and discharges each by direct application of the library's theorem.

The `example` below is the bridge: `CyclotomicRepunit.jacobiSumK` is *definitionally*
`DigitVisibility.jacobiSumK` (the same term), so every library theorem about the latter
is a proof of the corresponding statement about the former with no translation step.
-/

namespace CyclotomicRepunit

open Finset

def jacobiSumK {F R : Type*} [CommRing F] [Fintype F] [DecidableEq F] [CommRing R] {k : ℕ}
    (χ : Fin k → MulChar F R) : R :=
  ∑ x ∈ univ.filter fun x : Fin k → F => ∑ i, x i = 1, ∏ i, χ i (x i)

example : @CyclotomicRepunit.jacobiSumK = @DigitVisibility.jacobiSumK := rfl

theorem jacobiSumK_two {F R : Type*} [CommRing F] [Fintype F] [DecidableEq F] [CommRing R]
    (χ ψ : MulChar F R) : jacobiSumK ![χ, ψ] = jacobiSum χ ψ :=
  DigitVisibility.jacobiSumK_two χ ψ

theorem orderOf_eval_cyclotomic {q d : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d)
    (hexc : ¬(q = 2 ∧ d = 6)) :
    orderOf (q : ZMod ((Polynomial.cyclotomic d ℤ).eval (q : ℤ)).natAbs) = d :=
  DigitVisibility.orderOf_eval_cyclotomic hq hd hexc

theorem dvd_repunit_iff {q d : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d) (hexc : ¬(q = 2 ∧ d = 6))
    (k : ℕ) :
    (Polynomial.cyclotomic d ℤ).eval (q : ℤ) ∣ ∑ i ∈ range k, (q : ℤ) ^ i ↔ d ∣ k :=
  DigitVisibility.dvd_repunit_iff hq hd hexc k

theorem jacobiSumK_norm_dichotomy {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q d k j : ℕ} (hq : 2 ≤ q) (hd : 2 ≤ d) (hk : 2 ≤ k) (hexc : ¬(q = 2 ∧ d = 6))
    (hcard : Fintype.card K = q ^ d) (θ : MulChar K ℂ)
    (hθ : orderOf θ = ((Polynomial.cyclotomic d ℤ).eval (q : ℤ)).natAbs)
    (hj : Nat.Coprime j (orderOf θ)) :
    ‖jacobiSumK fun i : Fin k => θ ^ (j * q ^ (i : ℕ))‖ ^ 2
      = (q : ℝ) ^ (d * (if d ∣ k then k - 2 else k - 1)) :=
  DigitVisibility.jacobiSumK_norm_dichotomy hq hd hk hexc hcard θ hθ hj

theorem jacobiSumK_even_level_eval {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {p d k j : ℕ} (hp : p.Prime) (hd : 2 ≤ d) (hd2 : Even d) (hk : 2 ≤ k)
    (hexc : ¬(p = 2 ∧ d = 6)) (hcard : Fintype.card K = p ^ d) (θ : MulChar K ℂ)
    (hθ : orderOf θ = ((Polynomial.cyclotomic d ℤ).eval (p : ℤ)).natAbs)
    (hj : Nat.Coprime j (orderOf θ)) :
    (jacobiSumK fun i : Fin k => θ ^ (j * p ^ (i : ℕ)))
      = if d ∣ k then -(p : ℂ) ^ (d / 2 * (k - 2)) else (p : ℂ) ^ (d / 2 * (k - 1)) :=
  DigitVisibility.jacobiSumK_even_level_eval hp hd hd2 hk hexc hcard θ hθ hj

end CyclotomicRepunit
