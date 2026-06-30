/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.ElementaryFactor

/-!
# Affine coefficient control

Formalizes Lemma `lem:affine` (Affine coefficient control) and the
triangular-affine structure of Remark `rem:triangular`.

We model "a power series convergent near `0` with `h_0 = 1`" as a function
`h : ℂ → ℂ` that is analytic at `0` with `h 0 = 1`; by definition of
analyticity this is exactly a function locally given by a convergent power
series.
-/

namespace Weierstrass

open Complex

/-- **Lemma `lem:affine` (i).** Introducing the factor `E_n(z/a;c)` leaves
all Taylor coefficients of degree `≤ n` of `F = h · E_n(·/a;c)` unchanged,
independently of `c`. -/
theorem taylorCoeff_mul_E_eq_of_le {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1)
    {a c : ℂ} (ha : a ≠ 0) {n m : ℕ} (hmn : m ≤ n) :
    taylorCoeff (fun z => h z * E n c (z / a)) m = taylorCoeff h m := by
  sorry

/-- **Lemma `lem:affine` (ii).** The Taylor coefficient of degree `n+1` of
`F = h · E_n(·/a;c)` is affine in `c` with nonzero slope
`1/((n+1)·a^{n+1})`. -/
theorem taylorCoeff_mul_E_succ {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1)
    {a c : ℂ} (ha : a ≠ 0) (n : ℕ) :
    taylorCoeff (fun z => h z * E n c (z / a)) (n + 1)
      = taylorCoeff h (n + 1) + (c - 1) / ((n + 1) * a ^ (n + 1)) := by
  sorry

/-- **Remark `rem:triangular`.** For fixed `h, a, n`, the coefficient map
`c ↦ [z^{n+1}] (h · E_n(·/a;c))` is a surjective affine map `ℂ → ℂ`; in
particular every target value is attained by some `c`. -/
theorem exists_c_taylorCoeff_mul_E_succ_eq {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1)
    {a : ℂ} (ha : a ≠ 0) (n : ℕ) (target : ℂ) :
    ∃ c : ℂ, taylorCoeff (fun z => h z * E n c (z / a)) (n + 1) = target := by
  sorry

end Weierstrass
