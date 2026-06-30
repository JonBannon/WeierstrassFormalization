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
theorem taylorCoeff_mul_E_eq_of_le {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    {a c : ℂ} {n m : ℕ} (hmn : m ≤ n) :
    taylorCoeff (fun z => h z * E n c (z / a)) m = taylorCoeff h m := by
  -- Rewrite `z / a` as `a⁻¹ * z` to use the constant-multiple composition rule.
  have hEq : (fun z : ℂ => E n c (z / a)) = fun z : ℂ => E n c (a⁻¹ * z) := by
    funext z; rw [div_eq_inv_mul]
  have hEbare : ∀ j : ℕ, ContDiff ℂ j (E n c) := fun j => by unfold E; fun_prop
  have hEcomp : ∀ j : ℕ, ContDiff ℂ j (fun z : ℂ => E n c (a⁻¹ * z)) := fun j => by
    unfold E; fun_prop
  have hfactorial_ne_zero : ∀ j : ℕ, (Nat.factorial j : ℂ) ≠ 0 := fun j => by
    exact_mod_cast Nat.factorial_ne_zero j
  -- All derivatives of `E_n(·;c)` of order `1, …, n` vanish at `0` (Lemma `lem:structure` (ii)).
  have hderiv_E_zero : ∀ j : ℕ, 1 ≤ j → j ≤ n → iteratedDeriv j (E n c) 0 = 0 := by
    intro j hj1 hjn
    have hT := taylorCoeff_E_eq_zero (n := n) (c := c) (m := j) hj1 hjn
    unfold taylorCoeff at hT
    rw [div_eq_zero_iff] at hT
    rcases hT with hT | hT
    · exact hT
    · exact absurd hT (hfactorial_ne_zero j)
  have hf : ContDiffAt ℂ (m : ℕ) h 0 := hh.contDiffAt.of_le le_top
  have hg : ContDiffAt ℂ (m : ℕ) (fun z : ℂ => E n c (z / a)) 0 := by
    rw [hEq]; exact (hEcomp m).contDiffAt
  -- Leibniz rule for the `m`-th derivative of the product.
  have hsum := iteratedDeriv_fun_mul hf hg
  rw [Finset.sum_range_succ] at hsum
  -- Every term with index `i < m` involves a derivative of `E_n(·/a;c)` of
  -- order `m - i ∈ [1, n]`, which vanishes.
  have hterms : ∀ i ∈ Finset.range m,
      (m.choose i : ℂ) * iteratedDeriv i h 0
        * iteratedDeriv (m - i) (fun z => E n c (z / a)) 0 = 0 := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have h1 : 1 ≤ m - i := by omega
    have h2 : m - i ≤ n := by omega
    have hvanish : iteratedDeriv (m - i) (fun z : ℂ => E n c (z / a)) 0 = 0 := by
      rw [hEq, iteratedDeriv_comp_const_mul (hEbare (m - i)) a⁻¹]
      simp [hderiv_E_zero (m - i) h1 h2]
    rw [hvanish]; ring
  rw [Finset.sum_eq_zero hterms, zero_add, Nat.sub_self, Nat.choose_self, Nat.cast_one,
    one_mul] at hsum
  -- Only the `i = m` term survives, contributing `E_n(0/a;c) = 1`.
  have hlast : iteratedDeriv 0 (fun z : ℂ => E n c (z / a)) 0 = 1 := by
    simp [E_zero]
  rw [hlast, mul_one] at hsum
  unfold taylorCoeff
  rw [hsum]

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
