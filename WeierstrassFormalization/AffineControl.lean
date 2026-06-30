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
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfact : (Nat.factorial (n + 1) : ℂ) = ((n : ℂ) + 1) * (Nat.factorial n : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have to_iteratedDeriv : ∀ (f : ℂ → ℂ) (j : ℕ),
      taylorCoeff f j * (Nat.factorial j : ℂ) = iteratedDeriv j f 0 := by
    intro f j
    unfold taylorCoeff
    rw [div_mul_cancel₀ _ (hfactorial_ne_zero j)]
  -- Translate `taylorCoeff_E_succ` (Lemma `lem:structure` (iii)) into a statement
  -- about the bare `(n+1)`-st derivative of `E_n(·;c)`.
  have hEsucc : iteratedDeriv (n + 1) (E n c) 0 = (c - 1) * (Nat.factorial n : ℂ) := by
    rw [← to_iteratedDeriv (E n c) (n + 1), taylorCoeff_E_succ, hfact, ← mul_assoc,
      div_mul_cancel₀ _ hn1]
  have hf : ContDiffAt ℂ (n + 1 : ℕ) h 0 := hh.contDiffAt.of_le le_top
  have hg : ContDiffAt ℂ (n + 1 : ℕ) (fun z : ℂ => E n c (z / a)) 0 := by
    rw [hEq]; exact (hEcomp (n + 1)).contDiffAt
  -- Leibniz rule for the `(n+1)`-st derivative of the product.
  have hsum := iteratedDeriv_fun_mul hf hg
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hsum
  -- Every term with index `i + 1`, `0 ≤ i < n`, involves a derivative of
  -- `E_n(·/a;c)` of order `n + 1 - (i+1) ∈ [1, n]`, which vanishes.
  have hmid : ∀ i ∈ Finset.range n,
      ((n + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) h 0
        * iteratedDeriv (n + 1 - (i + 1)) (fun z => E n c (z / a)) 0 = 0 := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have h1 : 1 ≤ n + 1 - (i + 1) := by omega
    have h2 : n + 1 - (i + 1) ≤ n := by omega
    have hvanish : iteratedDeriv (n + 1 - (i + 1)) (fun z : ℂ => E n c (z / a)) 0 = 0 := by
      rw [hEq, iteratedDeriv_comp_const_mul (hEbare (n + 1 - (i + 1))) a⁻¹]
      change a⁻¹ ^ (n + 1 - (i + 1)) * iteratedDeriv (n + 1 - (i + 1)) (E n c) (a⁻¹ * 0) = 0
      rw [mul_zero, hderiv_E_zero (n + 1 - (i + 1)) h1 h2, mul_zero]
    rw [hvanish]; ring
  rw [Finset.sum_eq_zero hmid] at hsum
  -- Only the `i = 0` and `i = n+1` terms survive.
  simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, Nat.sub_self, Nat.cast_one,
    one_mul, iteratedDeriv_zero, zero_div, E_zero, mul_one, zero_add] at hsum
  rw [hh0, one_mul] at hsum
  have hfirst : iteratedDeriv (n + 1) (fun z : ℂ => E n c (z / a)) 0
      = a⁻¹ ^ (n + 1) * ((c - 1) * (Nat.factorial n : ℂ)) := by
    rw [hEq, iteratedDeriv_comp_const_mul (hEbare (n + 1)) a⁻¹]
    change a⁻¹ ^ (n + 1) * iteratedDeriv (n + 1) (E n c) (a⁻¹ * 0)
        = a⁻¹ ^ (n + 1) * ((c - 1) * (Nat.factorial n : ℂ))
    rw [mul_zero, hEsucc]
  rw [hfirst] at hsum
  unfold taylorCoeff
  rw [hsum, hfact, inv_pow]
  field_simp [hfactorial_ne_zero n]
  ring

/-- **Remark `rem:triangular`.** For fixed `h, a, n`, the coefficient map
`c ↦ [z^{n+1}] (h · E_n(·/a;c))` is a surjective affine map `ℂ → ℂ`; in
particular every target value is attained by some `c`. -/
theorem exists_c_taylorCoeff_mul_E_succ_eq {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1)
    {a : ℂ} (ha : a ≠ 0) (n : ℕ) (target : ℂ) :
    ∃ c : ℂ, taylorCoeff (fun z => h z * E n c (z / a)) (n + 1) = target := by
  sorry

end Weierstrass
