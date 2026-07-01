/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Divisor
import WeierstrassFormalization.AffineControl
import WeierstrassFormalization.WeierstrassProduct

/-!
# Gaussian-integer realization

Formalizes Theorem `prop:Zi`: every effective divisor on `𝔻` is the zero
divisor of a holomorphic function on `𝔻` with Taylor coefficients in the
Gaussian integers `ℤ[i]`.
-/

namespace Weierstrass

/-- `f` has Taylor coefficients in the Gaussian integers `ℤ[i]`. -/
def HasGaussianIntCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ z : GaussianInt, taylorCoeff f n = (z : ℂ)

/-- The Taylor coefficients of `z ↦ z ^ d * h z` are those of `h`, shifted by `d`
(and `0` below degree `d`). -/
theorem taylorCoeff_pow_mul {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0) (d m : ℕ) :
    taylorCoeff (fun z => z ^ d * h z) m = if d ≤ m then taylorCoeff h (m - d) else 0 := by
  have hf : ContDiffAt ℂ (m : ℕ) (fun z : ℂ => z ^ d) 0 := by fun_prop
  have hg : ContDiffAt ℂ (m : ℕ) h 0 := hh.contDiffAt.of_le le_top
  have hsum := iteratedDeriv_fun_mul hf hg
  have hpow_eq : ∀ i : ℕ, iteratedDeriv i (fun z : ℂ => z ^ d) 0
      = if i = d then (Nat.factorial d : ℂ) else 0 := by
    intro i; rw [iteratedDeriv_fun_pow_zero]; split_ifs <;> simp
  split_ifs with hdm
  · -- `d ≤ m`: only the `i = d` term of the Leibniz sum survives.
    have hd_mem : d ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single d
      (fun i _ hine => by rw [hpow_eq i, if_neg hine]; ring)
      (fun hnotmem => absurd hd_mem hnotmem)] at hsum
    rw [hpow_eq d, if_pos rfl] at hsum
    have hfact : (m.choose d : ℂ) * (Nat.factorial d : ℂ) * (Nat.factorial (m - d) : ℂ)
        = (Nat.factorial m : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hdm
    have hne_fact_m : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hne_fact_md : (Nat.factorial (m - d) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (m - d)
    unfold taylorCoeff
    rw [hsum, div_eq_div_iff hne_fact_m hne_fact_md, ← hfact]
    ring
  · -- `d > m`: every term of the Leibniz sum vanishes.
    have hall_zero : ∀ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ d) 0 * iteratedDeriv (m - i) h 0
          = 0 := by
      intro i hi
      have hile : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hpow_eq i, if_neg (by omega)]; ring
    rw [Finset.sum_eq_zero hall_zero] at hsum
    unfold taylorCoeff
    rw [hsum]
    simp

/-- **Theorem `prop:Zi` (Gaussian-integer realization).** Every effective
divisor on `𝔻` is the zero divisor of a holomorphic function on `𝔻` with
Taylor coefficients in `ℤ[i]`. -/
theorem exists_holomorphic_gaussianInt_coeffs_of_effectiveDivisor (D : EffectiveDivisor) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧ IsZeroDivisorOf D f ∧ HasGaussianIntCoeffs f := by
  obtain ⟨a, ha0, hamult, hesc, _⟩ := exists_enum_of_effectiveDivisor D
  obtain ⟨c, hcforce, hcbound⟩ := exists_coeffSeq a ha0
  have hM := exists_Mtest_of_coeffSeq a c ha0 hesc hcbound
  set d : ℕ := D.mult 0 with hd_def
  set g : ℂ → ℂ := fun z => ∏' k, E k (c k) (z / a k) with hg_def
  set f : ℂ → ℂ := fun z => z ^ d * g z with hf_def
  have hg_holo : HolomorphicOn g := holomorphicOn_tprod_factors (n := id) hM
  have hmono_holo : HolomorphicOn (fun z : ℂ => z ^ d) := by
    intro z _
    have : Differentiable ℂ (fun z : ℂ => z ^ d) := by fun_prop
    exact this.analyticAt z
  have hg_analytic0 : AnalyticAt ℂ g 0 := hg_holo 0 (by simp [mem_𝔻_iff])
  -- every Taylor coefficient of `g` lies in `ℤ[i]`.
  have hg_int : ∀ p : ℕ, ∃ z : GaussianInt, taylorCoeff g p = z := by
    intro p
    obtain ⟨zp, hzp⟩ := hcforce p
    refine ⟨zp, ?_⟩
    have hstep1 : taylorCoeff g p = taylorCoeff (partialProduct a c (p + 1 + 1)) p :=
      taylorCoeff_tprod_factors_eq_partial (n := id) monotone_id hM p (p + 1)
        (show p < p + 1 by omega)
    have hshrink : ∀ N, p ≤ N →
        taylorCoeff (partialProduct a c (N + 1)) p = taylorCoeff (partialProduct a c N) p := by
      intro N hN
      have hanalytic : AnalyticAt ℂ (partialProduct a c N) 0 := by
        have : Differentiable ℂ (partialProduct a c N) := by unfold partialProduct E; fun_prop
        exact this.analyticAt 0
      rw [partialProduct_succ]
      exact taylorCoeff_mul_E_eq_of_le hanalytic hN
    rw [hstep1, hshrink (p + 1) (by omega), hshrink p le_rfl, hzp]
  refine ⟨f, ?_, ?_, ?_⟩
  · -- `HolomorphicOn f`
    intro z hz
    exact (hmono_holo z hz).mul (hg_holo z hz)
  · -- `IsZeroDivisorOf D f`
    intro z hz
    have hg_analytic : AnalyticAt ℂ g z := hg_holo z hz
    have hmono_analytic : AnalyticAt ℂ (fun w : ℂ => w ^ d) z := hmono_holo z hz
    have hg_order : analyticOrderAt g z = ({k | a k = z}.ncard : ℕ∞) :=
      analyticOrderAt_tprod_factors_eq_ncard (n := id) ha0 hM z hz
    have hg_order_ne_top : analyticOrderAt g z ≠ ⊤ := by rw [hg_order]; exact ENat.coe_ne_top _
    have hf_eq : f = fun w => w ^ d * g w := hf_def
    by_cases hz0 : z = 0
    · subst hz0
      have hmono_order : analyticOrderAt (fun w : ℂ => w ^ d) (0 : ℂ) = (d : ℕ∞) := by
        have hfun_eq : (fun x : ℂ => x - 0) ^ d = fun w : ℂ => w ^ d := by
          funext x; simp [Pi.pow_apply]
        rw [← hfun_eq]
        exact analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (0 : ℂ)) (n := d)
      have hfiber_empty : {k | a k = (0 : ℂ)}.ncard = 0 := by
        have hempty : {k | a k = (0 : ℂ)} = ∅ := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact ha0 k
        rw [hempty, Set.ncard_empty]
      have hmono_order_ne_top : analyticOrderAt (fun w : ℂ => w ^ d) (0 : ℂ) ≠ ⊤ := by
        rw [hmono_order]; exact ENat.coe_ne_top _
      have hmul := analyticOrderNatAt_mul hmono_analytic hg_analytic
        hmono_order_ne_top hg_order_ne_top
      have hf_eq2 : f = (fun w : ℂ => w ^ d) * g := hf_eq
      change D.mult 0 = analyticOrderNatAt f 0
      rw [hf_eq2, hmul]
      unfold analyticOrderNatAt
      rw [hmono_order, hg_order, hfiber_empty]
      simp [hd_def]
    · have hmono_order0 : analyticOrderAt (fun w : ℂ => w ^ d) z = 0 :=
        hmono_analytic.analyticOrderAt_eq_zero.mpr (pow_ne_zero d hz0)
      have hmono_order0_ne_top : analyticOrderAt (fun w : ℂ => w ^ d) z ≠ ⊤ := by
        rw [hmono_order0]; simp
      have hmul := analyticOrderNatAt_mul hmono_analytic hg_analytic
        hmono_order0_ne_top hg_order_ne_top
      have hf_eq2 : f = (fun w : ℂ => w ^ d) * g := hf_eq
      change D.mult z = analyticOrderNatAt f z
      rw [hf_eq2, hmul]
      unfold analyticOrderNatAt
      rw [hmono_order0, hg_order, hamult z hz0]
      simp
  · -- `HasGaussianIntCoeffs f`
    intro m
    have hshift := taylorCoeff_pow_mul hg_analytic0 d m
    by_cases hdm : d ≤ m
    · obtain ⟨zg, hzg⟩ := hg_int (m - d)
      refine ⟨zg, ?_⟩
      rw [hf_def]
      rw [if_pos hdm] at hshift
      rw [hshift, hzg]
    · refine ⟨0, ?_⟩
      rw [hf_def]
      rw [if_neg hdm] at hshift
      rw [hshift]
      simp

end Weierstrass
