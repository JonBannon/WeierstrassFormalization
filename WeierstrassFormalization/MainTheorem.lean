/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.GaussianRealization
import WeierstrassFormalization.ComplexConjugation
import WeierstrassFormalization.ConjugatePairing

/-!
# Main theorem

Formalizes Theorem `thm:main`: an effective divisor on `𝔻` is the zero
divisor of a holomorphic function on `𝔻` with integer Taylor coefficients
if and only if it is invariant under complex conjugation.
-/

namespace Weierstrass

open Complex

/-- `f` has Taylor coefficients in `ℤ`. -/
def HasIntCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ k : ℤ, taylorCoeff f n = (k : ℂ)

/-! ## Necessity: real-coefficient functions have conjugate-symmetric zero divisors -/

/-- If `f` is holomorphic on `𝔻` with real (in particular, integer) Taylor coefficients, then `f`
is invariant under the "double conjugation" `z ↦ conj (f (conj z))`, throughout `𝔻`. -/
private theorem eqOn_conj_comp_conj_of_taylorCoeff_real {f : ℂ → ℂ} (hf : HolomorphicOn f)
    (hreal : ∀ n, (starRingEnd ℂ) (taylorCoeff f n) = taylorCoeff f n) :
    Set.EqOn f (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) 𝔻 := by
  have h0 : (0 : ℂ) ∈ 𝔻 := by simp [mem_𝔻_iff]
  have hf0 : AnalyticAt ℂ f 0 := hf 0 h0
  have hg0 : AnalyticAt ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) 0 := by
    have := analyticAt_conj_comp_conj hf0
    simpa using this
  have hpf := hf0.hasFPowerSeriesAt
  have hpg := hg0.hasFPowerSeriesAt
  have hcoeff_eq : (fun n => iteratedDeriv n (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) 0
      / (n.factorial : ℂ)) = fun n => iteratedDeriv n f 0 / (n.factorial : ℂ) := by
    funext n
    have hstep := taylorCoeff_conj_comp_conj hf0 n
    have hreal' := hreal n
    unfold taylorCoeff at hstep hreal'
    rw [hstep, hreal']
  rw [hcoeff_eq] at hpg
  obtain ⟨r1, hr1⟩ := hpf
  obtain ⟨r2, hr2⟩ := hpg
  have hunique := (hr1.mono (lt_min hr1.r_pos hr2.r_pos) inf_le_left).unique
    (hr2.mono (lt_min hr1.r_pos hr2.r_pos) inf_le_right)
  have heventually : f =ᶠ[nhds (0 : ℂ)] (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) := by
    filter_upwards [Metric.eball_mem_nhds (0 : ℂ) (lt_min hr1.r_pos hr2.r_pos)] with y hy
      using hunique hy
  have h𝔻open : IsOpen 𝔻 := Metric.isOpen_ball
  have h𝔻preconn : IsPreconnected 𝔻 := (convex_ball (0 : ℂ) 1).isPreconnected
  have hganalytic : AnalyticOnNhd ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) 𝔻 := by
    intro z hz
    have hconjz : (starRingEnd ℂ) z ∈ 𝔻 := by
      rw [mem_𝔻_iff] at hz ⊢
      rwa [Complex.norm_conj]
    have := analyticAt_conj_comp_conj (hf ((starRingEnd ℂ) z) hconjz)
    rwa [Complex.conj_conj] at this
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hf hganalytic h𝔻preconn h0 heventually

/-- **Necessity direction of Theorem `thm:main`.** If `f` is holomorphic on `𝔻` with the zero
divisor of `D` and integer Taylor coefficients, then `D` is invariant under complex
conjugation. -/
private theorem conjInvariant_of_hasIntCoeffs {D : EffectiveDivisor} {f : ℂ → ℂ}
    (hf : HolomorphicOn f) (hzd : IsZeroDivisorOf D f) (hcoeff : HasIntCoeffs f) :
    D.ConjInvariant := by
  have hreal : ∀ n, (starRingEnd ℂ) (taylorCoeff f n) = taylorCoeff f n := by
    intro n
    obtain ⟨k, hk⟩ := hcoeff n
    rw [hk]
    simp
  have heqOn := eqOn_conj_comp_conj_of_taylorCoeff_real hf hreal
  have h𝔻open : IsOpen 𝔻 := Metric.isOpen_ball
  intro z
  by_cases hz : z ∈ 𝔻
  · have hconjz : (starRingEnd ℂ) z ∈ 𝔻 := by
      rw [mem_𝔻_iff] at hz ⊢
      rwa [Complex.norm_conj]
    have horder := analyticOrderAt_conj_comp_conj (hf z hz)
    have hev : f =ᶠ[nhds ((starRingEnd ℂ) z)]
        (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) := by
      filter_upwards [h𝔻open.mem_nhds hconjz] with w hw using heqOn hw
    have hcongr : analyticOrderAt (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w)))
        ((starRingEnd ℂ) z) = analyticOrderAt f ((starRingEnd ℂ) z) :=
      (analyticOrderAt_congr hev).symm
    rw [hcongr] at horder
    have h1 : D.mult ((starRingEnd ℂ) z) = analyticOrderNatAt f ((starRingEnd ℂ) z) :=
      hzd ((starRingEnd ℂ) z) hconjz
    have h2 : D.mult z = analyticOrderNatAt f z := hzd z hz
    rw [h1, h2]
    unfold analyticOrderNatAt
    rw [horder]
  · have hconjz : (starRingEnd ℂ) z ∉ 𝔻 := by
      rw [mem_𝔻_iff] at hz
      rw [mem_𝔻_iff]
      rwa [Complex.norm_conj]
    rw [D.mult_eq_zero_of_not_mem_𝔻 z hz, D.mult_eq_zero_of_not_mem_𝔻 _ hconjz]

/-! ## Sufficiency: conjugate-invariant divisors are realized with integer coefficients -/

/-- **Sufficiency direction of Theorem `thm:main`.** Every effective divisor `D` on `𝔻`
invariant under complex conjugation is the zero divisor of a holomorphic function on `𝔻`
with integer Taylor coefficients.

Proof sketch (paper, proof of Theorem `thm:main`): enumerate `D`'s support with multiplicity,
grouping conjugate pairs of nonreal zeros to share a single "slot" of the construction (indexed
`n(k) := k / 2`, so real zeros are padded with a dummy point outside `𝔻` at odd positions).
For a real zero, force the degree-`(n+1)` Taylor coefficient to the nearest integer using a real
correction constant `c`. For a conjugate pair `{a, ā}`, use correction constants `c, c̄`; since
`E_n(z/a;c)·E_n(z/ā;c̄)` has real Taylor coefficients whenever `c̄ = conj c` (conjugating the
whole defining formula of `E_n` commutes with its `+, -, *, /, exp` operations), the resulting
degree-`(n+1)` shift `2 Re((c-1)/((n+1)a^{n+1}))` is a real-affine surjection of `c`; choose the
minimal-norm `c` forcing it to the nearest integer. Both slot types keep the inductive-forcing
and convergence estimates of `exists_coeffSeq`/`exists_Mtest_of_coeffSeq` intact (with at most a
factor-`2` loss from the pair case), and the resulting partial products have real Taylor
coefficients at every stage by construction, so no separate "rounding error can be unbounded"
issue arises (unlike naively rounding a single unpaired nonreal zero's coefficient to `ℝ`). -/
theorem exists_holomorphic_int_coeffs_of_conjInvariant (D : EffectiveDivisor)
    (hD : D.ConjInvariant) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧ IsZeroDivisorOf D f ∧ HasIntCoeffs f := by
  obtain ⟨a, ha0, hamult, hesc, ha_pair⟩ := exists_pairedEnum_of_conjInvariant D hD
  obtain ⟨c, hcforce, hcbound⟩ := exists_pairCoeffSeq a ha0 ha_pair
  have hM := exists_Mtest_of_pairCoeffSeq a c ha0 hesc hcbound
  set n : ℕ → ℕ := fun k => k / 2 with hn_def
  set g : ℂ → ℂ := fun z => ∏' k, E (n k) (c k) (z / a k) with hg_def
  set dd : ℕ := D.mult 0 with hdd_def
  set f : ℂ → ℂ := fun z => z ^ dd * g z with hf_def
  have hnmono : Monotone n := fun k1 k2 h => by simp only [hn_def]; omega
  have hg_holo : HolomorphicOn g := holomorphicOn_tprod_factors (n := n) hM
  have hmono_holo : HolomorphicOn (fun z : ℂ => z ^ dd) := by
    intro z _
    have : Differentiable ℂ (fun z : ℂ => z ^ dd) := by fun_prop
    exact this.analyticAt z
  have hg_analytic0 : AnalyticAt ℂ g 0 := hg_holo 0 (by simp [mem_𝔻_iff])
  -- every Taylor coefficient of `g` lies in `ℤ`.
  have hg_int : ∀ m : ℕ, ∃ k : ℤ, taylorCoeff g m = k := by
    intro m
    obtain ⟨km, hkm⟩ := hcforce m
    refine ⟨km, ?_⟩
    have hstep1 : taylorCoeff g m = taylorCoeff (pairProduct a c (2 * m + 2 + 1)) m :=
      taylorCoeff_tprod_factors_eq_partial (n := n) hnmono hM m (2 * m + 2)
        (show m < n (2 * m + 2) by simp only [hn_def]; omega)
    have hshrink1 := pairProduct_taylorCoeff_shrink a c (2 * m) m (by omega)
    have hshrink2 := pairProduct_taylorCoeff_shrink a c (2 * m + 1) m (by omega)
    have hshrink3 := pairProduct_taylorCoeff_shrink a c (2 * m + 2) m (by omega)
    rw [hstep1, hshrink3, hshrink2, hshrink1, hkm]
  refine ⟨f, ?_, ?_, ?_⟩
  · -- `HolomorphicOn f`
    intro z hz
    exact (hmono_holo z hz).mul (hg_holo z hz)
  · -- `IsZeroDivisorOf D f`
    intro z hz
    have hg_analytic : AnalyticAt ℂ g z := hg_holo z hz
    have hmono_analytic : AnalyticAt ℂ (fun w : ℂ => w ^ dd) z := hmono_holo z hz
    have hg_order : analyticOrderAt g z = ({k | a k = z}.ncard : ℕ∞) :=
      analyticOrderAt_tprod_factors_eq_ncard (n := n) ha0 hM z hz
    have hg_order_ne_top : analyticOrderAt g z ≠ ⊤ := by rw [hg_order]; exact ENat.coe_ne_top _
    have hf_eq : f = fun w => w ^ dd * g w := hf_def
    by_cases hz0 : z = 0
    · subst hz0
      have hmono_order : analyticOrderAt (fun w : ℂ => w ^ dd) (0 : ℂ) = (dd : ℕ∞) := by
        have hfun_eq : (fun x : ℂ => x - 0) ^ dd = fun w : ℂ => w ^ dd := by
          funext x; simp [Pi.pow_apply]
        rw [← hfun_eq]
        exact analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := (0 : ℂ)) (n := dd)
      have hfiber_empty : {k | a k = (0 : ℂ)}.ncard = 0 := by
        have hempty : {k | a k = (0 : ℂ)} = ∅ := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact ha0 k
        rw [hempty, Set.ncard_empty]
      have hmono_order_ne_top : analyticOrderAt (fun w : ℂ => w ^ dd) (0 : ℂ) ≠ ⊤ := by
        rw [hmono_order]; exact ENat.coe_ne_top _
      have hmul := analyticOrderNatAt_mul hmono_analytic hg_analytic
        hmono_order_ne_top hg_order_ne_top
      have hf_eq2 : f = (fun w : ℂ => w ^ dd) * g := hf_eq
      change D.mult 0 = analyticOrderNatAt f 0
      rw [hf_eq2, hmul]
      unfold analyticOrderNatAt
      rw [hmono_order, hg_order, hfiber_empty]
      simp [hdd_def]
    · have hmono_order0 : analyticOrderAt (fun w : ℂ => w ^ dd) z = 0 :=
        hmono_analytic.analyticOrderAt_eq_zero.mpr (pow_ne_zero dd hz0)
      have hmono_order0_ne_top : analyticOrderAt (fun w : ℂ => w ^ dd) z ≠ ⊤ := by
        rw [hmono_order0]; simp
      have hmul := analyticOrderNatAt_mul hmono_analytic hg_analytic
        hmono_order0_ne_top hg_order_ne_top
      have hf_eq2 : f = (fun w : ℂ => w ^ dd) * g := hf_eq
      change D.mult z = analyticOrderNatAt f z
      rw [hf_eq2, hmul]
      unfold analyticOrderNatAt
      rw [hmono_order0, hg_order, hamult z hz hz0]
      simp
  · -- `HasIntCoeffs f`
    intro m
    have hshift := taylorCoeff_pow_mul hg_analytic0 dd m
    by_cases hdm : dd ≤ m
    · obtain ⟨kg, hkg⟩ := hg_int (m - dd)
      refine ⟨kg, ?_⟩
      rw [hf_def]
      rw [if_pos hdm] at hshift
      rw [hshift, hkg]
    · refine ⟨0, ?_⟩
      rw [hf_def]
      rw [if_neg hdm] at hshift
      rw [hshift]
      simp

/-- **Theorem `thm:main`.** An effective divisor `D` on `𝔻` is the zero
divisor of a holomorphic function on `𝔻` with Taylor coefficients in `ℤ`
if and only if `D` is invariant under complex conjugation. -/
theorem exists_holomorphic_int_coeffs_iff_conjInvariant (D : EffectiveDivisor) :
    (∃ f : ℂ → ℂ, HolomorphicOn f ∧ IsZeroDivisorOf D f ∧ HasIntCoeffs f) ↔
      D.ConjInvariant := by
  constructor
  · rintro ⟨f, hf, hzd, hcoeff⟩
    exact conjInvariant_of_hasIntCoeffs hf hzd hcoeff
  · exact exists_holomorphic_int_coeffs_of_conjInvariant D

end Weierstrass
