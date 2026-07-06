/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Basic

/-!
# Complex conjugation and holomorphic functions

Shared utility lemmas about the interaction of complex conjugation with holomorphy, used both
by `MainTheorem.lean` (to show real-coefficient holomorphic functions have conjugate-symmetric
zero divisors) and by `ConjugatePairing.lean` (to show a conjugate-paired product of elementary
factors has real Taylor coefficients).

The recurring theme: a *single* conjugation, e.g. `f ∘ conj`, is generally anti-holomorphic, not
holomorphic; but *doubly* conjugating both the argument and the value, `z ↦ conj (f (conj z))`,
is holomorphic again, and this double conjugation transforms iterated derivatives, Taylor
coefficients, analyticity, and vanishing order in simple, functorial ways.
-/

namespace Weierstrass

open Complex

/-- **Core conjugation-composition fact.** Conjugating both the argument and the value of a
complex-differentiable function gives another complex-differentiable function. Concretely: if
`f` has derivative `f'` at `w`, then `z ↦ conj (f (conj z))` has derivative `conj f'` at
`conj w`. -/
theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' w : ℂ} (hf : HasDerivAt f f' w) :
    HasDerivAt (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) ((starRingEnd ℂ) f')
      ((starRingEnd ℂ) w) := by
  set z₀ : ℂ := (starRingEnd ℂ) w with hz₀_def
  have hconj_z₀ : (starRingEnd ℂ) z₀ = w := by rw [hz₀_def, Complex.conj_conj]
  have hFR : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ) w :=
    hf.hasFDerivAt.restrictScalars ℝ
  have hFR' : HasFDerivAt f ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ)
      ((starRingEnd ℂ) z₀) := by rwa [hconj_z₀]
  have hc1 : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z) (Complex.conjCLE : ℂ →L[ℝ] ℂ) z₀ :=
    Complex.conjCLE.hasFDerivAt
  have hstep1 : HasFDerivAt (fun z : ℂ => f ((starRingEnd ℂ) z))
      (((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ).comp
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z₀ :=
    hFR'.comp z₀ hc1
  have hc2 : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) z) (Complex.conjCLE : ℂ →L[ℝ] ℂ)
      (f ((starRingEnd ℂ) z₀)) := Complex.conjCLE.hasFDerivAt
  have hstep2 : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ).comp
          (Complex.conjCLE : ℂ →L[ℝ] ℂ))) z₀ :=
    hc2.comp z₀ hstep1
  have heq : ((ContinuousLinearMap.toSpanSingleton ℂ ((starRingEnd ℂ) f')).restrictScalars ℝ)
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        (((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ).comp
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) := by
    ext v
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, smul_eq_mul]
    rw [map_mul, Complex.conj_conj]
  have hstep3 : HasFDerivAt (fun z : ℂ => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))
      (ContinuousLinearMap.toSpanSingleton ℂ ((starRingEnd ℂ) f')) z₀ :=
    hasFDerivAt_of_restrictScalars ℝ hstep2 heq
  have := hasFDerivAt_iff_hasDerivAt.mp hstep3
  rwa [ContinuousLinearMap.toSpanSingleton_apply_one] at this

/-- If two functions are eventually equal near `x`, so are their `n`-th iterated derivatives. -/
theorem eventuallyEq_iteratedDeriv_of_eventuallyEq {f g : ℂ → ℂ} {x : ℂ}
    (h : f =ᶠ[nhds x] g) (n : ℕ) : iteratedDeriv n f =ᶠ[nhds x] iteratedDeriv n g := by
  filter_upwards [h.eventually_nhds] with y hy using Filter.EventuallyEq.iteratedDeriv_eq n hy

/-- Doubly conjugating a function analytic near `0` conjugates its iterated derivatives at `0`,
order by order. -/
theorem iteratedDeriv_conj_comp_conj_eventuallyEq {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (n : ℕ) :
    iteratedDeriv n (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) =ᶠ[nhds (0 : ℂ)]
      (fun z => (starRingEnd ℂ) (iteratedDeriv n f ((starRingEnd ℂ) z))) := by
  induction n generalizing f with
  | zero => filter_upwards with z; simp
  | succ n ih =>
      have hev : ∀ᶠ z in nhds (0 : ℂ), HasDerivAt f (deriv f z) z :=
        hf.eventually_analyticAt.mono fun z hz => hz.differentiableAt.hasDerivAt
      have htendsto : Filter.Tendsto (fun w : ℂ => (starRingEnd ℂ) w) (nhds 0) (nhds 0) := by
        have hc : Continuous (fun w : ℂ => (starRingEnd ℂ) w) := continuous_conj
        simpa using hc.tendsto (0 : ℂ)
      have hev' : ∀ᶠ w in nhds (0 : ℂ), HasDerivAt f (deriv f ((starRingEnd ℂ) w))
          ((starRingEnd ℂ) w) := htendsto.eventually hev
      have hderiv_eq : (deriv (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)))) =ᶠ[nhds (0 : ℂ)]
          (fun w => (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) w))) := by
        filter_upwards [hev'] with w hw
        have hd := hasDerivAt_conj_comp_conj hw
        rw [Complex.conj_conj] at hd
        exact hd.deriv
      have hIH := ih (f := deriv f) (hf.deriv)
      have hstep := eventuallyEq_iteratedDeriv_of_eventuallyEq hderiv_eq n
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
      filter_upwards [hstep, hIH] with z hz1 hz2
      rw [hz1, hz2]

/-- Doubly conjugating a function analytic at `0` conjugates its Taylor coefficients at `0`. -/
theorem taylorCoeff_conj_comp_conj {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorCoeff (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) n
      = (starRingEnd ℂ) (taylorCoeff f n) := by
  have hev := (iteratedDeriv_conj_comp_conj_eventuallyEq hf n).eq_of_nhds
  unfold taylorCoeff
  simp only [starRingEnd_apply] at hev ⊢
  rw [hev]
  simp

/-- Doubly conjugating an analytic function gives an analytic function, at the conjugate
point. -/
theorem analyticAt_conj_comp_conj {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) ((starRingEnd ℂ) p) := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hev : ∀ᶠ w in nhds p, DifferentiableAt ℂ f w :=
    hf.eventually_analyticAt.mono fun w hw => hw.differentiableAt
  have htendsto : Filter.Tendsto (fun z : ℂ => (starRingEnd ℂ) z) (nhds ((starRingEnd ℂ) p))
      (nhds p) := by
    have hc : Continuous (fun z : ℂ => (starRingEnd ℂ) z) := continuous_conj
    have := hc.tendsto ((starRingEnd ℂ) p)
    rwa [Complex.conj_conj] at this
  have hev' : ∀ᶠ z in nhds ((starRingEnd ℂ) p), DifferentiableAt ℂ f ((starRingEnd ℂ) z) :=
    htendsto.eventually hev
  filter_upwards [hev'] with z hz
  have hd := hasDerivAt_conj_comp_conj hz.hasDerivAt
  rw [Complex.conj_conj] at hd
  exact hd.differentiableAt

/-- **Order-preservation under double conjugation.** The order of vanishing of `f` at `p` equals
the order of vanishing of `z ↦ conj (f (conj z))` at `conj p`. -/
theorem analyticOrderAt_conj_comp_conj {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    analyticOrderAt (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) ((starRingEnd ℂ) p)
      = analyticOrderAt f p := by
  have hg : AnalyticAt ℂ (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) ((starRingEnd ℂ) p) :=
    analyticAt_conj_comp_conj hf
  have htendsto : Filter.Tendsto (fun z : ℂ => (starRingEnd ℂ) z) (nhds ((starRingEnd ℂ) p))
      (nhds p) := by
    have := Complex.continuous_conj.tendsto ((starRingEnd ℂ) p)
    rwa [Complex.conj_conj] at this
  by_cases htop : analyticOrderAt f p = ⊤
  · have hfz : ∀ᶠ z in nhds p, f z = 0 := analyticOrderAt_eq_top.mp htop
    have hgz : ∀ᶠ w in nhds ((starRingEnd ℂ) p), (starRingEnd ℂ) (f ((starRingEnd ℂ) w)) = 0 := by
      filter_upwards [htendsto.eventually hfz] with w hw using by rw [hw]; simp
    rw [htop, analyticOrderAt_eq_top.mpr hgz]
  · obtain ⟨n, hn⟩ := (analyticOrderAt f p).ne_top_iff_exists.mp htop
    have hn' : analyticOrderAt f p = n := hn.symm
    obtain ⟨φ, hφ, hφne, hφeq⟩ := (hf.analyticOrderAt_eq_natCast (n := n)).mp hn'
    set ψ : ℂ → ℂ := fun w => (starRingEnd ℂ) (φ ((starRingEnd ℂ) w)) with hψ_def
    have hψ : AnalyticAt ℂ ψ ((starRingEnd ℂ) p) := analyticAt_conj_comp_conj hφ
    have hψne : ψ ((starRingEnd ℂ) p) ≠ 0 := by
      simp only [hψ_def, Complex.conj_conj]
      exact fun h => hφne (by simpa using congrArg (starRingEnd ℂ) h)
    have hψeq : ∀ᶠ w in nhds ((starRingEnd ℂ) p), (starRingEnd ℂ) (f ((starRingEnd ℂ) w))
        = (w - (starRingEnd ℂ) p) ^ n • ψ w := by
      filter_upwards [htendsto.eventually hφeq] with w hw
      rw [hw]
      simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj, hψ_def]
    rw [hn', hg.analyticOrderAt_eq_natCast.mpr ⟨ψ, hψ, hψne, hψeq⟩]

end Weierstrass
