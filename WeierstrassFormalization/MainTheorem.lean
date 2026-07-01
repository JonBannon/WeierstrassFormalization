/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.GaussianRealization

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

/-- **Core conjugation-composition fact.** Conjugating both the argument and the value of a
complex-differentiable function gives another complex-differentiable function (this is where the
*double* conjugation matters: a single conjugation, e.g. `f ∘ conj`, is generally
anti-holomorphic, not holomorphic). Concretely: if `f` has derivative `f'` at `w`, then
`z ↦ conj (f (conj z))` has derivative `conj f'` at `conj w`. -/
private theorem hasDerivAt_conj_comp_conj {f : ℂ → ℂ} {f' w : ℂ} (hf : HasDerivAt f f' w) :
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
private theorem eventuallyEq_iteratedDeriv_of_eventuallyEq {f g : ℂ → ℂ} {x : ℂ}
    (h : f =ᶠ[nhds x] g) (n : ℕ) : iteratedDeriv n f =ᶠ[nhds x] iteratedDeriv n g := by
  filter_upwards [h.eventually_nhds] with y hy using Filter.EventuallyEq.iteratedDeriv_eq n hy

/-- Doubly conjugating a function analytic near `0` conjugates its iterated derivatives at `0`,
order by order. -/
private theorem iteratedDeriv_conj_comp_conj_eventuallyEq {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
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
private theorem taylorCoeff_conj_comp_conj {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorCoeff (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) n
      = (starRingEnd ℂ) (taylorCoeff f n) := by
  have hev := (iteratedDeriv_conj_comp_conj_eventuallyEq hf n).eq_of_nhds
  unfold taylorCoeff
  simp only [starRingEnd_apply] at hev ⊢
  rw [hev]
  simp

/-- Doubly conjugating an analytic function gives an analytic function, at the conjugate
point. -/
private theorem analyticAt_conj_comp_conj {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
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
private theorem analyticOrderAt_conj_comp_conj {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
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
  sorry

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
