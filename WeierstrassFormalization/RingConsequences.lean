/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.GaussianRealization
import WeierstrassFormalization.MainTheorem

/-!
# Ring-theoretic consequences

Formalizes Section `sec:algebra`: the subrings `𝓞(𝔻)`, `ℛ = ℤ[i][[z]] ∩ 𝓞(𝔻)`, and
`ℛ_ℝ = ℤ[[z]] ∩ 𝓞(𝔻)` of holomorphic functions on `𝔻`, and the propositions and
corollary describing their unit groups, factorization, and the contraction map
`MaxSpec(𝓞(𝔻)) → Spec(ℛ)`.
-/

namespace Weierstrass

open Complex

/-! ## Taylor coefficients of a sum and a product -/

/-- The Taylor coefficients of a sum are the sum of the Taylor coefficients. -/
theorem taylorCoeff_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (fun z => f z + g z) n = taylorCoeff f n + taylorCoeff g n := by
  have hf' : ContDiffAt ℂ (n : ℕ) f 0 := hf.contDiffAt.of_le le_top
  have hg' : ContDiffAt ℂ (n : ℕ) g 0 := hg.contDiffAt.of_le le_top
  unfold taylorCoeff
  rw [iteratedDeriv_fun_add hf' hg', add_div]

/-- The Taylor coefficients of a negation are the negation of the Taylor coefficients. -/
theorem taylorCoeff_neg (f : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (fun z => -f z) n = -taylorCoeff f n := by
  unfold taylorCoeff
  rw [iteratedDeriv_fun_neg n f 0, neg_div]

/-- **Cauchy product for Taylor coefficients.** The `n`-th Taylor coefficient of a product
`f · g` is the discrete convolution of the Taylor coefficients of `f` and `g`. -/
theorem taylorCoeff_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    taylorCoeff (fun z => f z * g z) n
      = ∑ i ∈ Finset.range (n + 1), taylorCoeff f i * taylorCoeff g (n - i) := by
  have hf' : ContDiffAt ℂ (n : ℕ) f 0 := hf.contDiffAt.of_le le_top
  have hg' : ContDiffAt ℂ (n : ℕ) g 0 := hg.contDiffAt.of_le le_top
  have hsum := iteratedDeriv_fun_mul hf' hg'
  have hfactorial_ne_zero : ∀ j : ℕ, (Nat.factorial j : ℂ) ≠ 0 := fun j => by
    exact_mod_cast Nat.factorial_ne_zero j
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℂ) * iteratedDeriv i f 0 * iteratedDeriv (n - i) g 0
        = (taylorCoeff f i * taylorCoeff g (n - i)) * (Nat.factorial n : ℂ) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hfact : (n.choose i : ℂ) * (Nat.factorial i : ℂ) * (Nat.factorial (n - i) : ℂ)
        = (Nat.factorial n : ℂ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
    have hderiv_f : iteratedDeriv i f 0 = taylorCoeff f i * (Nat.factorial i : ℂ) := by
      unfold taylorCoeff; rw [div_mul_cancel₀ _ (hfactorial_ne_zero i)]
    have hderiv_g : iteratedDeriv (n - i) g 0
        = taylorCoeff g (n - i) * (Nat.factorial (n - i) : ℂ) := by
      unfold taylorCoeff; rw [div_mul_cancel₀ _ (hfactorial_ne_zero (n - i))]
    rw [hderiv_f, hderiv_g, ← hfact]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hsum
  change iteratedDeriv n (fun z => f z * g z) 0 / (Nat.factorial n : ℂ)
      = ∑ i ∈ Finset.range (n + 1), taylorCoeff f i * taylorCoeff g (n - i)
  rw [hsum, mul_div_cancel_right₀ _ (hfactorial_ne_zero n)]

/-- `0 ∈ 𝔻`, used repeatedly to extract `AnalyticAt ℂ f 0` from `HolomorphicOn f`. -/
theorem zero_mem_𝔻 : (0 : ℂ) ∈ 𝔻 := mem_𝔻_iff.mpr (by norm_num)

/-- The Taylor coefficients of a constant function. -/
theorem taylorCoeff_const (c : ℂ) (n : ℕ) :
    taylorCoeff (fun _ : ℂ => c) n = if n = 0 then c else 0 := by
  unfold taylorCoeff
  rw [iteratedDeriv_const]
  split_ifs with h <;> simp [h]

/-! ## Closure of `HasGaussianIntCoeffs` under the ring operations -/

theorem hasGaussianIntCoeffs_zero : HasGaussianIntCoeffs (fun _ : ℂ => (0 : ℂ)) :=
  fun n => ⟨0, by rw [taylorCoeff_const]; split_ifs <;> simp⟩

theorem hasGaussianIntCoeffs_one : HasGaussianIntCoeffs (fun _ : ℂ => (1 : ℂ)) := by
  intro n
  by_cases hn : n = 0
  · exact ⟨1, by rw [taylorCoeff_const, if_pos hn]; simp⟩
  · exact ⟨0, by rw [taylorCoeff_const, if_neg hn]; simp⟩

theorem hasGaussianIntCoeffs_add {f g : ℂ → ℂ} (hf : HolomorphicOn f) (hg : HolomorphicOn g)
    (hfi : HasGaussianIntCoeffs f) (hgi : HasGaussianIntCoeffs g) :
    HasGaussianIntCoeffs (fun z => f z + g z) := by
  intro n
  obtain ⟨zf, hzf⟩ := hfi n
  obtain ⟨zg, hzg⟩ := hgi n
  exact ⟨zf + zg, by
    rw [taylorCoeff_add (hf 0 zero_mem_𝔻) (hg 0 zero_mem_𝔻), hzf, hzg, GaussianInt.toComplex_add]⟩

theorem hasGaussianIntCoeffs_neg {f : ℂ → ℂ} (hfi : HasGaussianIntCoeffs f) :
    HasGaussianIntCoeffs (fun z => -f z) := by
  intro n
  obtain ⟨zf, hzf⟩ := hfi n
  exact ⟨-zf, by rw [taylorCoeff_neg f n, hzf, GaussianInt.toComplex_neg]⟩

theorem hasGaussianIntCoeffs_mul {f g : ℂ → ℂ} (hf : HolomorphicOn f) (hg : HolomorphicOn g)
    (hfi : HasGaussianIntCoeffs f) (hgi : HasGaussianIntCoeffs g) :
    HasGaussianIntCoeffs (fun z => f z * g z) := by
  intro n
  choose zf hzf using hfi
  choose zg hzg using hgi
  refine ⟨∑ i ∈ Finset.range (n + 1), zf i * zg (n - i), ?_⟩
  rw [taylorCoeff_mul (hf 0 zero_mem_𝔻) (hg 0 zero_mem_𝔻), map_sum]
  exact Finset.sum_congr rfl (fun i _ => by rw [map_mul, hzf i, hzg (n - i)])

/-! ## Closure of `HasIntCoeffs` under the ring operations -/

theorem hasIntCoeffs_zero : HasIntCoeffs (fun _ : ℂ => (0 : ℂ)) :=
  fun n => ⟨0, by rw [taylorCoeff_const]; split_ifs <;> simp⟩

theorem hasIntCoeffs_one : HasIntCoeffs (fun _ : ℂ => (1 : ℂ)) := by
  intro n
  by_cases hn : n = 0
  · exact ⟨1, by rw [taylorCoeff_const, if_pos hn]; simp⟩
  · exact ⟨0, by rw [taylorCoeff_const, if_neg hn]; simp⟩

theorem hasIntCoeffs_add {f g : ℂ → ℂ} (hf : HolomorphicOn f) (hg : HolomorphicOn g)
    (hfi : HasIntCoeffs f) (hgi : HasIntCoeffs g) :
    HasIntCoeffs (fun z => f z + g z) := by
  intro n
  obtain ⟨kf, hkf⟩ := hfi n
  obtain ⟨kg, hkg⟩ := hgi n
  exact ⟨kf + kg, by
    rw [taylorCoeff_add (hf 0 zero_mem_𝔻) (hg 0 zero_mem_𝔻), hkf, hkg]; push_cast; ring⟩

theorem hasIntCoeffs_neg {f : ℂ → ℂ} (hfi : HasIntCoeffs f) :
    HasIntCoeffs (fun z => -f z) := by
  intro n
  obtain ⟨kf, hkf⟩ := hfi n
  exact ⟨-kf, by rw [taylorCoeff_neg f n, hkf]; push_cast; ring⟩

theorem hasIntCoeffs_mul {f g : ℂ → ℂ} (hf : HolomorphicOn f) (hg : HolomorphicOn g)
    (hfi : HasIntCoeffs f) (hgi : HasIntCoeffs g) :
    HasIntCoeffs (fun z => f z * g z) := by
  intro n
  choose kf hkf using hfi
  choose kg hkg using hgi
  refine ⟨∑ i ∈ Finset.range (n + 1), kf i * kg (n - i), ?_⟩
  rw [taylorCoeff_mul (hf 0 zero_mem_𝔻) (hg 0 zero_mem_𝔻)]
  push_cast
  exact Finset.sum_congr rfl (fun i _ => by rw [hkf i, hkg (n - i)])

/-! ## Proposition `prop:nv`: nowhere-vanishing functions with `ℤ[i]`-coefficients -/

/-- **Proposition `prop:nv`.** Given a sequence `a : ℕ → ℂ` lying outside the closed unit
disk with `‖a n‖ → 1`, there is a holomorphic function on `𝔻` with Taylor coefficients in
`ℤ[i]`, nowhere vanishing on `𝔻`, with value `1` at the origin. -/
theorem exists_holomorphic_gaussianInt_coeffs_nowhereVanishing
    (a : ℕ → ℂ) (ha1 : ∀ n, 1 < ‖a n‖)
    (_hesc : Filter.Tendsto (fun n => ‖a n‖) Filter.atTop (nhds 1)) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧ HasGaussianIntCoeffs f ∧ (∀ z ∈ 𝔻, f z ≠ 0) ∧ f 0 = 1 := by
  have ha0 : ∀ k, a k ≠ 0 := fun k h => by
    have := ha1 k; rw [h] at this; norm_num at this
  have hesc_empty : ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite := by
    intro s hs
    have hempty : {k | ‖a k‖ < s} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hlt; linarith [ha1 k]
    rw [hempty]; exact Set.finite_empty
  obtain ⟨c, hcforce, hcbound⟩ := exists_coeffSeq a ha0
  have hM := exists_Mtest_of_coeffSeq a c ha0 hesc_empty hcbound
  set g : ℂ → ℂ := fun z => ∏' k, E k (c k) (z / a k) with hg_def
  have hg_holo : HolomorphicOn g := holomorphicOn_tprod_factors (n := id) hM
  refine ⟨g, hg_holo, ?_, ?_, ?_⟩
  · -- `HasGaussianIntCoeffs g`
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
  · -- nowhere vanishing on `𝔻`
    intro z hz
    have hg_analytic : AnalyticAt ℂ g z := hg_holo z hz
    have hg_order : analyticOrderAt g z = ({k | a k = z}.ncard : ℕ∞) :=
      analyticOrderAt_tprod_factors_eq_ncard (n := id) ha0 hM z hz
    have hempty : {k | a k = z} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hak
      have h1 : ‖z‖ < 1 := mem_𝔻_iff.mp hz
      have h2 : 1 < ‖a k‖ := ha1 k
      rw [hak] at h2; linarith
    rw [hempty, Set.ncard_empty] at hg_order
    exact hg_analytic.analyticOrderAt_eq_zero.mp (by exact_mod_cast hg_order)
  · -- `g 0 = 1`
    have hstep : taylorCoeff g 0 = taylorCoeff (partialProduct a c 2) 0 :=
      taylorCoeff_tprod_factors_eq_partial (n := id) monotone_id hM 0 1
        (show (0 : ℕ) < 1 by omega)
    have hval : taylorCoeff (partialProduct a c 2) 0 = (partialProduct a c 2) 0 := by
      unfold taylorCoeff; simp
    have hprod0 : (partialProduct a c 2) 0 = 1 := by
      unfold partialProduct; simp [E_zero]
    have hgval : taylorCoeff g 0 = g 0 := by unfold taylorCoeff; simp
    rw [← hgval, hstep, hval, hprod0]

/-! ## Proposition `prop:units`: the reciprocal-power-series recursion -/

/-- The `0`-th Taylor coefficient of any function is its value at `0`. -/
theorem taylorCoeff_zero_eq (f : ℂ → ℂ) : taylorCoeff f 0 = f 0 := by
  unfold taylorCoeff; simp

/-- Auxiliary "history table" for the reciprocal-power-series recursion: `reciprocalSeqAux u r N`
records the first `N + 1` terms of the sequence, built by ordinary structural recursion on `N`
(the memoized-history device used elsewhere in this project for recursions depending on more
than the immediately preceding term, e.g. `auxP`/`auxQ`). -/
private noncomputable def reciprocalSeqAux {R : Type*} [CommRing R] (u : Rˣ) (r : ℕ → R) :
    ℕ → ℕ → R
  | 0, _ => ((u⁻¹ : Rˣ) : R)
  | (N + 1), k =>
      if k ≤ N then reciprocalSeqAux u r N k
      else -((u⁻¹ : Rˣ) : R)
        * ∑ j ∈ Finset.range (N + 1), r (j + 1) * reciprocalSeqAux u r N (N - j)

/-- The reciprocal-power-series coefficients: the unique sequence `s` with `s 0 = u⁻¹` and
`s (n+1) = -u⁻¹ · ∑_{k=0}^{n} r (k+1) · s (n-k)`, matching the formal recursion for the
reciprocal of a power series `∑ r n z ^ n` with unit constant term `u`. -/
private noncomputable def reciprocalSeq {R : Type*} [CommRing R] (u : Rˣ) (r : ℕ → R) (n : ℕ) :
    R :=
  reciprocalSeqAux u r n n

private theorem reciprocalSeqAux_stable {R : Type*} [CommRing R] (u : Rˣ) (r : ℕ → R)
    (N k : ℕ) (hk : k ≤ N) : reciprocalSeqAux u r (N + 1) k = reciprocalSeqAux u r N k := by
  simp only [reciprocalSeqAux, if_pos hk]

private theorem reciprocalSeqAux_eq_reciprocalSeq {R : Type*} [CommRing R] (u : Rˣ) (r : ℕ → R) :
    ∀ N k, k ≤ N → reciprocalSeqAux u r N k = reciprocalSeq u r k := by
  intro N
  induction N with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0; rfl
  | succ N ih =>
      intro k hk
      rcases Nat.lt_or_ge k (N + 1) with hlt | hge
      · exact (reciprocalSeqAux_stable u r N k (by omega)).trans (ih k (by omega))
      · have : k = N + 1 := by omega
        subst this; rfl

private theorem reciprocalSeq_zero {R : Type*} [CommRing R] (u : Rˣ) (r : ℕ → R) :
    reciprocalSeq u r 0 = ((u⁻¹ : Rˣ) : R) := rfl

private theorem reciprocalSeq_succ {R : Type*} [CommRing R] (u : Rˣ) (r : ℕ → R) (N : ℕ) :
    reciprocalSeq u r (N + 1)
      = -((u⁻¹ : Rˣ) : R) * ∑ j ∈ Finset.range (N + 1), r (j + 1) * reciprocalSeq u r (N - j) := by
  have hunfold : reciprocalSeq u r (N + 1)
      = -((u⁻¹ : Rˣ) : R)
        * ∑ j ∈ Finset.range (N + 1), r (j + 1) * reciprocalSeqAux u r N (N - j) := by
    change reciprocalSeqAux u r (N + 1) (N + 1) = _
    simp only [reciprocalSeqAux, if_neg (show ¬ N + 1 ≤ N by omega)]
  rw [hunfold]
  congr 1
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [reciprocalSeqAux_eq_reciprocalSeq u r N (N - j) (Nat.sub_le N j)]

/-- **The reciprocal-power-series argument underlying Proposition `prop:units`.** If `f` is
holomorphic and nowhere-vanishing on `𝔻`, its Taylor coefficients all lie in the image of an
injective-on-units ring hom `φ : R →+* ℂ` (via a sequence `r`), and `f 0` is the image of a
*unit* `u` of `R`, then the Taylor coefficients of `1/f` also all lie in the image of `φ`. This
is the "formal inverse of a unit-constant-term power series stays integral" fact used to show
that the reciprocal of a unit of `ℛ` (or `ℛ_ℝ`) again lies in `ℛ` (or `ℛ_ℝ`). -/
theorem hasCoeffsIn_inv {R : Type*} [CommRing R] (φ : R →+* ℂ)
    {f : ℂ → ℂ} (hf : HolomorphicOn f) (hfnv : ∀ z ∈ 𝔻, f z ≠ 0)
    (r : ℕ → R) (hr : ∀ n, taylorCoeff f n = φ (r n)) (u : Rˣ) (hu : φ (u : R) = f 0) :
    ∀ n, taylorCoeff (fun z => (f z)⁻¹) n = φ (reciprocalSeq u r n) := by
  have hf0ne : f 0 ≠ 0 := hfnv 0 zero_mem_𝔻
  have hf_at0 : AnalyticAt ℂ f 0 := hf 0 zero_mem_𝔻
  have hfinv_at0 : AnalyticAt ℂ (fun z => (f z)⁻¹) 0 := hf_at0.inv hf0ne
  have h𝔻nhds : 𝔻 ∈ nhds (0 : ℂ) := Metric.isOpen_ball.mem_nhds zero_mem_𝔻
  have hfg_ev : (fun z => f z * (f z)⁻¹) =ᶠ[nhds (0 : ℂ)] (fun _ : ℂ => (1 : ℂ)) := by
    filter_upwards [h𝔻nhds] with z hz
    exact mul_inv_cancel₀ (hfnv z hz)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have htaylor_eq :
        taylorCoeff (fun z => f z * (f z)⁻¹) n = taylorCoeff (fun _ : ℂ => (1 : ℂ)) n := by
      unfold taylorCoeff
      exact congrArg (· / (Nat.factorial n : ℂ))
        (eventuallyEq_iteratedDeriv_of_eventuallyEq hfg_ev n).self_of_nhds
    rw [taylorCoeff_mul hf_at0 hfinv_at0 n, taylorCoeff_const, Finset.sum_range_succ',
      Nat.sub_zero] at htaylor_eq
    rw [taylorCoeff_zero_eq f] at htaylor_eq
    rcases n with _ | m
    · -- base case `n = 0`
      simp only [Finset.range_zero, Finset.sum_empty, zero_add] at htaylor_eq
      norm_num at htaylor_eq
      rw [reciprocalSeq_zero]
      have hfu : φ (u : R) * φ ((u⁻¹ : Rˣ) : R) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [hu] at hfu
      exact mul_left_cancel₀ hf0ne (htaylor_eq.trans hfu.symm)
    · -- inductive step `n = m + 1`
      have hsub : ∀ i ∈ Finset.range (m + 1), (m + 1) - (i + 1) = m - i := by
        intro i hi; have : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi); omega
      rw [Finset.sum_congr rfl (fun i hi => by rw [hsub i hi])] at htaylor_eq
      simp only [if_neg (Nat.succ_ne_zero m)] at htaylor_eq
      have hsum_eq : ∑ i ∈ Finset.range (m + 1), taylorCoeff f (i + 1) * taylorCoeff
          (fun z => (f z)⁻¹) (m - i) = φ (∑ i ∈ Finset.range (m + 1), r (i + 1)
            * reciprocalSeq u r (m - i)) := by
        rw [map_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have him : m - i ≤ m := Nat.sub_le m i
        rw [map_mul, hr (i + 1), ih (m - i) (by omega)]
      rw [hsum_eq] at htaylor_eq
      have hSeq : ∑ i ∈ Finset.range (m + 1), r (i + 1) * reciprocalSeq u r (m - i)
          = -((u : Rˣ) : R) * reciprocalSeq u r (m + 1) := by
        rw [reciprocalSeq_succ u r m, ← mul_assoc]
        have hu2 : -((u : Rˣ) : R) * -((u⁻¹ : Rˣ) : R) = 1 := by
          rw [neg_mul_neg, Units.mul_inv]
        rw [hu2, one_mul]
      rw [hSeq, map_mul, map_neg, hu] at htaylor_eq
      have : f 0 * taylorCoeff (fun z => (f z)⁻¹) (m + 1)
          = f 0 * φ (reciprocalSeq u r (m + 1)) := by linear_combination htaylor_eq
      exact mul_left_cancel₀ hf0ne this

/-! ## Proposition `prop:units`: units of `ℛ` and `ℛ_ℝ` -/

/-- `f` is a unit of `ℛ = ℤ[i][[z]] ∩ 𝒪(𝔻)`: it lies in `ℛ` and has a multiplicative inverse
that also lies in `ℛ`. -/
def IsUnitOfGaussianIntRing (f : ℂ → ℂ) : Prop :=
  HolomorphicOn f ∧ HasGaussianIntCoeffs f ∧
    ∃ g : ℂ → ℂ, HolomorphicOn g ∧ HasGaussianIntCoeffs g ∧ ∀ z ∈ 𝔻, f z * g z = 1

/-- `f` is a unit of `ℛ_ℝ = ℤ[[z]] ∩ 𝒪(𝔻)`. -/
def IsUnitOfIntRing (f : ℂ → ℂ) : Prop :=
  HolomorphicOn f ∧ HasIntCoeffs f ∧
    ∃ g : ℂ → ℂ, HolomorphicOn g ∧ HasIntCoeffs g ∧ ∀ z ∈ 𝔻, f z * g z = 1

/-- **Proposition `prop:units` (Gaussian-integer half).** An element `f` of `ℛ` is a unit iff
`f 0 ∈ ℤ[i]ˣ` and `f` is nowhere-vanishing on `𝔻`. -/
theorem isUnitOfGaussianIntRing_iff {f : ℂ → ℂ} (hf : HolomorphicOn f)
    (hfi : HasGaussianIntCoeffs f) :
    IsUnitOfGaussianIntRing f ↔
      (∃ u : GaussianInt, f 0 = (u : ℂ) ∧ IsUnit u) ∧ (∀ z ∈ 𝔻, f z ≠ 0) := by
  constructor
  · rintro ⟨-, -, g, -, hgi, hfg⟩
    refine ⟨?_, fun z hz hcontra => by
      have := hfg z hz; rw [hcontra, zero_mul] at this; exact absurd this.symm one_ne_zero⟩
    obtain ⟨zf, hzf⟩ := hfi 0
    obtain ⟨zg, hzg⟩ := hgi 0
    rw [taylorCoeff_zero_eq] at hzf hzg
    have h01 := hfg 0 zero_mem_𝔻
    rw [hzf, hzg] at h01
    have heq : ((zf * zg : GaussianInt) : ℂ) = ((1 : GaussianInt) : ℂ) := by
      rw [GaussianInt.toComplex_mul, GaussianInt.toComplex_one]; exact h01
    exact ⟨zf, hzf, IsUnit.of_mul_eq_one zg (GaussianInt.toComplex_inj.mp heq)⟩
  · rintro ⟨⟨u0, hfu0, u, hu⟩, hfnv⟩
    have hf0ne : f 0 ≠ 0 := hfnv 0 zero_mem_𝔻
    have hfi' := hfi
    choose zr hzr using hfi'
    have hphiu : GaussianInt.toComplex (u : GaussianInt) = f 0 := by rw [hu, ← hfu0]
    refine ⟨hf, hfi, fun z => (f z)⁻¹, fun z hz => (hf z hz).inv (hfnv z hz), ?_,
      fun z hz => mul_inv_cancel₀ (hfnv z hz)⟩
    intro n
    exact ⟨reciprocalSeq u zr n, hasCoeffsIn_inv GaussianInt.toComplex hf hfnv zr hzr u hphiu n⟩

/-- **Proposition `prop:units` (integer half).** An element `f` of `ℛ_ℝ` is a unit iff
`f 0 ∈ ℤˣ = \{\pm 1\}` and `f` is nowhere-vanishing on `𝔻`. -/
theorem isUnitOfIntRing_iff {f : ℂ → ℂ} (hf : HolomorphicOn f) (hfi : HasIntCoeffs f) :
    IsUnitOfIntRing f ↔
      (∃ u : ℤ, f 0 = (u : ℂ) ∧ IsUnit u) ∧ (∀ z ∈ 𝔻, f z ≠ 0) := by
  constructor
  · rintro ⟨-, -, g, -, hgi, hfg⟩
    refine ⟨?_, fun z hz hcontra => by
      have := hfg z hz; rw [hcontra, zero_mul] at this; exact absurd this.symm one_ne_zero⟩
    obtain ⟨kf, hkf⟩ := hfi 0
    obtain ⟨kg, hkg⟩ := hgi 0
    rw [taylorCoeff_zero_eq] at hkf hkg
    have h01 := hfg 0 zero_mem_𝔻
    rw [hkf, hkg] at h01
    have heq : ((kf * kg : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by push_cast; exact h01
    exact ⟨kf, hkf, IsUnit.of_mul_eq_one kg (by exact_mod_cast heq)⟩
  · rintro ⟨⟨u0, hfu0, u, hu⟩, hfnv⟩
    have hf0ne : f 0 ≠ 0 := hfnv 0 zero_mem_𝔻
    have hfi' := hfi
    choose kr hkr using hfi'
    have hphiu : ((u : ℤ) : ℂ) = f 0 := by rw [hu, ← hfu0]
    refine ⟨hf, hfi, fun z => (f z)⁻¹, fun z hz => (hf z hz).inv (hfnv z hz), ?_,
      fun z hz => mul_inv_cancel₀ (hfnv z hz)⟩
    intro n
    exact ⟨reciprocalSeq u kr n,
      hasCoeffsIn_inv (Int.castRingHom ℂ) hf hfnv kr hkr u hphiu n⟩

end Weierstrass
