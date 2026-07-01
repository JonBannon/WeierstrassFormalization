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

open Complex Filter Topology

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

/-! ## Proposition `prop:associate`: factorization up to units in `𝒪(𝔻)` -/

/-- `𝔻` is preconnected (it is a ball, hence convex). -/
theorem isPreconnected_𝔻 : IsPreconnected 𝔻 := (convex_ball (0 : ℂ) 1).isPreconnected

/-- If `f` is holomorphic on `𝔻` and not identically zero there, its analytic order is finite
at every point of `𝔻`: by the identity theorem, `f` cannot vanish identically near any point of
the connected set `𝔻` without vanishing identically everywhere on `𝔻`. -/
theorem analyticOrderAt_ne_top_of_ne_zero_somewhere {f : ℂ → ℂ} (hf : HolomorphicOn f)
    (hfne : ∃ z ∈ 𝔻, f z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ 𝔻) : analyticOrderAt f z₀ ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hzero : Set.EqOn f 0 𝔻 :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_𝔻 hz₀ htop
  obtain ⟨z, hzD, hzne⟩ := hfne
  exact hzne (hzero hzD)

/-- **The zero divisor of a holomorphic function that is not identically zero.** Its support is
locally finite by the identity theorem: a not-identically-zero analytic function on the connected
set `𝔻` has isolated zeros, hence meets every compact subset in only finitely many of them. -/
noncomputable def zeroDivisorOfHolomorphic (f : ℂ → ℂ) (hf : HolomorphicOn f)
    (hfne : ∃ z ∈ 𝔻, f z ≠ 0) : EffectiveDivisor where
  mult z := @ite _ (z ∈ 𝔻) (Classical.propDecidable _) (analyticOrderNatAt f z) 0
  mult_eq_zero_of_not_mem_𝔻 z hz := if_neg hz
  finite_inter_compact K hKsub hKcpt := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_𝔻 with hz0 | hev
    · obtain ⟨z, hzD, hzne⟩ := hfne
      exact absurd (hz0 hzD) hzne
    · have hmemK : {x : ℂ | f x ≠ 0} ∈ Filter.codiscreteWithin K :=
        Filter.codiscreteWithin_mono hKsub hev
      have hfin := hKcpt.finite_sdiff_of_mem_codiscreteWithin hmemK
      refine Set.Finite.subset hfin (fun z hz => ?_)
      obtain ⟨hzK, hzmult⟩ := hz
      have hzD : z ∈ 𝔻 := hKsub hzK
      rw [if_pos hzD] at hzmult
      have hfz0 : f z = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzmult
      simp only [Set.mem_sdiff, Set.mem_setOf_eq, not_not]
      exact ⟨hzK, hfz0⟩

/-- The divisor `zeroDivisorOfHolomorphic f hf hfne` is indeed the zero divisor of `f`. -/
theorem isZeroDivisorOf_zeroDivisorOfHolomorphic (f : ℂ → ℂ) (hf : HolomorphicOn f)
    (hfne : ∃ z ∈ 𝔻, f z ≠ 0) :
    IsZeroDivisorOf (zeroDivisorOfHolomorphic f hf hfne) f := by
  classical
  intro z hz
  change (if z ∈ 𝔻 then analyticOrderNatAt f z else 0) = analyticOrderNatAt f z
  rw [if_pos hz]

/-- If `f` is holomorphic on `𝔻` and has finite analytic order at *one* point of `𝔻`, it has
finite analytic order at *every* point of `𝔻` (it cannot be identically zero near that one
point without being identically zero everywhere, by the identity theorem). -/
theorem analyticOrderAt_ne_top_of_analyticOrderAt_ne_top_at {f : ℂ → ℂ} (hf : HolomorphicOn f)
    {z₁ : ℂ} (hz₁ : z₁ ∈ 𝔻) (hfin : analyticOrderAt f z₁ ≠ ⊤) {z₀ : ℂ} (hz₀ : z₀ ∈ 𝔻) :
    analyticOrderAt f z₀ ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hzero : Set.EqOn f 0 𝔻 :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_𝔻 hz₀ htop
  apply hfin
  rw [analyticOrderAt_eq_top]
  filter_upwards [Metric.isOpen_ball.mem_nhds hz₁] with z hz using hzero hz

/-- At a common zero of `f` and `g` of the same finite order, the ratio `f / g` has a
removable singularity with a nonzero limit. -/
theorem exists_tendsto_div_nhdsWithin_ne_of_analyticOrderNatAt_eq
    {f g : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀)
    (hf_fin : analyticOrderAt f z₀ ≠ ⊤) (hg_fin : analyticOrderAt g z₀ ≠ ⊤)
    (horder : analyticOrderNatAt f z₀ = analyticOrderNatAt g z₀) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (fun w => f w / g w) (𝓝[≠] z₀) (𝓝 L) := by
  set n := analyticOrderNatAt f z₀ with hn_def
  obtain ⟨f₁, hf₁_an, hf₁_ne, hf₁_eq⟩ := (hf.analyticOrderNatAt_eq_iff hf_fin).mp rfl
  obtain ⟨g₁, hg₁_an, hg₁_ne, hg₁_eq⟩ :=
    (hg.analyticOrderNatAt_eq_iff hg_fin (n := n)).mp horder.symm
  refine ⟨f₁ z₀ / g₁ z₀, div_ne_zero hf₁_ne hg₁_ne, ?_⟩
  have htendsto_quot : Tendsto (fun w => f₁ w / g₁ w) (𝓝[≠] z₀) (𝓝 (f₁ z₀ / g₁ z₀)) :=
    (hf₁_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div
      (hg₁_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hg₁_ne
  refine htendsto_quot.congr' ?_
  filter_upwards [hf₁_eq.filter_mono nhdsWithin_le_nhds, hg₁_eq.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hfw hgw hwne
  have hpow_ne : (w - z₀) ^ n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hwne)
  rw [hfw, hgw, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ hpow_ne]

/-- **The key analytic lemma behind Proposition `prop:associate`.** If `f, g` are holomorphic
on `𝔻`, have the same analytic order at every point, and this common order is nonzero
somewhere (so neither is identically zero), then `f / g` extends to a holomorphic,
nowhere-vanishing function `u` on `𝔻` with `f = g * u` throughout: at a common zero of `f` and
`g`, the ratio `f / g` has a removable singularity with nonzero limit. -/
theorem exists_holomorphicOn_nowhereVanishing_mul_eq_of_analyticOrderNatAt_eq
    {f g : ℂ → ℂ} (hf : HolomorphicOn f) (hg : HolomorphicOn g)
    (horder : ∀ z ∈ 𝔻, analyticOrderNatAt f z = analyticOrderNatAt g z)
    (hsomepos : ∃ z ∈ 𝔻, analyticOrderNatAt f z ≠ 0) :
    ∃ u : ℂ → ℂ, HolomorphicOn u ∧ (∀ z ∈ 𝔻, u z ≠ 0) ∧ ∀ z ∈ 𝔻, f z = g z * u z := by
  classical
  obtain ⟨z₁, hz₁, hz₁ne⟩ := hsomepos
  have hf_fin1 : analyticOrderAt f z₁ ≠ ⊤ := fun h => hz₁ne (by simp [analyticOrderNatAt, h])
  have hg_fin1 : analyticOrderAt g z₁ ≠ ⊤ := fun h => by
    apply hz₁ne; rw [horder z₁ hz₁]; simp [analyticOrderNatAt, h]
  have hf_fin : ∀ z ∈ 𝔻, analyticOrderAt f z ≠ ⊤ :=
    fun z hz => analyticOrderAt_ne_top_of_analyticOrderAt_ne_top_at hf hz₁ hf_fin1 hz
  have hg_fin : ∀ z ∈ 𝔻, analyticOrderAt g z ≠ ⊤ :=
    fun z hz => analyticOrderAt_ne_top_of_analyticOrderAt_ne_top_at hg hz₁ hg_fin1 hz
  -- the naive quotient, corrected by its limit at removable singularities
  set u : ℂ → ℂ := fun z => if g z ≠ 0 then f z / g z else limUnder (𝓝[≠] z) (fun w => f w / g w)
    with hu_def
  have hu_eq_div : ∀ z, g z ≠ 0 → u z = f z / g z := fun z hz => by rw [hu_def]; simp [hz]
  -- at a zero of `g`, both `f` and `g` vanish (matching orders), and `u z` is the nonzero limit
  have hg_zero_imp : ∀ z ∈ 𝔻, g z = 0 → f z = 0 ∧ ∃ L, L ≠ 0 ∧
      Tendsto (fun w => f w / g w) (𝓝[≠] z) (𝓝 L) ∧ u z = L ∧ ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
    intro z hz hgz
    have hgorder_ne : analyticOrderNatAt g z ≠ 0 := by
      intro h0
      have hcast := Nat.cast_analyticOrderNatAt (hg_fin z hz)
      rw [h0] at hcast
      exact (analyticOrderAt_ne_zero.mpr ⟨hg z hz, hgz⟩) (by exact_mod_cast hcast.symm)
    have hforder_ne : analyticOrderNatAt f z ≠ 0 := by rw [horder z hz]; exact hgorder_ne
    have hforder_ne' : analyticOrderAt f z ≠ 0 := by
      intro h0
      apply hforder_ne
      have hfcast := Nat.cast_analyticOrderNatAt (hf_fin z hz)
      rw [h0] at hfcast
      exact_mod_cast hfcast
    have hfz0 : f z = 0 := (analyticOrderAt_ne_zero.mp hforder_ne').2
    obtain ⟨L, hLne, hLtendsto⟩ := exists_tendsto_div_nhdsWithin_ne_of_analyticOrderNatAt_eq
      (hf z hz) (hg z hz) (hf_fin z hz) (hg_fin z hz) (horder z hz)
    have hg_ev_ne : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 := by
      rcases (hg z hz).eventually_eq_zero_or_eventually_ne_zero with h0 | hne
      · exact absurd (analyticOrderAt_eq_top.mpr h0) (hg_fin z hz)
      · exact hne
    have huz : u z = L := by
      have hu_eq : u z = limUnder (𝓝[≠] z) (fun w => f w / g w) := by
        rw [hu_def]; exact if_neg (by simp [hgz])
      rw [hu_eq]; exact hLtendsto.limUnder_eq
    exact ⟨hfz0, L, hLne, hLtendsto, huz, hg_ev_ne⟩
  refine ⟨u, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · -- `HolomorphicOn u`
    by_cases hgz : g z = 0
    · obtain ⟨hfz0, L, hLne, hLtendsto, huz, hg_ev_ne⟩ := hg_zero_imp z hz hgz
      have hg_ev_ne' : ∀ᶠ w in 𝓝 z, w ≠ z → g w ≠ 0 := eventually_nhdsWithin_iff.mp hg_ev_ne
      have hu_eq_update : u =ᶠ[𝓝 z] Function.update (fun w => f w / g w) z L := by
        filter_upwards [hg_ev_ne'] with w hw
        by_cases hwz : w = z
        · subst hwz; rw [huz, Function.update_self]
        · rw [hu_eq_div w (hw hwz), Function.update_of_ne hwz]
      have hu_cont : ContinuousAt u z :=
        (continuousAt_update_same.mpr hLtendsto).congr hu_eq_update.symm
      have hu_diff : ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ u w := by
        have h𝔻nhds : 𝔻 ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
        filter_upwards [hg_ev_ne, mem_nhdsWithin_of_mem_nhds h𝔻nhds] with w hgw hwD
        have hu_eq_near : u =ᶠ[𝓝 w] (fun v => f v / g v) := by
          filter_upwards [(hg w hwD).continuousAt.eventually_ne hgw] with v hv
          exact hu_eq_div v hv
        exact ((hf w hwD).div (hg w hwD) hgw).differentiableAt.congr_of_eventuallyEq hu_eq_near
      exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hu_diff hu_cont
    · have hu_eq_near : u =ᶠ[𝓝 z] (fun w => f w / g w) := by
        filter_upwards [(hg z hz).continuousAt.eventually_ne hgz] with w hw
        exact hu_eq_div w hw
      exact ((hf z hz).div (hg z hz) hgz).congr hu_eq_near.symm
  · -- `∀ z ∈ 𝔻, u z ≠ 0`
    by_cases hgz : g z = 0
    · obtain ⟨-, L, hLne, -, huz, -⟩ := hg_zero_imp z hz hgz
      rw [huz]; exact hLne
    · rw [hu_eq_div z hgz]
      have hgorder0 : analyticOrderAt g z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hgz)
      have hforder0 : analyticOrderAt f z = 0 := by
        have hgcast : (analyticOrderNatAt g z : ℕ∞) = 0 := by
          rw [Nat.cast_analyticOrderNatAt (hg_fin z hz), hgorder0]
        have hgnat0 : analyticOrderNatAt g z = 0 := by exact_mod_cast hgcast
        have hfnat0 : analyticOrderNatAt f z = 0 := by rw [horder z hz]; exact hgnat0
        have hfcast : (analyticOrderNatAt f z : ℕ∞) = analyticOrderAt f z :=
          Nat.cast_analyticOrderNatAt (hf_fin z hz)
        rw [hfnat0] at hfcast
        exact hfcast.symm
      have hfz_ne : f z ≠ 0 := by
        rcases analyticOrderAt_eq_zero.mp hforder0 with h | h
        · exact absurd (hf z hz) h
        · exact h
      exact div_ne_zero hfz_ne hgz
  · -- `∀ z ∈ 𝔻, f z = g z * u z`
    by_cases hgz : g z = 0
    · obtain ⟨hfz0, -, -, -, -, -⟩ := hg_zero_imp z hz hgz
      rw [hfz0, hgz, zero_mul]
    · rw [hu_eq_div z hgz, mul_div_cancel₀ _ hgz]

/-- **Proposition `prop:associate` (Factorization up to units in `𝒪(𝔻)`).** Every `f ∈ 𝒪(𝔻)`
can be written `f = g * u` with `g ∈ ℛ` and `u ∈ 𝒪(𝔻)ˣ` (holomorphic and nowhere-vanishing). -/
theorem exists_hasGaussianIntCoeffs_mul_nowhereVanishing (f : ℂ → ℂ) (hf : HolomorphicOn f) :
    ∃ g u : ℂ → ℂ, HolomorphicOn g ∧ HasGaussianIntCoeffs g ∧
      HolomorphicOn u ∧ (∀ z ∈ 𝔻, u z ≠ 0) ∧ ∀ z ∈ 𝔻, f z = g z * u z := by
  by_cases hfzero : ∀ z ∈ 𝔻, f z = 0
  · -- `f ≡ 0` on `𝔻`: take `g = 0`, `u = 1`.
    exact ⟨fun _ => 0, fun _ => 1, fun _ _ => analyticAt_const, hasGaussianIntCoeffs_zero,
      fun _ _ => analyticAt_const, fun _ _ => one_ne_zero,
      fun z hz => by rw [hfzero z hz]; ring⟩
  · push Not at hfzero
    by_cases hfnv : ∀ z ∈ 𝔻, f z ≠ 0
    · -- `f` is already nowhere-vanishing: take `g = 1`, `u = f`.
      exact ⟨fun _ => 1, f, fun _ _ => analyticAt_const, hasGaussianIntCoeffs_one, hf, hfnv,
        fun z _ => by ring⟩
    · -- `f` has at least one zero: apply Theorem `prop:Zi` to its zero divisor.
      push Not at hfnv
      obtain ⟨z0, hz0D, hfz0⟩ := hfnv
      have hfne : ∃ z ∈ 𝔻, f z ≠ 0 := hfzero
      set Df := zeroDivisorOfHolomorphic f hf hfne with hDf_def
      have hIsZDf : IsZeroDivisorOf Df f := isZeroDivisorOf_zeroDivisorOfHolomorphic f hf hfne
      obtain ⟨g, hg_holo, hg_zd, hg_int⟩ :=
        exists_holomorphic_gaussianInt_coeffs_of_effectiveDivisor Df
      have horder : ∀ z ∈ 𝔻, analyticOrderNatAt f z = analyticOrderNatAt g z := by
        intro z hz; rw [← hIsZDf z hz, ← hg_zd z hz]
      have hsomepos : ∃ z ∈ 𝔻, analyticOrderNatAt f z ≠ 0 := by
        refine ⟨z0, hz0D, fun h0 => ?_⟩
        have hcast : (analyticOrderNatAt f z0 : ℕ∞) = 0 := by exact_mod_cast h0
        rw [Nat.cast_analyticOrderNatAt (analyticOrderAt_ne_top_of_ne_zero_somewhere hf hfne hz0D)]
          at hcast
        exact (analyticOrderAt_ne_zero.mpr ⟨hf z0 hz0D, hfz0⟩) hcast
      obtain ⟨u, hu_holo, hu_nv, hu_eq⟩ :=
        exists_holomorphicOn_nowhereVanishing_mul_eq_of_analyticOrderNatAt_eq
          hf hg_holo horder hsomepos
      exact ⟨g, u, hg_holo, hg_int, hu_holo, hu_nv, hu_eq⟩

/-! ## Corollary `cor:ideals`: every ideal of `𝒪(𝔻)` is generated by its `ℛ`-elements -/

/-- An ideal of `𝒪(𝔻)`: a set of holomorphic functions on `𝔻`, closed under addition, absorbing
multiplication by any element of `𝒪(𝔻)`, and depending only on behavior on `𝔻` (since elements
of `𝒪(𝔻)` are functions on `𝔻`, represented here by arbitrary total extensions to `ℂ`). -/
structure IsIdealOD (I : Set (ℂ → ℂ)) : Prop where
  subset_holomorphic : ∀ f ∈ I, HolomorphicOn f
  add_mem : ∀ f ∈ I, ∀ g ∈ I, (fun z => f z + g z) ∈ I
  smul_mem : ∀ h, HolomorphicOn h → ∀ f ∈ I, (fun z => h z * f z) ∈ I
  congr_on_𝔻 : ∀ f ∈ I, ∀ f', HolomorphicOn f' → Set.EqOn f f' 𝔻 → f' ∈ I

/-- **Corollary `cor:ideals`.** Every ideal `I` of `𝒪(𝔻)` satisfies `I = (I ∩ ℛ) · 𝒪(𝔻)`: an
`f ∈ 𝒪(𝔻)` lies in `I` if and only if it factors as `f = g * u` with `g ∈ I` a `ℛ`-element and
`u ∈ 𝒪(𝔻)`. -/
theorem cor_ideals {I : Set (ℂ → ℂ)} (hI : IsIdealOD I) {f : ℂ → ℂ} (hf : HolomorphicOn f) :
    f ∈ I ↔ ∃ g u : ℂ → ℂ, g ∈ I ∧ HasGaussianIntCoeffs g ∧ HolomorphicOn u ∧
      ∀ z ∈ 𝔻, f z = g z * u z := by
  constructor
  · intro hfI
    obtain ⟨g, u, hg_holo, hg_int, hu_holo, hu_nv, hu_eq⟩ :=
      exists_hasGaussianIntCoeffs_mul_nowhereVanishing f hf
    have hu_inv_holo : HolomorphicOn (fun z => (u z)⁻¹) :=
      fun z hz => (hu_holo z hz).inv (hu_nv z hz)
    have hg_mem : (fun z => (u z)⁻¹ * f z) ∈ I := hI.smul_mem _ hu_inv_holo f hfI
    have hg_eq : Set.EqOn (fun z => (u z)⁻¹ * f z) g 𝔻 := by
      intro z hz
      change (u z)⁻¹ * f z = g z
      rw [hu_eq z hz, mul_comm (g z) (u z), ← mul_assoc, inv_mul_cancel₀ (hu_nv z hz), one_mul]
    have hgI : g ∈ I := hI.congr_on_𝔻 _ hg_mem g hg_holo hg_eq
    exact ⟨g, u, hgI, hg_int, hu_holo, hu_eq⟩
  · rintro ⟨g, u, hgI, -, hu_holo, hfeq⟩
    have hprod_mem : (fun z => u z * g z) ∈ I := hI.smul_mem u hu_holo g hgI
    refine hI.congr_on_𝔻 _ hprod_mem f hf (fun z hz => ?_)
    rw [hfeq z hz, mul_comm]

end Weierstrass
