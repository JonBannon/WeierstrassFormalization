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

end Weierstrass
