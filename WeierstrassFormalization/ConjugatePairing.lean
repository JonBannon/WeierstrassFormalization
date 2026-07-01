/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.WeierstrassProduct
import WeierstrassFormalization.ComplexConjugation

/-!
# Conjugate-paired Weierstrass products

Scaffolding for the sufficiency direction of Theorem `thm:main` (`MainTheorem.lean`): given a
conjugation-invariant effective divisor `D`, build a holomorphic function on `𝔻` with zero
divisor `D` and *integer* Taylor coefficients, by grouping the zeros of `D` into "slots" of the
`WeierstrassProduct.lean` construction — a single slot for each real zero, and a slot shared by
each conjugate pair of nonreal zeros — indexed so that slot `j` uses factors of order `j` at
positions `2j` and `2j+1`. Because both factors of a slot share the same order, the correction
constants can be linked (`c̄` for the conjugate-pair companion) so that the slot's *combined*
contribution to the Taylor coefficients is always real, keeping a real-coefficient invariant
throughout the induction and allowing rounding to the nearest *integer* instead of nearest
Gaussian integer.
-/

namespace Weierstrass

open Complex

/-! ## Enumerating a conjugate-invariant divisor into slots -/

/-- The "upper half" of `D`: the same multiplicities as `D`, but restricted to points with
nonnegative imaginary part (and excluding the origin). Since `D` is conjugation-invariant, `D`'s
support is recovered from this divisor's support together with its complex conjugate. -/
private noncomputable def halfDivisor (D : EffectiveDivisor) : EffectiveDivisor where
  mult z := if 0 ≤ z.im ∧ z ≠ 0 then D.mult z else 0
  mult_eq_zero_of_not_mem_𝔻 z hz := by
    split_ifs with h
    · exact D.mult_eq_zero_of_not_mem_𝔻 z hz
    · rfl
  finite_inter_compact K hK hKcpt := by
    refine Set.Finite.subset (D.finite_inter_compact K hK hKcpt) ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz ⊢
    refine ⟨hz.1, ?_⟩
    intro hcontra
    apply hz.2
    simp [hcontra]

private theorem halfDivisor_mult_eq {D : EffectiveDivisor} {z : ℂ} (hzim : 0 ≤ z.im)
    (hz0 : z ≠ 0) : (halfDivisor D).mult z = D.mult z := by simp [halfDivisor, hzim, hz0]

private theorem mem_support_halfDivisor {D : EffectiveDivisor} {z : ℂ} :
    z ∈ (halfDivisor D).support → 0 ≤ z.im := by
  intro hz
  by_contra hcon
  rw [not_le] at hcon
  simp only [EffectiveDivisor.support, Set.mem_setOf_eq, halfDivisor] at hz
  rw [if_neg (fun h => absurd h.1 (not_le.mpr hcon))] at hz
  exact hz rfl

/-- Given `p` enumerating the support of `halfDivisor D` (one point per real zero or per
conjugate-pair representative, with multiplicity), the full paired enumeration of `D`'s support:
even positions repeat `p`, odd positions carry the real/conjugate "companion" of the preceding
even position (a fixed dummy point `2 ∉ 𝔻` for a real `p`-value, since no companion is needed). -/
noncomputable def pairedEnum (p : ℕ → ℂ) : ℕ → ℂ :=
  fun k => if k % 2 = 0 then p (k / 2)
    else if (p (k / 2)).im = 0 then 2 else (starRingEnd ℂ) (p (k / 2))

theorem pairedEnum_even (p : ℕ → ℂ) (j : ℕ) : pairedEnum p (2 * j) = p j := by
  simp [pairedEnum, Nat.mul_div_cancel_left j (by norm_num : 0 < 2)]

theorem pairedEnum_odd (p : ℕ → ℂ) (j : ℕ) :
    pairedEnum p (2 * j + 1) = if (p j).im = 0 then 2 else (starRingEnd ℂ) (p j) := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [pairedEnum, h1, h2]

theorem pairedEnum_ne_zero (p : ℕ → ℂ) (hp0 : ∀ k, p k ≠ 0) (k : ℕ) : pairedEnum p k ≠ 0 := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, ← two_mul, pairedEnum_even]; exact hp0 j
  · rw [hj, pairedEnum_odd]
    split_ifs with h
    · norm_num
    · intro hcontra
      exact hp0 j (by rw [← Complex.conj_conj (p j), hcontra, map_zero])

/-- **Paired enumeration of a conjugate-invariant divisor.** Every effective divisor `D`
invariant under complex conjugation can be enumerated in slots of two (one point per real zero,
two conjugate points per nonreal zero), the odd positions being the real/conjugate companions of
the even positions (`pairedEnum_even`, `pairedEnum_odd`), realizing `D`'s multiplicities on `𝔻`
and with the same escape-to-the-boundary property as `exists_enum_of_effectiveDivisor`. -/
theorem exists_pairedEnum_of_conjInvariant (D : EffectiveDivisor) (hD : D.ConjInvariant) :
    ∃ a : ℕ → ℂ, (∀ k, a k ≠ 0) ∧
      (∀ z ∈ 𝔻, z ≠ 0 → D.mult z = {k | a k = z}.ncard) ∧
      (∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite) ∧
      (∀ j, a (2 * j + 1) = if (a (2 * j)).im = 0 then 2 else (starRingEnd ℂ) (a (2 * j))) := by
  obtain ⟨p, hp0, hpmult, hpesc, hpaux⟩ := exists_enum_of_effectiveDivisor (halfDivisor D)
  have hp_im : ∀ k, 0 ≤ (p k).im := by
    intro k
    rcases hpaux k with h2 | hmem
    · simp [h2]
    · exact mem_support_halfDivisor hmem
  refine ⟨pairedEnum p, pairedEnum_ne_zero p hp0, ?_, ?_, fun j => by
    rw [pairedEnum_even, pairedEnum_odd]⟩
  · -- multiplicity, on `𝔻 \ {0}`
    intro z hz hz0
    have hpinj2 : Function.Injective (fun j : ℕ => 2 * j) := fun j1 j2 h => by
      simp only at h; omega
    have hpinj2' : Function.Injective (fun j : ℕ => 2 * j + 1) := fun j1 j2 h => by
      simp only at h; omega
    by_cases hzim : 0 ≤ z.im
    · -- `z` itself is a `halfDivisor`-point.
      rw [← halfDivisor_mult_eq hzim hz0, hpmult z hz0]
      have hset : {k | pairedEnum p k = z} = (fun j => 2 * j) '' {j | p j = z} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro hk
          rcases Nat.even_or_odd k with ⟨j, hj0⟩ | ⟨j, hj⟩
          · have hj : k = 2 * j := by omega
            rw [hj, pairedEnum_even] at hk
            exact ⟨j, hk, hj.symm⟩
          · exfalso
            rw [hj, pairedEnum_odd] at hk
            split_ifs at hk with him
            · rw [← hk] at hz
              rw [mem_𝔻_iff] at hz
              norm_num at hz
            · have himeq : -(p j).im = z.im := by
                have := congrArg Complex.im hk
                rwa [Complex.conj_im] at this
              have h1 := hp_im j
              exact him (by linarith)
        · rintro ⟨j, hj, rfl⟩
          rw [pairedEnum_even]; exact hj
      rw [hset, Set.ncard_image_of_injective _ hpinj2]
    · -- `z ∉ halfDivisor`'s domain: use conjugate invariance, `conj z` is.
      rw [not_le] at hzim
      have hzconj_im : 0 ≤ ((starRingEnd ℂ) z).im := by rw [Complex.conj_im]; linarith
      have hzconj_ne : (starRingEnd ℂ) z ≠ 0 := fun h =>
        hz0 (by rw [← Complex.conj_conj z, h, map_zero])
      rw [← hD z, ← halfDivisor_mult_eq hzconj_im hzconj_ne, hpmult _ hzconj_ne]
      have hset : {k | pairedEnum p k = z}
          = (fun j => 2 * j + 1) '' {j | p j = (starRingEnd ℂ) z} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_image]
        constructor
        · intro hk
          rcases Nat.even_or_odd k with ⟨j, hj0⟩ | ⟨j, hj⟩
          · exfalso
            have hj : k = 2 * j := by omega
            rw [hj, pairedEnum_even] at hk
            have := hp_im j
            rw [hk] at this
            linarith
          · rw [hj, pairedEnum_odd] at hk
            split_ifs at hk with him
            · exfalso; rw [← hk] at hzim; norm_num at hzim
            · exact ⟨j, by rw [← hk, Complex.conj_conj], hj.symm⟩
        · rintro ⟨j, hj, rfl⟩
          rw [pairedEnum_odd]
          have hjim : (p j).im ≠ 0 := by
            rw [hj, Complex.conj_im]; intro h; apply absurd hzim; linarith
          rw [if_neg hjim, hj, Complex.conj_conj]
      rw [hset, Set.ncard_image_of_injective _ hpinj2']
  · -- escape property
    intro s hs
    have hpfin := hpesc s hs
    have hsub : {k | ‖pairedEnum p k‖ < s} ⊆
        (fun j => 2 * j) '' {j | ‖p j‖ < s} ∪ (fun j => 2 * j + 1) '' {j | ‖p j‖ < s} := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      rcases Nat.even_or_odd k with ⟨j, hj0⟩ | ⟨j, hj⟩
      · have hj : k = 2 * j := by omega
        rw [hj, pairedEnum_even] at hk
        exact Or.inl ⟨j, hk, hj.symm⟩
      · rw [hj, pairedEnum_odd] at hk
        split_ifs at hk with him
        · exfalso; norm_num at hk; linarith
        · refine Or.inr ⟨j, ?_, hj.symm⟩
          rwa [Complex.norm_conj] at hk
    exact Set.Finite.subset
      ((hpfin.image (fun j => 2 * j)).union (hpfin.image (fun j => 2 * j + 1))) hsub

/-! ## Real-coefficient invariant: conjugating a slot factor -/

/-- Conjugating `E n c w` conjugates both parameters: `E`'s defining formula involves only
`+, -, *, /, exp` applied to `w`, `c`, and *rational* numeric constants, all of which commute
with conjugation. -/
theorem E_conj (n : ℕ) (c w : ℂ) :
    (starRingEnd ℂ) (E n c w) = E n ((starRingEnd ℂ) c) ((starRingEnd ℂ) w) := by
  unfold E
  have hn1 : (starRingEnd ℂ) ((n : ℂ) + 1) = (n : ℂ) + 1 := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.conj_natCast]
  have hsum : (starRingEnd ℂ) (∑ k ∈ Finset.Icc 1 n, w ^ k / (k : ℂ))
      = ∑ k ∈ Finset.Icc 1 n, (starRingEnd ℂ) w ^ k / (k : ℂ) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_div₀, map_pow, Complex.conj_natCast]
  rw [map_mul, map_sub, map_one, ← Complex.exp_conj, map_add, hsum, map_div₀, map_mul,
    map_pow, hn1]

/-- A function is *conjugate-symmetric* if `conj (h (conj z)) = h z` for all `z`; equivalently
(`taylorCoeff_real_of_conjSymmetric`), if `h` is analytic at `0`, all its Taylor coefficients
there are real. -/
def ConjSymmetric (h : ℂ → ℂ) : Prop := ∀ z, (starRingEnd ℂ) (h ((starRingEnd ℂ) z)) = h z

theorem ConjSymmetric.mul {h₁ h₂ : ℂ → ℂ} (h1 : ConjSymmetric h₁) (h2 : ConjSymmetric h₂) :
    ConjSymmetric (fun z => h₁ z * h₂ z) := fun z => by
  simp only [map_mul, h1 z, h2 z]

theorem conjSymmetric_one : ConjSymmetric (fun _ : ℂ => (1 : ℂ)) := fun _ => by simp

/-- A real point with a real correction constant gives a conjugate-symmetric factor. -/
theorem conjSymmetric_E_real {n : ℕ} {c a : ℂ} (hc : (starRingEnd ℂ) c = c)
    (ha : (starRingEnd ℂ) a = a) : ConjSymmetric (fun z => E n c (z / a)) := fun z => by
  rw [E_conj, hc, map_div₀, ha, Complex.conj_conj]

/-- A conjugate pair of points, with conjugate correction constants, gives a
conjugate-symmetric combined factor. -/
theorem conjSymmetric_E_pair (n : ℕ) (c a : ℂ) :
    ConjSymmetric (fun z => E n c (z / a) * E n ((starRingEnd ℂ) c) (z / (starRingEnd ℂ) a)) :=
  fun z => by
    rw [map_mul, E_conj, E_conj, map_div₀, map_div₀, Complex.conj_conj, Complex.conj_conj,
      Complex.conj_conj]
    ring

/-- A conjugate-symmetric function analytic at `0` has real Taylor coefficients there. -/
theorem taylorCoeff_real_of_conjSymmetric {h : ℂ → ℂ} (hh : AnalyticAt ℂ h 0)
    (hsymm : ConjSymmetric h) (n : ℕ) :
    (starRingEnd ℂ) (taylorCoeff h n) = taylorCoeff h n := by
  have heq := taylorCoeff_conj_comp_conj hh n
  rw [funext hsymm] at heq
  exact heq.symm

/-! ## Rounding to the nearest integer -/

/-- A nearest integer to `x : ℝ`, as a complex number. -/
noncomputable def nearestIntC (x : ℝ) : ℂ := ((round x : ℤ) : ℂ)

theorem norm_sub_nearestIntC_le (x : ℝ) : ‖(x : ℂ) - nearestIntC x‖ ≤ 1 / 2 := by
  unfold nearestIntC
  rw [show (x : ℂ) - ((round x : ℤ) : ℂ) = ((x - (round x : ℤ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real]
  exact abs_sub_round x

/-! ## The paired coefficient-forcing induction -/

/-- Unconditional version of `exists_c_taylorCoeff_mul_E_succ_eq`: see the analogous
`WeierstrassProduct.lean` construction for why this "unconditional" form is needed to build the
correction constants by structural recursion before their defining hypotheses are verified. -/
private theorem exists_c_taylorCoeff_mul_E_succ_eq'' (h : ℂ → ℂ) (a : ℂ) (n : ℕ) (target : ℂ) :
    ∃ c : ℂ, AnalyticAt ℂ h 0 → h 0 = 1 → a ≠ 0 →
      taylorCoeff (fun z => h z * E n c (z / a)) (n + 1) = target := by
  by_cases hcond : AnalyticAt ℂ h 0 ∧ h 0 = 1 ∧ a ≠ 0
  · obtain ⟨hh, hh0, ha⟩ := hcond
    obtain ⟨c, hc⟩ := exists_c_taylorCoeff_mul_E_succ_eq hh hh0 ha n target
    exact ⟨c, fun _ _ _ => hc⟩
  · exact ⟨0, fun hh hh0 ha => absurd ⟨hh, hh0, ha⟩ hcond⟩

/-- **Real-zero slot.** The correction constant forcing the degree-`(n+1)` Taylor coefficient of
`h * E n c (·/a)` to the nearest integer to `(taylorCoeff h (n+1)).re`. When `taylorCoeff h (n+1)`
is actually real (as it will be, by the conjugate-symmetry invariant) and `a` is real, this
target is the nearest integer to the true pre-existing value, and `c` comes out real (a
consequence, not an extra constraint: see `chooseCReal_conj`). -/
private noncomputable def chooseCReal (h : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  Classical.choose (exists_c_taylorCoeff_mul_E_succ_eq'' h a n
    (nearestIntC (taylorCoeff h (n + 1)).re))

private theorem chooseCReal_spec (h : ℂ → ℂ) (a : ℂ) (n : ℕ)
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1) (ha : a ≠ 0) :
    taylorCoeff (fun z => h z * E n (chooseCReal h a n) (z / a)) (n + 1)
      = nearestIntC (taylorCoeff h (n + 1)).re :=
  Classical.choose_spec (exists_c_taylorCoeff_mul_E_succ_eq'' h a n
    (nearestIntC (taylorCoeff h (n + 1)).re)) hh hh0 ha

/-- **Conjugate-pair slot.** The correction constant `c` for the first factor `E n c (·/a)` of a
conjugate-pair slot (the second factor uses `conj c` at `conj a`), chosen as the minimal-norm
solution forcing the *combined* degree-`(n+1)` coefficient to the nearest integer to
`(taylorCoeff h (n+1)).re` (Theorem `thm:main`'s proof, "choose `c_n` to be the preimage of
minimal modulus"). -/
private noncomputable def chooseCPair (h : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  1 + (((round (taylorCoeff h (n + 1)).re : ℝ) - (taylorCoeff h (n + 1)).re : ℝ) : ℂ)
    * ((n : ℂ) + 1) / 2 * a ^ (n + 1)

private theorem chooseCPair_spec (h : ℂ → ℂ) (a : ℂ) (n : ℕ)
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1) (ha : a ≠ 0)
    (hreal : (starRingEnd ℂ) (taylorCoeff h (n + 1)) = taylorCoeff h (n + 1)) :
    taylorCoeff (fun z => h z * E n (chooseCPair h a n) (z / a)
        * E n ((starRingEnd ℂ) (chooseCPair h a n)) (z / (starRingEnd ℂ) a)) (n + 1)
      = nearestIntC (taylorCoeff h (n + 1)).re := by
  set v : ℂ := taylorCoeff h (n + 1) with hv_def
  set c₁ : ℂ := chooseCPair h a n with hc₁_def
  set Δ : ℝ := (round v.re : ℝ) - v.re with hΔ_def
  have hvre : v = (v.re : ℂ) := by
    have hre := Complex.re_add_im v
    have him0 : v.im = 0 := by
      have himeq := congrArg Complex.im hreal
      rw [Complex.conj_im] at himeq
      linarith
    rw [← hre, him0]; simp
  have hapow : a ^ (n + 1) ≠ 0 := pow_ne_zero _ ha
  have hconj_a_ne : (starRingEnd ℂ) a ≠ 0 := fun hh0' =>
    ha (by rw [← Complex.conj_conj a, hh0', map_zero])
  have hn1' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hc₁sub : c₁ - 1 = (Δ : ℂ) * ((n : ℂ) + 1) / 2 * a ^ (n + 1) := by
    rw [hc₁_def]; unfold chooseCPair; ring
  have hstep1 : taylorCoeff (fun z => h z * E n c₁ (z / a)) (n + 1) = v + (Δ / 2 : ℂ) := by
    rw [taylorCoeff_mul_E_succ hh hh0 ha n, hc₁sub]
    have hcancel : (Δ : ℂ) * ((n : ℂ) + 1) / 2 * a ^ (n + 1) / (((n : ℂ) + 1) * a ^ (n + 1))
        = (Δ : ℂ) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)]
      field_simp
    rw [hcancel]
  have hh'analytic : AnalyticAt ℂ (fun z => h z * E n c₁ (z / a)) 0 := by
    have h1 : AnalyticAt ℂ (fun z : ℂ => z / a) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (E n c₁) (0 / a) := by rw [zero_div]; unfold E; fun_prop
    exact hh.mul (AnalyticAt.comp (f := fun z : ℂ => z / a) (x := 0) h2 h1)
  have hh'0 : (fun z => h z * E n c₁ (z / a)) 0 = 1 := by simp [hh0, E_zero]
  have hstep2 := taylorCoeff_mul_E_succ (h := fun z => h z * E n c₁ (z / a))
    (c := (starRingEnd ℂ) c₁) hh'analytic hh'0 hconj_a_ne n
  rw [hstep1] at hstep2
  have hconjcoef : (starRingEnd ℂ) ((Δ : ℂ) * ((n : ℂ) + 1) / 2) = (Δ : ℂ) * ((n : ℂ) + 1) / 2 := by
    rw [map_div₀, map_mul, Complex.conj_ofReal, map_add, Complex.conj_natCast, map_one,
      show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.conj_natCast]
  have hc₂sub : (starRingEnd ℂ) c₁ - 1
      = (Δ : ℂ) * ((n : ℂ) + 1) / 2 * ((starRingEnd ℂ) a) ^ (n + 1) := by
    have hc₁eq : c₁ = 1 + (Δ : ℂ) * ((n : ℂ) + 1) / 2 * a ^ (n + 1) := by rw [← hc₁sub]; ring
    rw [hc₁eq, map_add, map_one, map_mul, map_pow, hconjcoef]
    ring
  have hstep2' : taylorCoeff (fun z => h z * E n c₁ (z / a) * E n ((starRingEnd ℂ) c₁)
      (z / (starRingEnd ℂ) a)) (n + 1) = v + (Δ / 2 : ℂ) + (Δ / 2 : ℂ) := by
    rw [hstep2, hc₂sub]
    have hcancel2 : (Δ : ℂ) * ((n : ℂ) + 1) / 2 * ((starRingEnd ℂ) a) ^ (n + 1)
        / (((n : ℂ) + 1) * (starRingEnd ℂ) a ^ (n + 1)) = (Δ : ℂ) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)]
      field_simp
    rw [hcancel2]
  rw [hstep2']
  have hfinal : v + (Δ / 2 : ℂ) + (Δ / 2 : ℂ) = ((round v.re : ℤ) : ℂ) := by
    have hΔc : (Δ : ℂ) = ((round v.re : ℤ) : ℂ) - v := by
      rw [hΔ_def]; push_cast; rw [← hvre]
    rw [hΔc]; ring
  rw [hfinal]; rfl

end Weierstrass
