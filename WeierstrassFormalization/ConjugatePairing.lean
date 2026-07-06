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

/-- **Real-zero slot.** The correction constant forcing the degree-`(n+1)` Taylor coefficient of
`h * E n c (·/a)` to the nearest integer to `(taylorCoeff h (n+1)).re` (the explicit affine
formula from `exists_c_taylorCoeff_mul_E_succ_eq`, given directly rather than by
`Classical.choose` so that its realness, given real inputs, is immediate — see
`chooseCReal_real`). -/
noncomputable def chooseCReal (h : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  1 + (nearestIntC (taylorCoeff h (n + 1)).re - taylorCoeff h (n + 1))
    * (((n : ℂ) + 1) * a ^ (n + 1))

private theorem chooseCReal_spec (h : ℂ → ℂ) (a : ℂ) (n : ℕ)
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1) (ha : a ≠ 0) :
    taylorCoeff (fun z => h z * E n (chooseCReal h a n) (z / a)) (n + 1)
      = nearestIntC (taylorCoeff h (n + 1)).re := by
  rw [taylorCoeff_mul_E_succ hh hh0 ha n]
  unfold chooseCReal
  have hn1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hapow : a ^ (n + 1) ≠ 0 := pow_ne_zero _ ha
  field_simp
  ring

private theorem chooseCReal_real {h : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hreal : (starRingEnd ℂ) (taylorCoeff h (n + 1)) = taylorCoeff h (n + 1))
    (ha : (starRingEnd ℂ) a = a) :
    (starRingEnd ℂ) (chooseCReal h a n) = chooseCReal h a n := by
  unfold chooseCReal
  rw [map_add, map_one, map_mul, map_sub, hreal, map_mul, map_add, map_one, map_pow,
    Complex.conj_natCast, ha]
  congr 2
  unfold nearestIntC
  rw [show ((round (taylorCoeff h (n + 1)).re : ℤ) : ℂ)
      = (((round (taylorCoeff h (n + 1)).re : ℤ) : ℝ) : ℂ) by push_cast; ring,
    Complex.conj_ofReal]

/-- **Conjugate-pair slot.** The correction constant `c` for the first factor `E n c (·/a)` of a
conjugate-pair slot (the second factor uses `conj c` at `conj a`), chosen as the minimal-norm
solution forcing the *combined* degree-`(n+1)` coefficient to the nearest integer to
`(taylorCoeff h (n+1)).re` (Theorem `thm:main`'s proof, "choose `c_n` to be the preimage of
minimal modulus"). -/
noncomputable def chooseCPair (h : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
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

/-! ## The paired partial products -/

/-- The `N`-th partial product of the paired construction, with the `k`-th factor at order
`k / 2` (so factors `2j` and `2j + 1` share order `j`, matching a single slot). -/
noncomputable def pairProduct (a c : ℕ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => ∏ k ∈ Finset.range N, E (k / 2) (c k) (z / a k)

theorem pairProduct_zero (a c : ℕ → ℂ) : pairProduct a c 0 = fun _ => 1 := by
  funext z; simp [pairProduct]

theorem pairProduct_succ (a c : ℕ → ℂ) (N : ℕ) :
    pairProduct a c (N + 1) = fun z => pairProduct a c N z * E (N / 2) (c N) (z / a N) := by
  funext z; simp [pairProduct, Finset.prod_range_succ]

theorem pairProduct_taylorCoeff_shrink (a c : ℕ → ℂ) (N m : ℕ) (hN : m ≤ N / 2) :
    taylorCoeff (pairProduct a c (N + 1)) m = taylorCoeff (pairProduct a c N) m := by
  have hanalytic : AnalyticAt ℂ (pairProduct a c N) 0 := by
    have : Differentiable ℂ (pairProduct a c N) := by unfold pairProduct E; fun_prop
    exact this.analyticAt 0
  rw [pairProduct_succ]
  exact taylorCoeff_mul_E_eq_of_le hanalytic hN

/-- The structural recursion building the paired partial products slot by slot: at slot `j`, if
`a (2j)` is real, force the degree-`(j+1)` coefficient with a single real correction constant
(the companion factor at `a (2j+1) = 2` uses the trivial `c = 1`); otherwise force it with a
conjugate-linked pair of correction constants at the conjugate pair `a (2j), a (2j+1)`. -/
private noncomputable def auxQ (a : ℕ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 1
  | (j + 1) => fun z =>
      if (a (2 * j)).im = 0 then
        auxQ a j z * E j (chooseCReal (auxQ a j) (a (2 * j)) j) (z / a (2 * j))
          * E j 1 (z / a (2 * j + 1))
      else
        auxQ a j z * E j (chooseCPair (auxQ a j) (a (2 * j)) j) (z / a (2 * j))
          * E j ((starRingEnd ℂ) (chooseCPair (auxQ a j) (a (2 * j)) j)) (z / a (2 * j + 1))

private theorem auxQ_invariant (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0)
    (ha_pair : ∀ j, a (2 * j + 1) = if (a (2 * j)).im = 0 then 2 else (starRingEnd ℂ) (a (2 * j)))
    (j : ℕ) :
    AnalyticAt ℂ (auxQ a j) 0 ∧ auxQ a j 0 = 1 ∧ ConjSymmetric (auxQ a j) := by
  induction j with
  | zero => exact ⟨by unfold auxQ; fun_prop, rfl, conjSymmetric_one⟩
  | succ j ih =>
      obtain ⟨hAnalytic, hOne, hSymm⟩ := ih
      have hfactor_analytic : ∀ c a' : ℂ, a' ≠ 0 → AnalyticAt ℂ (fun z => E j c (z / a')) 0 := by
        intro c a' ha'
        have h1 : AnalyticAt ℂ (fun z : ℂ => z / a') 0 := by fun_prop
        have h2 : AnalyticAt ℂ (E j c) (0 / a') := by rw [zero_div]; unfold E; fun_prop
        exact AnalyticAt.comp (f := fun z : ℂ => z / a') (x := 0) h2 h1
      by_cases him : (a (2 * j)).im = 0
      · -- real slot: `a (2j)` real, `a (2j+1) = 2`.
        have hodd : a (2 * j + 1) = 2 := by rw [ha_pair j, if_pos him]
        have hareal : (starRingEnd ℂ) (a (2 * j)) = a (2 * j) := Complex.conj_eq_iff_im.mpr him
        set c := chooseCReal (auxQ a j) (a (2 * j)) j with hc_def
        have hcreal : (starRingEnd ℂ) c = c :=
          chooseCReal_real (taylorCoeff_real_of_conjSymmetric hAnalytic hSymm (j + 1)) hareal
        have haux_eq : auxQ a (j + 1)
            = fun z => auxQ a j z * E j c (z / a (2 * j)) * E j 1 (z / a (2 * j + 1)) := by
          funext z; simp only [auxQ, if_pos him, ← hc_def]
        rw [haux_eq]
        refine ⟨(hAnalytic.mul (hfactor_analytic c (a (2 * j)) (ha0 (2 * j)))).mul
          (hfactor_analytic 1 (a (2 * j + 1)) (ha0 (2 * j + 1))), ?_, ?_⟩
        · simp [hOne, E_zero]
        · exact (hSymm.mul (conjSymmetric_E_real hcreal hareal)).mul
            (hodd ▸ conjSymmetric_E_real (map_one (starRingEnd ℂ)) (map_ofNat (starRingEnd ℂ) 2))
      · -- conjugate-pair slot: `a (2j+1) = conj (a (2j))`.
        have hodd : a (2 * j + 1) = (starRingEnd ℂ) (a (2 * j)) := by rw [ha_pair j, if_neg him]
        set c := chooseCPair (auxQ a j) (a (2 * j)) j with hc_def
        have haux_eq : auxQ a (j + 1) = fun z => auxQ a j z * E j c (z / a (2 * j))
            * E j ((starRingEnd ℂ) c) (z / a (2 * j + 1)) := by
          funext z; simp only [auxQ, if_neg him, ← hc_def]
        rw [haux_eq]
        refine ⟨(hAnalytic.mul (hfactor_analytic c (a (2 * j)) (ha0 (2 * j)))).mul
          (hfactor_analytic ((starRingEnd ℂ) c) (a (2 * j + 1)) (ha0 (2 * j + 1))), ?_, ?_⟩
        · simp [hOne, E_zero]
        · have hassoc : (fun z => auxQ a j z * E j c (z / a (2 * j))
              * E j ((starRingEnd ℂ) c) (z / a (2 * j + 1)))
              = fun z => auxQ a j z * (E j c (z / a (2 * j))
                * E j ((starRingEnd ℂ) c) (z / a (2 * j + 1))) := by
            funext z; ring
          rw [hassoc, hodd]
          exact hSymm.mul (conjSymmetric_E_pair j c (a (2 * j)))

/-- The correction-constant sequence matching `auxQ`'s slot-by-slot choices. -/
private noncomputable def cOfSlot (a : ℕ → ℂ) (k : ℕ) : ℂ :=
  if (a (2 * (k / 2))).im = 0 then
    (if k % 2 = 0 then chooseCReal (auxQ a (k / 2)) (a (2 * (k / 2))) (k / 2) else 1)
  else
    (if k % 2 = 0 then chooseCPair (auxQ a (k / 2)) (a (2 * (k / 2))) (k / 2)
     else (starRingEnd ℂ) (chooseCPair (auxQ a (k / 2)) (a (2 * (k / 2))) (k / 2)))

private theorem auxQ_eq_pairProduct (a : ℕ → ℂ) (j : ℕ) :
    auxQ a j = pairProduct a (cOfSlot a) (2 * j) := by
  induction j with
  | zero => rw [pairProduct_zero]; rfl
  | succ j ih =>
      have hdiv0 : 2 * j / 2 = j := by omega
      have hdiv1 : (2 * j + 1) / 2 = j := by omega
      have hc0 : cOfSlot a (2 * j) = (if (a (2 * j)).im = 0
          then chooseCReal (auxQ a j) (a (2 * j)) j else chooseCPair (auxQ a j) (a (2 * j)) j) := by
        unfold cOfSlot; simp [hdiv0]
      have hc1 : cOfSlot a (2 * j + 1) = (if (a (2 * j)).im = 0
          then (1 : ℂ) else (starRingEnd ℂ) (chooseCPair (auxQ a j) (a (2 * j)) j)) := by
        unfold cOfSlot; simp [hdiv1]
      have hstep : pairProduct a (cOfSlot a) (2 * (j + 1))
          = fun z => pairProduct a (cOfSlot a) (2 * j) z
            * E (2 * j / 2) (cOfSlot a (2 * j)) (z / a (2 * j))
            * E ((2 * j + 1) / 2) (cOfSlot a (2 * j + 1)) (z / a (2 * j + 1)) := by
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pairProduct_succ, pairProduct_succ]
      rw [hstep, ← ih, hdiv0, hdiv1, hc0, hc1]
      by_cases him : (a (2 * j)).im = 0
      · rw [if_pos him, if_pos him]
        funext z; simp only [auxQ, if_pos him]
      · rw [if_neg him, if_neg him]
        funext z; simp only [auxQ, if_neg him]

/-! ## Rounding-error bounds -/

private theorem chooseCReal_sub_one_le (h : ℂ → ℂ) (a : ℂ) (n : ℕ)
    (hreal : (starRingEnd ℂ) (taylorCoeff h (n + 1)) = taylorCoeff h (n + 1)) :
    ‖chooseCReal h a n - 1‖ ≤ (1 / 2 : ℝ) * (n + 1) * ‖a‖ ^ (n + 1) := by
  set v : ℂ := taylorCoeff h (n + 1) with hv_def
  have hvre : v = (v.re : ℂ) := by
    have hre := Complex.re_add_im v
    have him0 : v.im = 0 := by
      have himeq := congrArg Complex.im hreal
      rw [Complex.conj_im] at himeq
      linarith
    rw [← hre, him0]; simp
  have hbound : ‖nearestIntC v.re - v‖ ≤ 1 / 2 := by
    have heq : nearestIntC v.re - v = -((v.re : ℂ) - nearestIntC v.re) := by
      rw [← hvre]; ring
    rw [heq, norm_neg]
    exact norm_sub_nearestIntC_le v.re
  have h2 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  unfold chooseCReal
  rw [← hv_def]
  calc ‖1 + (nearestIntC v.re - v) * (((n : ℂ) + 1) * a ^ (n + 1)) - 1‖
      = ‖nearestIntC v.re - v‖ * ‖((n : ℂ) + 1)‖ * ‖a‖ ^ (n + 1) := by
        rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_pow]; ring
    _ ≤ (1 / 2) * ((n : ℝ) + 1) * ‖a‖ ^ (n + 1) := by rw [h2]; gcongr

private theorem chooseCPair_sub_one_le (h : ℂ → ℂ) (a : ℂ) (n : ℕ) :
    ‖chooseCPair h a n - 1‖ ≤ (1 / 4 : ℝ) * (n + 1) * ‖a‖ ^ (n + 1) := by
  set v : ℂ := taylorCoeff h (n + 1) with hv_def
  set Δ : ℝ := (round v.re : ℝ) - v.re with hΔ_def
  have hΔbound : |Δ| ≤ 1 / 2 := by rw [hΔ_def, abs_sub_comm]; exact abs_sub_round v.re
  have h2 : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  unfold chooseCPair
  rw [← hv_def, ← hΔ_def, add_sub_cancel_left, norm_mul,
    norm_div, norm_mul, Complex.norm_real, h2, show ‖(2 : ℂ)‖ = 2 by norm_num,
    Complex.norm_pow, Real.norm_eq_abs]
  calc |Δ| * ((n : ℝ) + 1) / 2 * ‖a‖ ^ (n + 1)
      ≤ (1 / 2) * ((n : ℝ) + 1) / 2 * ‖a‖ ^ (n + 1) := by gcongr
    _ = (1 / 4 : ℝ) * (n + 1) * ‖a‖ ^ (n + 1) := by ring

/-! ## Existence of the integer coefficient sequence -/

private theorem auxQ_succ_taylorCoeff_int (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0)
    (ha_pair : ∀ j, a (2 * j + 1) = if (a (2 * j)).im = 0 then 2 else (starRingEnd ℂ) (a (2 * j)))
    (j : ℕ) : ∃ k : ℤ, taylorCoeff (auxQ a (j + 1)) (j + 1) = k := by
  obtain ⟨hAnalytic, hOne, hSymm⟩ := auxQ_invariant a ha0 ha_pair j
  by_cases him : (a (2 * j)).im = 0
  · -- real slot
    set h1 : ℂ → ℂ :=
      fun z => auxQ a j z * E j (chooseCReal (auxQ a j) (a (2 * j)) j) (z / a (2 * j))
      with hh1_def
    have hh1analytic : AnalyticAt ℂ h1 0 := by
      have h1a : AnalyticAt ℂ (fun z : ℂ => z / a (2 * j)) 0 := by fun_prop
      have h2a : AnalyticAt ℂ (E j (chooseCReal (auxQ a j) (a (2 * j)) j)) (0 / a (2 * j)) := by
        rw [zero_div]; unfold E; fun_prop
      exact hAnalytic.mul (AnalyticAt.comp (f := fun z : ℂ => z / a (2 * j)) (x := 0) h2a h1a)
    have hh1_0 : h1 0 = 1 := by simp [hh1_def, hOne, E_zero]
    have hh1_coeff : taylorCoeff h1 (j + 1) = nearestIntC (taylorCoeff (auxQ a j) (j + 1)).re :=
      chooseCReal_spec (auxQ a j) (a (2 * j)) j hAnalytic hOne (ha0 (2 * j))
    have hsecond := taylorCoeff_mul_E_succ (c := (1 : ℂ)) hh1analytic hh1_0 (ha0 (2 * j + 1)) j
    rw [hh1_coeff, sub_self, zero_div, add_zero] at hsecond
    refine ⟨round (taylorCoeff (auxQ a j) (j + 1)).re, ?_⟩
    have haux_eq : auxQ a (j + 1) = fun z => h1 z * E j 1 (z / a (2 * j + 1)) := by
      funext z; simp only [auxQ, if_pos him, hh1_def]
    rw [haux_eq, hsecond]
    unfold nearestIntC; ring
  · -- conjugate-pair slot
    refine ⟨round (taylorCoeff (auxQ a j) (j + 1)).re, ?_⟩
    have hodd : a (2 * j + 1) = (starRingEnd ℂ) (a (2 * j)) := by rw [ha_pair j, if_neg him]
    have haux_eq : auxQ a (j + 1) = fun z => auxQ a j z
        * E j (chooseCPair (auxQ a j) (a (2 * j)) j) (z / a (2 * j))
        * E j ((starRingEnd ℂ) (chooseCPair (auxQ a j) (a (2 * j)) j))
          (z / (starRingEnd ℂ) (a (2 * j))) := by
      funext z; rw [← hodd]; simp only [auxQ, if_neg him]
    rw [haux_eq, chooseCPair_spec (auxQ a j) (a (2 * j)) j hAnalytic hOne (ha0 (2 * j))
      (taylorCoeff_real_of_conjSymmetric hAnalytic hSymm (j + 1))]
    unfold nearestIntC; ring

theorem exists_pairCoeffSeq (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0)
    (ha_pair : ∀ j, a (2 * j + 1) = if (a (2 * j)).im = 0 then 2 else (starRingEnd ℂ) (a (2 * j))) :
    ∃ c : ℕ → ℂ,
      (∀ m, ∃ k : ℤ, taylorCoeff (pairProduct a c (2 * m)) m = k) ∧
      (∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * ((k / 2 : ℕ) + 1 : ℝ) * ‖a k‖ ^ (k / 2 + 1)) := by
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact (Real.sqrt_lt_sqrt (by norm_num) (by norm_num)).le
  refine ⟨cOfSlot a, ?_, ?_⟩
  · intro m
    rw [← auxQ_eq_pairProduct a m]
    cases m with
    | zero => exact ⟨1, by unfold auxQ; simp [taylorCoeff, iteratedDeriv_zero]⟩
    | succ j => exact auxQ_succ_taylorCoeff_int a ha0 ha_pair j
  · intro k
    have hcOfSlot0 : ∀ j, cOfSlot a (2 * j) = (if (a (2 * j)).im = 0
        then chooseCReal (auxQ a j) (a (2 * j)) j else chooseCPair (auxQ a j) (a (2 * j)) j) := by
      intro j
      unfold cOfSlot
      rw [Nat.mul_div_cancel_left j (by norm_num : 0 < 2), Nat.mul_mod_right]
      simp
    have hcOfSlot1 : ∀ j, cOfSlot a (2 * j + 1) = (if (a (2 * j)).im = 0
        then (1 : ℂ) else (starRingEnd ℂ) (chooseCPair (auxQ a j) (a (2 * j)) j)) := by
      intro j
      unfold cOfSlot
      have he1 : (2 * j + 1) / 2 = j := by omega
      have he2 : (2 * j + 1) % 2 = 1 := by omega
      rw [he1, he2]; simp
    rcases Nat.even_or_odd k with ⟨j, hj0⟩ | ⟨j, hj⟩
    · have hj : k = 2 * j := by omega
      have hkdiv : k / 2 = j := by omega
      subst hj
      rw [hcOfSlot0, hkdiv]
      obtain ⟨hAnalytic, hOne, hSymm⟩ := auxQ_invariant a ha0 ha_pair j
      split_ifs with him
      · calc ‖chooseCReal (auxQ a j) (a (2 * j)) j - 1‖
            ≤ (1 / 2 : ℝ) * (j + 1) * ‖a (2 * j)‖ ^ (j + 1) :=
              chooseCReal_sub_one_le (auxQ a j) (a (2 * j)) j
                (taylorCoeff_real_of_conjSymmetric hAnalytic hSymm (j + 1))
          _ ≤ Real.sqrt 2 / 2 * ((j : ℝ) + 1) * ‖a (2 * j)‖ ^ (j + 1) := by
              gcongr
      · calc ‖chooseCPair (auxQ a j) (a (2 * j)) j - 1‖
            ≤ (1 / 4 : ℝ) * (j + 1) * ‖a (2 * j)‖ ^ (j + 1) :=
              chooseCPair_sub_one_le (auxQ a j) (a (2 * j)) j
          _ ≤ Real.sqrt 2 / 2 * ((j : ℝ) + 1) * ‖a (2 * j)‖ ^ (j + 1) := by
              gcongr
              linarith
    · have hkdiv : k / 2 = j := by omega
      rw [hkdiv, hj, hcOfSlot1]
      split_ifs with him
      · simp only [sub_self, norm_zero]
        positivity
      · rw [show (starRingEnd ℂ) (chooseCPair (auxQ a j) (a (2 * j)) j) - 1
              = (starRingEnd ℂ) (chooseCPair (auxQ a j) (a (2 * j)) j - 1) by
            rw [map_sub, map_one]]
        rw [Complex.norm_conj]
        have hb := chooseCPair_sub_one_le (auxQ a j) (a (2 * j)) j
        have hodd_norm : ‖a (2 * j)‖ = ‖a (2 * j + 1)‖ := by
          rw [ha_pair j, if_neg him]
          exact (Complex.norm_conj _).symm
        rw [hodd_norm] at hb
        calc ‖chooseCPair (auxQ a j) (a (2 * j)) j - 1‖
            ≤ (1 / 4 : ℝ) * (j + 1) * ‖a (2 * j + 1)‖ ^ (j + 1) := hb
          _ ≤ Real.sqrt 2 / 2 * ((j : ℝ) + 1) * ‖a (2 * j + 1)‖ ^ (j + 1) := by
              gcongr
              linarith

/-! ## The Weierstrass `M`-test for the paired construction -/

private theorem summable_pow_half (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun k : ℕ => r ^ (k / 2 + d)) := by
  have hsr0 : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsr1 : Real.sqrt r < 1 := (Real.sqrt_lt' (by norm_num)).mpr (by rw [one_pow]; exact hr1)
  have hle : ∀ k : ℕ, r ^ (k / 2 + d) ≤ (Real.sqrt r) ^ k := by
    intro k
    have hpow : r ^ (k / 2 + d) = (Real.sqrt r) ^ (2 * (k / 2 + d)) := by
      rw [pow_mul, Real.sq_sqrt hr0]
    rw [hpow]
    have hexp : k ≤ 2 * (k / 2 + d) := by omega
    exact pow_le_pow_of_le_one hsr0 hsr1.le hexp
  exact Summable.of_nonneg_of_le (fun k => by positivity) hle
    (summable_geometric_of_lt_one hsr0 hsr1)

theorem exists_Mtest_of_pairCoeffSeq (a c : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0)
    (hesc : ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite)
    (hc : ∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * ((k / 2 : ℕ) + 1 : ℝ) * ‖a k‖ ^ (k / 2 + 1)) :
    ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (k / 2) (c k) (z / a k) - 1‖ ≤ u k := by
  classical
  intro K hKsub hKcpt
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨fun _ => 0, summable_zero, by simp [hKe]⟩
  obtain ⟨z₀, hz₀K, hz₀max⟩ :=
    hKcpt.exists_isMaxOn hKne (continuous_norm.continuousOn (s := K))
  set r : ℝ := ‖z₀‖ with hr_def
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := mem_𝔻_iff.mp (hKsub hz₀K)
  have hKr : ∀ z ∈ K, ‖z‖ ≤ r := fun z hz => hz₀max hz
  set s : ℝ := (r + 1) / 2 with hs_def
  have hrs : r < s := by rw [hs_def]; linarith
  have hs1 : s < 1 := by rw [hs_def]; linarith
  have hs0 : 0 < s := by linarith
  have hrs0 : 0 ≤ r / s := div_nonneg hr0 hs0.le
  have hrs1 : r / s < 1 := (div_lt_one hs0).mpr hrs
  set F : Set ℕ := {k | ‖a k‖ < s} with hF_def
  have hFfin : F.Finite := hesc s hs1
  set B : ℕ → ℝ := fun k => Real.sqrt 2 / 2 * r ^ (k / 2 + 1) + (r / s) ^ (k / 2 + 2) / (1 - r / s)
    with hB_def
  have hBnonneg : ∀ k, 0 ≤ B k := fun k => by
    have : (0 : ℝ) < 1 - r / s := by linarith
    positivity
  have hSummable_r : Summable (fun k : ℕ => r ^ (k / 2 + 1)) :=
    summable_pow_half r hr0 hr1 1 le_rfl
  have hSummable_rs : Summable (fun k : ℕ => (r / s) ^ (k / 2 + 2)) :=
    summable_pow_half (r / s) hrs0 hrs1 2 (by norm_num)
  have hBsummable : Summable B := by
    have h1 : Summable (fun k => Real.sqrt 2 / 2 * r ^ (k / 2 + 1)) := hSummable_r.mul_left _
    have h2 : Summable (fun k => (r / s) ^ (k / 2 + 2) / (1 - r / s)) := by
      simpa [div_eq_mul_inv, mul_comm] using hSummable_rs.mul_right (1 - r / s)⁻¹
    simpa [hB_def] using h1.add h2
  have hBtendsto : Filter.Tendsto B Filter.atTop (nhds 0) := hBsummable.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hBtendsto (1 / 2) (by norm_num)
  have hNbound : ∀ k, N ≤ k → B k < 1 / 2 := by
    intro k hk
    have := hN k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hBnonneg k)] at this
  set Bad : Set ℕ := F ∪ {k | k < N} with hBad_def
  have hBadFin : Bad.Finite := hFfin.union (Set.finite_Iio N)
  have hMbound : ∀ k, ∃ M : ℝ, ∀ z ∈ K, ‖E (k / 2) (c k) (z / a k) - 1‖ ≤ M := by
    intro k
    have h1 : ContinuousOn (fun z : ℂ => z / a k) K := by fun_prop
    have h2 : Continuous (E (k / 2) (c k)) := by unfold E; fun_prop
    have hcont : ContinuousOn (fun z => ‖E (k / 2) (c k) (z / a k) - 1‖) K :=
      ((h2.comp_continuousOn h1).sub continuousOn_const).norm
    obtain ⟨zmax, hzmaxK, hzmaxmax⟩ := hKcpt.exists_isMaxOn hKne hcont
    exact ⟨_, fun z hz => hzmaxmax hz⟩
  choose M hM using hMbound
  refine ⟨fun k => (if k ∈ Bad then max (M k) 0 else 0) + 2 * B k, ?_, ?_⟩
  · refine Summable.add ?_ (hBsummable.mul_left 2)
    exact (hasSum_sum_of_ne_finset_zero
      (s := hBadFin.toFinset) (fun b hb => by simp [Set.Finite.mem_toFinset] at hb; simp [hb])
      ).summable
  · intro k z hz
    by_cases hkBad : k ∈ Bad
    · simp only [hkBad, if_true]
      have := hM k z hz
      have hM0 : M k ≤ max (M k) 0 := le_max_left _ _
      have : 0 ≤ 2 * B k := by positivity
      linarith [hM k z hz]
    · simp only [hkBad, if_false, zero_add]
      rw [hBad_def, Set.mem_union, hF_def] at hkBad
      push Not at hkBad
      obtain ⟨hkF, hkN⟩ := hkBad
      have hak0 : a k ≠ 0 := ha0 k
      have haks : s ≤ ‖a k‖ := not_lt.mp hkF
      have hakN : N ≤ k := not_lt.mp hkN
      have hakpos : 0 < ‖a k‖ := lt_of_lt_of_le hs0 haks
      set ρ : ℝ := r / ‖a k‖ with hρ_def
      have hρ0 : 0 ≤ ρ := div_nonneg hr0 hakpos.le
      have hρs : ρ ≤ r / s := div_le_div_of_nonneg_left hr0 hs0 haks
      have hρ1 : ρ < 1 := lt_of_le_of_lt hρs hrs1
      have hzk : ‖z / a k‖ ≤ ρ := by
        rw [norm_div, hρ_def]
        gcongr
        exact hKr z hz
      have hGbound := norm_G_le (k / 2) (c k) (z / a k) hρ0 hρ1 hzk
      have haffine : ‖c k - 1‖ / ((k / 2 : ℕ) + 1) * ρ ^ (k / 2 + 1)
          ≤ Real.sqrt 2 / 2 * r ^ (k / 2 + 1) := by
        have h1 : ‖c k - 1‖ / ((k / 2 : ℕ) + 1) ≤ Real.sqrt 2 / 2 * ‖a k‖ ^ (k / 2 + 1) := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((k / 2 : ℕ) : ℝ) + 1)]
          calc ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * ((k / 2 : ℕ) + 1 : ℝ) * ‖a k‖ ^ (k / 2 + 1) := hc k
            _ = Real.sqrt 2 / 2 * ‖a k‖ ^ (k / 2 + 1) * (((k / 2 : ℕ) : ℝ) + 1) := by ring
        calc ‖c k - 1‖ / ((k / 2 : ℕ) + 1) * ρ ^ (k / 2 + 1)
            ≤ (Real.sqrt 2 / 2 * ‖a k‖ ^ (k / 2 + 1)) * ρ ^ (k / 2 + 1) := by gcongr
          _ = Real.sqrt 2 / 2 * (‖a k‖ * ρ) ^ (k / 2 + 1) := by rw [mul_pow]; ring
          _ = Real.sqrt 2 / 2 * r ^ (k / 2 + 1) := by
              rw [hρ_def, mul_div_cancel₀ _ (ne_of_gt hakpos)]
      have htail : ρ ^ (k / 2 + 2) / (1 - ρ) ≤ (r / s) ^ (k / 2 + 2) / (1 - r / s) := by
        have h2 : (0 : ℝ) < 1 - r / s := by linarith
        have h4 : 1 - r / s ≤ 1 - ρ := by linarith
        calc ρ ^ (k / 2 + 2) / (1 - ρ)
            ≤ (r / s) ^ (k / 2 + 2) / (1 - ρ) := by gcongr
          _ ≤ (r / s) ^ (k / 2 + 2) / (1 - r / s) :=
              div_le_div_of_nonneg_left (by positivity) h2 h4
      have hGbound2 : ‖G (k / 2) (c k) (z / a k)‖ ≤ B k :=
        hGbound.trans (add_le_add haffine htail)
      have hGlt_half : ‖G (k / 2) (c k) (z / a k)‖ < 1 / 2 :=
        lt_of_le_of_lt hGbound2 (hNbound k hakN)
      have hGle1 : ‖G (k / 2) (c k) (z / a k)‖ ≤ 1 := by linarith
      have hzk𝔻 : z / a k ∈ 𝔻 := mem_𝔻_iff.mpr (lt_of_le_of_lt hzk hρ1)
      rw [E_eq_exp_G hzk𝔻]
      calc ‖Complex.exp (G (k / 2) (c k) (z / a k)) - 1‖
          ≤ 2 * ‖G (k / 2) (c k) (z / a k)‖ := Complex.norm_exp_sub_one_le hGle1
        _ ≤ 2 * B k := by linarith

end Weierstrass
