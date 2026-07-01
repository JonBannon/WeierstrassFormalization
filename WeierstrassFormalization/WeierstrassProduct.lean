/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.AffineControl
import WeierstrassFormalization.Divisor
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# The Weierstrass-type product construction

Scaffolding for the proof of Theorem `prop:Zi` (`GaussianRealization.lean`), following the
paper's proof (`integer_weierstrass_18.tex`, Section 3) closely: given an effective divisor
`D` on `𝔻`, we build a holomorphic function on `𝔻` with zero divisor `D` and Taylor
coefficients in `ℤ[i]`, as an infinite product
`f(z) = ∏' k, E k (c k) (z / a k)`
where `a` enumerates the (locally finite) support of `D` with multiplicity, the degree of the
`k`-th factor is simply `k` (dense, no gaps — this is the key simplification making both the
Gaussian-integer forcing *and* the convergence estimate work with a single index), and the
correction constants `c : ℕ → ℂ` are chosen via `exists_c_taylorCoeff_mul_E_succ_eq` (Remark
`rem:triangular`, `AffineControl.lean`) to round each newly-introduced Taylor coefficient of
the partial products to the nearest Gaussian integer. The point of rounding to the *nearest*
Gaussian integer (rather than forcing the coefficient to `0`) is the bound
`‖c k - 1‖ ≤ (√2/2) * (k+1) * ‖a k‖ ^ (k+1)`: the `‖a k‖ ^ (k+1)` growth here exactly cancels
the `‖a k‖ ^ (k+1)` shrinkage of `‖z / a k‖ ^ (k+1)` in the convergence estimate, giving a
bound independent of how fast `a k` approaches the boundary.

This file is organized as a sequence of lemmas mirroring the paper's proof structure. Several
are stated but not yet proved (`sorry`); each docstring records exactly what it must establish
and how it is meant to be used, so they can be tackled independently.
-/

namespace Weierstrass

open Complex Filter Topology

/-! ## Gaussian-integer rounding -/

/-- A nearest Gaussian integer to `v : ℂ`, rounding real and imaginary parts independently. -/
noncomputable def nearestGaussianInt (v : ℂ) : GaussianInt := ⟨round v.re, round v.im⟩

/-- The rounding error of `nearestGaussianInt` is bounded by `√2/2` (Section 3, Step 1: "the
nearest-`ℤ[i]` rounding error satisfies `|T-v| ≤ √2/2`"). -/
theorem norm_sub_nearestGaussianInt_le (v : ℂ) :
    ‖v - (nearestGaussianInt v : ℂ)‖ ≤ Real.sqrt 2 / 2 := by
  have hre : |v.re - (round v.re : ℝ)| ≤ 1 / 2 := abs_sub_round v.re
  have him : |v.im - (round v.im : ℝ)| ≤ 1 / 2 := abs_sub_round v.im
  have hval1 : (v - (nearestGaussianInt v : ℂ)).re = v.re - round v.re := by
    simp [nearestGaussianInt, GaussianInt.toComplex_def']
  have hval2 : (v - (nearestGaussianInt v : ℂ)).im = v.im - round v.im := by
    simp [nearestGaussianInt, GaussianInt.toComplex_def']
  have hbound := Complex.norm_le_sqrt_two_mul_max (v - (nearestGaussianInt v : ℂ))
  rw [hval1, hval2] at hbound
  have hmax : max |v.re - (round v.re : ℝ)| |v.im - (round v.im : ℝ)| ≤ 1 / 2 := max_le hre him
  calc ‖v - (nearestGaussianInt v : ℂ)‖
      ≤ Real.sqrt 2 * max |v.re - (round v.re : ℝ)| |v.im - (round v.im : ℝ)| := hbound
    _ ≤ Real.sqrt 2 * (1 / 2) := by gcongr
    _ = Real.sqrt 2 / 2 := by ring

/-! ## A quantitative bound on the exponent `G` -/

/-- **Bound on the exponent `G_n(w;c)`** (Section 3, Step 3, first display).
For `‖w‖ ≤ ρ < 1`,
`‖G n c w‖ ≤ ‖c - 1‖ / (n+1) * ρ^(n+1) + ρ^(n+2) / (1 - ρ)`,
bounding the affine-correction term and the geometric tail of the exponent separately.

Proof sketch: bound the first term of `G` by the triangle inequality directly. For the tail
`∑' k, if k ≥ n+2 then w^k/k else 0`, bound `‖w^k/k‖ ≤ ‖w‖^k` termwise (since `k ≥ n+2 ≥ 1`)
and sum the resulting geometric tail `∑_{k ≥ n+2} ρ^k = ρ^(n+2)/(1-ρ)`, reusing the
shift/reindexing argument from `E_eq_exp_G`'s proof (`Function.Injective.hasSum_iff` with
`g := (· + (n+2))`, or `tsum_geometric_of_norm_lt_one` combined with
`Summable.sum_add_tsum_nat_add`). -/
theorem norm_G_le (n : ℕ) (c w : ℂ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : ‖w‖ ≤ ρ) :
    ‖G n c w‖ ≤ ‖c - 1‖ / (n + 1) * ρ ^ (n + 1) + ρ ^ (n + 2) / (1 - ρ) := by
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw hρ1
  -- the tail sum agrees with a shifted `tsum`, exactly as in `E_eq_exp_G`'s proof
  set f0 : ℕ → ℂ := fun k => w ^ k / k with hf0_def
  have hSum0 : HasSum f0 (-Complex.log (1 - w)) := Complex.hasSum_taylorSeries_neg_log hw1
  have hSummable0 : Summable f0 := hSum0.summable
  have hginj : Function.Injective (fun i : ℕ => i + (n + 2)) := add_left_injective (n + 2)
  have hfzero : ∀ x, x ∉ Set.range (fun i : ℕ => i + (n + 2)) →
      (if x ≥ n + 2 then f0 x else 0) = 0 := by
    intro x hx
    rw [if_neg]
    intro hge
    exact hx ⟨x - (n + 2), Nat.sub_add_cancel hge⟩
  have hshiftSummable : Summable (fun i : ℕ => f0 (i + (n + 2))) :=
    (summable_nat_add_iff (n + 2)).2 hSummable0
  have hcomp : (fun k : ℕ => if k ≥ n + 2 then f0 k else 0) ∘ (fun i : ℕ => i + (n + 2))
      = fun i : ℕ => f0 (i + (n + 2)) := by
    funext i
    simp only [Function.comp_apply]
    rw [if_pos (Nat.le_add_left (n + 2) i)]
  have hTHasSum : HasSum (fun k : ℕ => if k ≥ n + 2 then f0 k else 0) (∑' i, f0 (i + (n + 2))) :=
    (hginj.hasSum_iff hfzero).mp (hcomp ▸ hshiftSummable.hasSum)
  have hT_eq : (∑' k : ℕ, if k ≥ n + 2 then f0 k else 0) = ∑' i, f0 (i + (n + 2)) :=
    hTHasSum.tsum_eq
  -- bound the tail by a geometric series
  have hbound_tail : ‖∑' i, f0 (i + (n + 2))‖ ≤ ρ ^ (n + 2) / (1 - ρ) := by
    have hterm_le : ∀ i, ‖f0 (i + (n + 2))‖ ≤ ρ ^ (n + 2) * ρ ^ i := by
      intro i
      have h1 : ‖f0 (i + (n + 2))‖ = ‖w‖ ^ (i + (n + 2)) / ((i + (n + 2) : ℕ) : ℝ) := by
        change ‖w ^ (i + (n + 2)) / ((i + (n + 2) : ℕ) : ℂ)‖
            = ‖w‖ ^ (i + (n + 2)) / ((i + (n + 2) : ℕ) : ℝ)
        rw [norm_div, norm_pow, Complex.norm_natCast]
      rw [h1]
      have hge1 : (1 : ℝ) ≤ ((i + (n + 2) : ℕ) : ℝ) := by
        have : (2 : ℝ) ≤ ((i + (n + 2) : ℕ) : ℝ) := by
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]
        linarith
      calc ‖w‖ ^ (i + (n + 2)) / ((i + (n + 2) : ℕ) : ℝ)
          ≤ ‖w‖ ^ (i + (n + 2)) := div_le_self (by positivity) hge1
        _ ≤ ρ ^ (i + (n + 2)) := by gcongr
        _ = ρ ^ (n + 2) * ρ ^ i := by rw [pow_add]; ring
    have hsummableρ : Summable (fun i : ℕ => ρ ^ (n + 2) * ρ ^ i) :=
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
    calc ‖∑' i, f0 (i + (n + 2))‖
        ≤ ∑' i, ‖f0 (i + (n + 2))‖ := norm_tsum_le_tsum_norm (hshiftSummable.norm)
      _ ≤ ∑' i, ρ ^ (n + 2) * ρ ^ i := (hshiftSummable.norm).tsum_le_tsum hterm_le hsummableρ
      _ = ρ ^ (n + 2) * ∑' i, ρ ^ i := tsum_mul_left
      _ = ρ ^ (n + 2) * (1 - ρ)⁻¹ := by rw [tsum_geometric_of_lt_one hρ0 hρ1]
      _ = ρ ^ (n + 2) / (1 - ρ) := by ring
  -- bound the affine term
  have hbound_affine : ‖(c - 1) * w ^ (n + 1) / (n + 1)‖ ≤ ‖c - 1‖ / (n + 1) * ρ ^ (n + 1) := by
    have hcast : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    push_cast
    rw [div_mul_eq_mul_div,
      div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    gcongr
  unfold G
  calc ‖(c - 1) * w ^ (n + 1) / (n + 1) - ∑' k : ℕ, if k ≥ n + 2 then w ^ k / k else 0‖
      ≤ ‖(c - 1) * w ^ (n + 1) / (n + 1)‖
        + ‖∑' k : ℕ, if k ≥ n + 2 then w ^ k / k else 0‖ := norm_sub_le _ _
    _ ≤ ‖c - 1‖ / (n + 1) * ρ ^ (n + 1) + ρ ^ (n + 2) / (1 - ρ) := by
        rw [hT_eq]
        exact add_le_add hbound_affine hbound_tail

/-! ## Divisor enumeration -/

/-- **Divisor enumeration** (Section 3, proof of `prop:Zi`, first paragraph).
The support of an effective divisor `D`, away from the origin, can be enumerated as a
sequence `a : ℕ → ℂ` realizing the multiplicity function `D.mult` by counting repeats
(`Set.ncard` of the fibre), with the enumerated points escaping to the boundary of `𝔻` in the
sense that any fixed radius `s < 1` bounds `‖a k‖` from below for all but finitely many `k`.

Unlike the paper, we do not require `a k ∈ 𝔻`: to handle a divisor with finite support
uniformly (rather than as a separate "vacuous" case — see the discussion in
`GaussianRealization.lean` on the gap this closes in the paper's treatment of that case), the
enumeration is padded, once the support is exhausted, by a fixed point outside `𝔻` (e.g.
`a k := 2`), which trivially satisfies the escape property and contributes no zero in `𝔻`.
The point `z = 0` is excluded here and handled separately in the final assembly by an
explicit monomial factor `z ^ D.mult 0`.

Proof sketch: `𝔻 \ {0}` is exhausted by the compact annuli `{z | 1/(m+2) ≤ ‖z‖ ≤ 1-1/(m+2)}`;
on each, `D.finite_inter_compact` gives a finite subset of the support with multiplicities,
listed (each point repeated according to its multiplicity) into a finite list; concatenating
these lists over `m`, in order, gives an enumeration of `D.support \ {0}` with the escape
property (paper's "such an enumeration exists ... because `S` is discrete"). If this
enumeration is finite (or empty), continue it with the constant sequence `a k := 2`. -/
private theorem support_countable (D : EffectiveDivisor) : (D.support \ {0}).Countable := by
  have hsub : D.support \ {0} ⊆ ⋃ m : ℕ, D.support ∩ Metric.closedBall 0 (1 - 1 / (m + 2)) := by
    intro z hz
    have hzS : z ∈ D.support := hz.1
    have hz𝔻 : z ∈ 𝔻 := by
      by_contra h; exact hzS (D.mult_eq_zero_of_not_mem_𝔻 z h)
    have hzn1 : ‖z‖ < 1 := mem_𝔻_iff.mp hz𝔻
    have h1mz : (0:ℝ) < 1 - ‖z‖ := by linarith
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - ‖z‖))
    rw [div_lt_iff₀ h1mz] at hm
    refine Set.mem_iUnion.mpr ⟨m, hzS, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : (0:ℝ) < (m:ℝ) + 2 := by positivity
    rw [show (1:ℝ) - 1 / ((m:ℝ) + 2) = ((m:ℝ) + 2 - 1) / ((m:ℝ) + 2) by field_simp]
    rw [le_div_iff₀ h2]
    nlinarith [hm]
  refine Set.Countable.mono hsub (Set.countable_iUnion fun m => Set.Finite.countable ?_)
  rw [Set.inter_comm]
  refine D.finite_inter_compact _ (fun z hz => ?_) (isCompact_closedBall 0 _)
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  refine mem_𝔻_iff.mpr (lt_of_le_of_lt hz ?_)
  have : (0:ℝ) < 1 / ((m:ℝ) + 2) := by positivity
  linarith

theorem exists_enum_of_effectiveDivisor (D : EffectiveDivisor) :
    ∃ a : ℕ → ℂ, (∀ k, a k ≠ 0) ∧
      (∀ z ≠ 0, D.mult z = {k | a k = z}.ncard) ∧
      ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite := by
  classical
  set S : Set ℂ := D.support \ {0} with hS_def
  have hScount : S.Countable := support_countable D
  haveI : Countable ↥S := hScount.to_subtype
  -- the "labeled zeros with multiplicity": `ZigmaT` has one element `⟨z, i⟩` for each `z ∈ S`
  -- and each `i < D.mult z`.
  let ZigmaT := Σ z : ↥S, Fin (D.mult z)
  haveI : Countable ZigmaT := inferInstance
  -- an injective `ι : ZigmaT → ℕ`, surjective if `ZigmaT` is infinite (so that there is no
  -- "padding" in that case; otherwise `ι` just has finite range, which is enough).
  obtain ⟨ι, hιinj, hιsurj⟩ : ∃ ι : ZigmaT → ℕ, Function.Injective ι ∧
      (Infinite ZigmaT → Function.Surjective ι) := by
    by_cases hfin : Finite ZigmaT
    · exact ⟨Fin.val ∘ Finite.equivFin ZigmaT,
        Fin.val_injective.comp (Finite.equivFin ZigmaT).injective,
        fun hinf => (hinf.not_finite hfin).elim⟩
    · haveI : Infinite ZigmaT := not_finite_iff_infinite.mp hfin
      haveI : Encodable ZigmaT := Encodable.ofCountable ZigmaT
      haveI : Denumerable ZigmaT := Denumerable.ofEncodableOfInfinite ZigmaT
      exact ⟨Denumerable.eqv ZigmaT, (Denumerable.eqv ZigmaT).injective,
        fun _ => (Denumerable.eqv ZigmaT).surjective⟩
  set a : ℕ → ℂ := fun k => if h : ∃ σ : ZigmaT, ι σ = k then ((Classical.choose h).1 : ℂ)
    else 2 with ha_def
  have ha_of_ex {k : ℕ} (h : ∃ σ : ZigmaT, ι σ = k) : a k = ((Classical.choose h).1 : ℂ) := by
    simp only [ha_def, dif_pos h]
  have ha_of_not_ex {k : ℕ} (h : ¬ ∃ σ : ZigmaT, ι σ = k) : a k = 2 := by
    simp only [ha_def, dif_neg h]
  have haS : ∀ k (h : ∃ σ : ZigmaT, ι σ = k), a k ∈ S := by
    intro k h; rw [ha_of_ex h]; exact (Classical.choose h).1.2
  refine ⟨a, ?_, ?_, ?_⟩
  · -- `a k ≠ 0`
    intro k
    by_cases h : ∃ σ : ZigmaT, ι σ = k
    · exact (haS k h).2
    · rw [ha_of_not_ex h]; norm_num
  · -- multiplicity
    intro z0 hz0
    by_cases hzS : z0 ∈ S
    · -- `z0` is genuinely a zero of `D`.
      set zS : ↥S := ⟨z0, hzS⟩ with hzS_def
      have hz0lt1 : ‖z0‖ < 1 := by
        have : z0 ∈ 𝔻 := by
          by_contra h
          exact hzS.1 (D.mult_eq_zero_of_not_mem_𝔻 z0 h) |>.elim
        exact mem_𝔻_iff.mp this
      have hz0ne2 : z0 ≠ 2 := by
        intro h; rw [h] at hz0lt1; norm_num at hz0lt1
      have hset : {k | a k = z0}
          = Set.range (ι ∘ fun i : Fin (D.mult zS) => (⟨zS, i⟩ : ZigmaT)) := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_range]
        constructor
        · intro hak
          have hex : ∃ σ : ZigmaT, ι σ = k := by
            by_contra hne
            rw [ha_of_not_ex hne] at hak
            exact hz0ne2 hak.symm
          rw [ha_of_ex hex] at hak
          generalize hσeq : Classical.choose hex = σ₀ at hak
          obtain ⟨z₁, i₁⟩ := σ₀
          have hz1 : z₁ = zS := Subtype.ext hak
          subst hz1
          refine ⟨i₁, ?_⟩
          simp only [Function.comp_apply]
          rw [← hσeq]
          exact Classical.choose_spec hex
        · rintro ⟨i, hi⟩
          simp only [Function.comp_apply] at hi
          have hex : ∃ σ : ZigmaT, ι σ = k := ⟨⟨zS, i⟩, hi⟩
          rw [ha_of_ex hex]
          have : Classical.choose hex = (⟨zS, i⟩ : ZigmaT) :=
            hιinj (Classical.choose_spec hex |>.trans hi.symm)
          rw [this]
      have hmk_inj : Function.Injective (fun i : Fin (D.mult zS) => (⟨zS, i⟩ : ZigmaT)) :=
        fun i1 i2 h => by
          have := sigma_mk_injective (α := ↥S) (β := fun z => Fin (D.mult z)) (i := zS) h
          exact this
      rw [hset, Set.ncard_range_of_injective (hιinj.comp hmk_inj)]
      change D.mult z0 = Nat.card (Fin (D.mult zS))
      rw [hzS_def]
      simp [Nat.card_eq_fintype_card]
    · -- `z0` is not a zero of `D`.
      have hmult0 : D.mult z0 = 0 := by
        by_contra h
        exact hzS ⟨h, hz0⟩
      rw [hmult0]
      by_cases hz2 : z0 = 2
      · subst hz2
        have hcompl : {k | a k = 2} = {k | ¬ ∃ σ : ZigmaT, ι σ = k} := by
          ext k
          simp only [Set.mem_setOf_eq]
          constructor
          · intro hak hex
            rw [ha_of_ex hex] at hak
            have : (Classical.choose hex).1.1 ∈ 𝔻 := by
              have := (Classical.choose hex).1.2
              by_contra hnot
              exact this.1 (D.mult_eq_zero_of_not_mem_𝔻 _ hnot)
            rw [hak] at this
            have := mem_𝔻_iff.mp this
            norm_num at this
          · intro hne; exact ha_of_not_ex hne
        rw [hcompl]
        by_cases hfin : Finite ZigmaT
        · symm
          apply Set.Infinite.ncard
          have hrange_fin : (Set.range ι).Finite := Set.finite_range ι
          have : {k | ¬ ∃ σ : ZigmaT, ι σ = k} = (Set.range ι)ᶜ := by
            ext k; simp [Set.mem_range]
          rw [this]
          exact hrange_fin.infinite_compl
        · haveI : Infinite ZigmaT := not_finite_iff_infinite.mp hfin
          have hsurj : Function.Surjective ι := hιsurj this
          have : {k | ¬ ∃ σ : ZigmaT, ι σ = k} = ∅ := by
            ext k
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
            exact hsurj k
          rw [this, Set.ncard_empty]
      · symm
        have : {k | a k = z0} = ∅ := by
          ext k
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hak
          by_cases hex : ∃ σ : ZigmaT, ι σ = k
          · rw [ha_of_ex hex] at hak
            exact hzS (hak ▸ (Classical.choose hex).1.2)
          · rw [ha_of_not_ex hex] at hak
            exact hz2 hak.symm
        rw [this, Set.ncard_empty]
  · -- escape property
    intro s hs
    set T : Set ℂ := D.support ∩ Metric.closedBall 0 s with hT_def
    have hTfin : T.Finite := by
      rw [hT_def, Set.inter_comm]
      refine D.finite_inter_compact _ (fun z hz => ?_) (isCompact_closedBall 0 s)
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact mem_𝔻_iff.mpr (lt_of_le_of_lt hz hs)
    have hfiber_fin : ∀ z ∈ T, {k | a k = z}.Finite := by
      intro z hzT
      have hz2 : z ≠ 2 := by
        intro h
        rw [hT_def] at hzT
        have hzball := hzT.2
        rw [Metric.mem_closedBall, dist_zero_right, h] at hzball
        norm_num at hzball
        linarith
      by_cases hzS : z ∈ S
      · set zS : ↥S := ⟨z, hzS⟩ with hzS_def
        have hsub2 : {k | a k = z}
            ⊆ Set.range (ι ∘ fun i : Fin (D.mult zS) => (⟨zS, i⟩ : ZigmaT)) := by
          intro k hak
          simp only [Set.mem_setOf_eq] at hak
          have hex : ∃ σ : ZigmaT, ι σ = k := by
            by_contra hne; rw [ha_of_not_ex hne] at hak; exact hz2 hak.symm
          rw [ha_of_ex hex] at hak
          generalize hσeq : Classical.choose hex = σ₀ at hak
          obtain ⟨z₁, i₁⟩ := σ₀
          have hz1 : z₁ = zS := Subtype.ext hak
          subst hz1
          refine ⟨i₁, ?_⟩
          simp only [Function.comp_apply]
          rw [← hσeq]
          exact Classical.choose_spec hex
        exact Set.Finite.subset (Set.finite_range _) hsub2
      · have hempty : {k | a k = z} ⊆ (∅ : Set ℕ) := by
          intro k hak
          simp only [Set.mem_setOf_eq] at hak
          by_cases hex : ∃ σ : ZigmaT, ι σ = k
          · rw [ha_of_ex hex] at hak
            exact absurd (hak ▸ (Classical.choose hex).1.2) hzS
          · rw [ha_of_not_ex hex] at hak
            exact hz2 hak.symm
        exact Set.Finite.subset Set.finite_empty hempty
    have hsub : {k | ‖a k‖ < s} ⊆ ⋃ z ∈ T, {k | a k = z} := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      have hak_mem : ∃ σ : ZigmaT, ι σ = k := by
        by_contra hne
        rw [ha_of_not_ex hne] at hk
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2] at hk
        linarith
      have hakT : a k ∈ T := by
        rw [hT_def, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
        exact ⟨(haS k hak_mem).1, le_of_lt hk⟩
      exact Set.mem_iUnion₂.mpr ⟨a k, hakT, rfl⟩
    exact Set.Finite.subset (Set.Finite.biUnion hTfin hfiber_fin) hsub

/-! ## The partial products and the inductive rounding step -/

/-- The `N`-th partial product `P_N = ∏_{k<N} E_k(z/a_k; c_k)` (paper's `P_N`, `0`-indexed so
that `partialProduct a c 0 = 1` and the `k`-th factor introduced has degree exactly `k`). -/
noncomputable def partialProduct (a c : ℕ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => ∏ k ∈ Finset.range N, E k (c k) (z / a k)

theorem partialProduct_zero (a c : ℕ → ℂ) : partialProduct a c 0 = fun _ => 1 := by
  funext z; simp [partialProduct]

theorem partialProduct_succ (a c : ℕ → ℂ) (N : ℕ) :
    partialProduct a c (N + 1) = fun z => partialProduct a c N z * E N (c N) (z / a N) := by
  funext z; simp [partialProduct, Finset.prod_range_succ]

/-- Unconditional version of `exists_c_taylorCoeff_mul_E_succ_eq`: the correction constant is
chosen so that *if* the hypotheses hold, the coefficient is forced to `target`. This lets us
build the constant by `Classical.choose` before we have separately verified the hypotheses,
and check the hypotheses afterwards by an ordinary induction. -/
private theorem exists_c_taylorCoeff_mul_E_succ_eq' (h : ℂ → ℂ) (a : ℂ) (n : ℕ) (target : ℂ) :
    ∃ c : ℂ, AnalyticAt ℂ h 0 → h 0 = 1 → a ≠ 0 →
      taylorCoeff (fun z => h z * E n c (z / a)) (n + 1) = target := by
  by_cases hcond : AnalyticAt ℂ h 0 ∧ h 0 = 1 ∧ a ≠ 0
  · obtain ⟨hh, hh0, ha⟩ := hcond
    obtain ⟨c, hc⟩ := exists_c_taylorCoeff_mul_E_succ_eq hh hh0 ha n target
    exact ⟨c, fun _ _ _ => hc⟩
  · exact ⟨0, fun hh hh0 ha => absurd ⟨hh, hh0, ha⟩ hcond⟩

/-- The correction constant chosen (via `nearestGaussianInt`-rounding) to force the degree
`n + 1` Taylor coefficient of `h * E n c (· / a)`, whenever `h` is analytic at `0` with
`h 0 = 1` and `a ≠ 0`. -/
private noncomputable def chooseC (h : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  Classical.choose (exists_c_taylorCoeff_mul_E_succ_eq' h a n
    (nearestGaussianInt (taylorCoeff h (n + 1))))

private theorem chooseC_spec (h : ℂ → ℂ) (a : ℂ) (n : ℕ)
    (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 1) (ha : a ≠ 0) :
    taylorCoeff (fun z => h z * E n (chooseC h a n) (z / a)) (n + 1)
      = (nearestGaussianInt (taylorCoeff h (n + 1)) : ℂ) :=
  Classical.choose_spec (exists_c_taylorCoeff_mul_E_succ_eq' h a n
    (nearestGaussianInt (taylorCoeff h (n + 1)))) hh hh0 ha

/-- The partial products, built by structural recursion using `chooseC` at each step. Agrees
with `partialProduct a (fun N => chooseC (auxP a N) (a N) N)` (`auxP_eq_partialProduct`). -/
private noncomputable def auxP (a : ℕ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 1
  | (N + 1) => fun z => auxP a N z * E N (chooseC (auxP a N) (a N) N) (z / a N)

private theorem auxP_analyticAt_and_eq_one (a : ℕ → ℂ) (_ha0 : ∀ k, a k ≠ 0) (N : ℕ) :
    AnalyticAt ℂ (auxP a N) 0 ∧ auxP a N 0 = 1 := by
  induction N with
  | zero => exact ⟨by unfold auxP; fun_prop, rfl⟩
  | succ N ih =>
      obtain ⟨hAnalytic, hOne⟩ := ih
      have h1 : AnalyticAt ℂ (fun z : ℂ => z / a N) 0 := by fun_prop
      have h2 : AnalyticAt ℂ (E N (chooseC (auxP a N) (a N) N)) (0 / a N) := by
        rw [zero_div]; unfold E; fun_prop
      refine ⟨?_, ?_⟩
      · change AnalyticAt ℂ (fun z => auxP a N z * E N (chooseC (auxP a N) (a N) N) (z / a N)) 0
        exact hAnalytic.mul
          (AnalyticAt.comp (f := fun z : ℂ => z / a N) (x := 0) h2 h1)
      · change auxP a N 0 * E N (chooseC (auxP a N) (a N) N) (0 / a N) = 1
        simp [hOne, E_zero]

private theorem auxP_succ_taylorCoeff (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0) (N : ℕ) :
    taylorCoeff (auxP a (N + 1)) (N + 1)
      = (nearestGaussianInt (taylorCoeff (auxP a N) (N + 1)) : ℂ) := by
  obtain ⟨hAnalytic, hOne⟩ := auxP_analyticAt_and_eq_one a ha0 N
  exact chooseC_spec (auxP a N) (a N) N hAnalytic hOne (ha0 N)

private theorem chooseC_sub_one_le (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0) (N : ℕ) :
    ‖chooseC (auxP a N) (a N) N - 1‖ ≤ Real.sqrt 2 / 2 * (N + 1) * ‖a N‖ ^ (N + 1) := by
  obtain ⟨hAnalytic, hOne⟩ := auxP_analyticAt_and_eq_one a ha0 N
  set v : ℂ := taylorCoeff (auxP a N) (N + 1) with hv_def
  set cN : ℂ := chooseC (auxP a N) (a N) N with hcN_def
  have hsucc : taylorCoeff (fun z => auxP a N z * E N cN (z / a N)) (N + 1)
      = v + (cN - 1) / ((N + 1) * (a N) ^ (N + 1)) :=
    taylorCoeff_mul_E_succ (c := cN) hAnalytic hOne (ha0 N) N
  have hforce : taylorCoeff (fun z => auxP a N z * E N cN (z / a N)) (N + 1)
      = (nearestGaussianInt v : ℂ) :=
    chooseC_spec (auxP a N) (a N) N hAnalytic hOne (ha0 N)
  have heq : (nearestGaussianInt v : ℂ) = v + (cN - 1) / ((N + 1) * (a N) ^ (N + 1)) := by
    rw [← hforce, hsucc]
  have hn1 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  have hpow : (a N) ^ (N + 1) ≠ 0 := pow_ne_zero _ (ha0 N)
  have hcN_eq : cN - 1 = ((nearestGaussianInt v : ℂ) - v) * ((N + 1) * (a N) ^ (N + 1)) := by
    rw [heq]; field_simp; ring
  have h1 : ‖(nearestGaussianInt v : ℂ) - v‖ ≤ Real.sqrt 2 / 2 := by
    rw [show (nearestGaussianInt v : ℂ) - v = -(v - (nearestGaussianInt v : ℂ)) by ring,
      norm_neg]
    exact norm_sub_nearestGaussianInt_le v
  have h2 : ‖((N : ℂ) + 1)‖ = (N : ℝ) + 1 := by
    rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  calc ‖cN - 1‖
      = ‖(nearestGaussianInt v : ℂ) - v‖ * ‖((N : ℂ) + 1)‖ * ‖a N‖ ^ (N + 1) := by
        rw [hcN_eq, norm_mul, norm_mul, Complex.norm_pow, mul_assoc]
    _ = ‖(nearestGaussianInt v : ℂ) - v‖ * ((N : ℝ) + 1) * ‖a N‖ ^ (N + 1) := by rw [h2]
    _ ≤ Real.sqrt 2 / 2 * ((N : ℝ) + 1) * ‖a N‖ ^ (N + 1) := by gcongr

/-- **Inductive coefficient forcing** (Section 3, proof of `prop:Zi`, Step 1's Claim).
Given points `a : ℕ → ℂ` with `a k ≠ 0`, there is a sequence of correction constants
`c : ℕ → ℂ` such that, writing `P N := partialProduct a c N`:
* every Taylor coefficient of `P N` at degree `N` is (the image of) a Gaussian integer
  (this is the coefficient exactly forced at stage `N`, by rounding to the nearest element
  of `ℤ[i]`; degrees `< N` were already forced, and stay unchanged, at earlier stages by
  `taylorCoeff_mul_E_eq_of_le`);
* the rounding error is controlled: `‖c k - 1‖ ≤ (√2/2) * (k+1) * ‖a k‖ ^ (k+1)`.

Built above via `auxP`/`chooseC`, a structural recursion combined with the unconditional
existence lemma `exists_c_taylorCoeff_mul_E_succ_eq'`. -/
theorem exists_coeffSeq (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0) :
    ∃ c : ℕ → ℂ,
      (∀ N, ∃ z : GaussianInt, taylorCoeff (partialProduct a c N) N = z) ∧
      ∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (k + 1) * ‖a k‖ ^ (k + 1) := by
  refine ⟨fun N => chooseC (auxP a N) (a N) N, ?_, chooseC_sub_one_le a ha0⟩
  have hPeq : ∀ N, auxP a N = partialProduct a (fun N => chooseC (auxP a N) (a N) N) N := by
    intro N
    induction N with
    | zero => rw [partialProduct_zero]; rfl
    | succ N ih =>
        rw [partialProduct_succ, ← ih]
        rfl
  intro N
  cases N with
  | zero =>
      refine ⟨1, ?_⟩
      rw [← hPeq]
      change taylorCoeff (fun _ => (1 : ℂ)) 0 = ((1 : GaussianInt) : ℂ)
      simp [taylorCoeff, iteratedDeriv_zero]
  | succ N =>
      refine ⟨nearestGaussianInt (taylorCoeff (auxP a N) (N + 1)), ?_⟩
      rw [← hPeq]
      exact auxP_succ_taylorCoeff a ha0 N

/-! ## The Weierstrass `M`-test -/

/-- **Weierstrass convergence estimate** (Section 3, proof of `prop:Zi`, Step 3).
Given the quantitative rounding bound on `c` from `exists_coeffSeq` and the escape property
from `exists_enum_of_effectiveDivisor`, the factors `E k (c k) (· / a k)` satisfy a
Weierstrass `M`-test on every compact `K ⊆ 𝔻`: there is a summable bound, uniform in `z ∈ K`.

Proof sketch: fix `K ⊆ 𝔻` compact, so `K ⊆ {z | ‖z‖ ≤ r}` for some `r < 1`
(`IsCompact.exists_forall_le`/boundedness), and fix `s` with `r < s < 1`. By the escape
property, `‖a k‖ ≥ s` for all but finitely many `k`; for those `k` and `z ∈ K`,
`‖z / a k‖ ≤ r / s < 1`, so `norm_G_le` applies (with `ρ := r/s`), and the hypothesis on `c k`
makes the affine term collapse to `(√2/2) r^(k+1)` exactly as in the paper (the `‖a k‖^(k+1)`
factors cancel). Both resulting terms are summable in `k` (geometric with ratios `r < 1` and
`r/s < 1`), and their sum eventually is `< 1/2`, so `E_eq_exp_G` together with
`Complex.norm_exp_sub_one_le` (`‖exp x - 1‖ ≤ 2‖x‖` for `‖x‖ ≤ 1`) converts the `G`-bound into
a bound on `‖E k (c k) (z/a k) - 1‖`. The finitely many exceptional small `k` are handled by
enlarging the bound `u` on a finite set (summability of a sequence is unaffected by changing
finitely many terms). -/
theorem exists_Mtest_of_coeffSeq (a c : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0)
    (hesc : ∀ s : ℝ, s < 1 → {k | ‖a k‖ < s}.Finite)
    (hc : ∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (k + 1) * ‖a k‖ ^ (k + 1)) :
    ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E k (c k) (z / a k) - 1‖ ≤ u k := by
  classical
  intro K hKsub hKcpt
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨fun _ => 0, summable_zero, by simp [hKe]⟩
  -- `K` sits inside a closed disk of radius `r < 1`.
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
  -- the finite exceptional set of `k` with `a k` too close to `0`.
  set F : Set ℕ := {k | ‖a k‖ < s} with hF_def
  have hFfin : F.Finite := hesc s hs1
  -- the summable geometric majorant.
  set B : ℕ → ℝ := fun k => Real.sqrt 2 / 2 * r ^ (k + 1) + (r / s) ^ (k + 2) / (1 - r / s)
    with hB_def
  have hBnonneg : ∀ k, 0 ≤ B k := fun k => by
    have : (0:ℝ) < 1 - r / s := by linarith
    positivity
  have hSummable_r : Summable (fun k : ℕ => r ^ (k + 1)) := by
    have := (summable_geometric_of_lt_one hr0 hr1).mul_left r
    simpa [pow_succ, mul_comm] using this
  have hSummable_rs : Summable (fun k : ℕ => (r / s) ^ (k + 2)) := by
    have := (summable_geometric_of_lt_one hrs0 hrs1).mul_left ((r / s) ^ 2)
    simpa [pow_add, mul_comm] using this
  have hBsummable : Summable B := by
    have h1 : Summable (fun k => Real.sqrt 2 / 2 * r ^ (k + 1)) := hSummable_r.mul_left _
    have h2 : Summable (fun k => (r / s) ^ (k + 2) / (1 - r / s)) := by
      simpa [div_eq_mul_inv, mul_comm] using hSummable_rs.mul_right (1 - r / s)⁻¹
    simpa [hB_def] using h1.add h2
  -- `B k → 0`, so `B k < 1/2` eventually.
  have hBtendsto : Filter.Tendsto B Filter.atTop (nhds 0) := hBsummable.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hBtendsto (1 / 2) (by norm_num)
  have hNbound : ∀ k, N ≤ k → B k < 1 / 2 := by
    intro k hk
    have := hN k hk
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hBnonneg k)] at this
  -- the finite "bad" set: too close to `0`, or not yet small.
  set Bad : Set ℕ := F ∪ {k | k < N} with hBad_def
  have hBadFin : Bad.Finite := hFfin.union (Set.finite_Iio N)
  -- for the finitely many bad indices, bound by the actual maximum on `K`.
  have hMbound : ∀ k, ∃ M : ℝ, ∀ z ∈ K, ‖E k (c k) (z / a k) - 1‖ ≤ M := by
    intro k
    have h1 : ContinuousOn (fun z : ℂ => z / a k) K := by fun_prop
    have h2 : Continuous (E k (c k)) := by unfold E; fun_prop
    have hcont : ContinuousOn (fun z => ‖E k (c k) (z / a k) - 1‖) K :=
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
      -- `k` is neither in `F` nor small: apply the quantitative estimate.
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
      -- apply the quantitative bound on `G`
      have hGbound := norm_G_le k (c k) (z / a k) hρ0 hρ1 hzk
      have haffine : ‖c k - 1‖ / (k + 1) * ρ ^ (k + 1) ≤ Real.sqrt 2 / 2 * r ^ (k + 1) := by
        have h1 : ‖c k - 1‖ / (k + 1) ≤ Real.sqrt 2 / 2 * ‖a k‖ ^ (k + 1) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ) + 1)]
          calc ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (k + 1) * ‖a k‖ ^ (k + 1) := hc k
            _ = Real.sqrt 2 / 2 * ‖a k‖ ^ (k + 1) * ((k:ℝ) + 1) := by ring
        calc ‖c k - 1‖ / (k + 1) * ρ ^ (k + 1)
            ≤ (Real.sqrt 2 / 2 * ‖a k‖ ^ (k + 1)) * ρ ^ (k + 1) := by gcongr
          _ = Real.sqrt 2 / 2 * (‖a k‖ * ρ) ^ (k + 1) := by rw [mul_pow]; ring
          _ = Real.sqrt 2 / 2 * r ^ (k + 1) := by
              rw [hρ_def, mul_div_cancel₀ _ (ne_of_gt hakpos)]
      have htail : ρ ^ (k + 2) / (1 - ρ) ≤ (r / s) ^ (k + 2) / (1 - r / s) := by
        have h2 : (0:ℝ) < 1 - r / s := by linarith
        have h4 : 1 - r / s ≤ 1 - ρ := by linarith
        calc ρ ^ (k + 2) / (1 - ρ)
            ≤ (r / s) ^ (k + 2) / (1 - ρ) := by gcongr
          _ ≤ (r / s) ^ (k + 2) / (1 - r / s) :=
              div_le_div_of_nonneg_left (by positivity) h2 h4
      have hGbound2 : ‖G k (c k) (z / a k)‖ ≤ B k :=
        hGbound.trans (add_le_add haffine htail)
      have hGlt_half : ‖G k (c k) (z / a k)‖ < 1 / 2 :=
        lt_of_le_of_lt hGbound2 (hNbound k hakN)
      have hGle1 : ‖G k (c k) (z / a k)‖ ≤ 1 := by linarith
      have hzk𝔻 : z / a k ∈ 𝔻 := mem_𝔻_iff.mpr (lt_of_le_of_lt hzk hρ1)
      rw [E_eq_exp_G hzk𝔻]
      calc ‖Complex.exp (G k (c k) (z / a k)) - 1‖
          ≤ 2 * ‖G k (c k) (z / a k)‖ := Complex.norm_exp_sub_one_le hGle1
        _ ≤ 2 * B k := by linarith

/-! ## Convergence and holomorphy of the infinite product -/

variable {a : ℕ → ℂ} {n : ℕ → ℕ} {c : ℕ → ℂ}

/-- The individual bare factors are continuous on `𝔻`. -/
private theorem continuousOn_factor :
    ContinuousOn (fun z => E (n k) (c k) (z / a k)) 𝔻 := by
  have : ContinuousOn (fun z : ℂ => z / a k) 𝔻 := by fun_prop
  exact (by unfold E; fun_prop : Continuous (E (n k) (c k))).comp_continuousOn this

/-- **Locally uniform convergence of the Weierstrass product.**
Given an `M`-test bound (e.g. from `exists_Mtest_of_coeffSeq`, with `n := id`), the partial
products of the factors `E (n k) (c k) (· / a k)` converge locally uniformly on `𝔻`. -/
theorem hasProdLocallyUniformlyOn_factors
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k) :
    HasProdLocallyUniformlyOn (fun k z => E (n k) (c k) (z / a k))
      (fun z => ∏' k, E (n k) (c k) (z / a k)) 𝔻 := by
  have h𝔻open : IsOpen 𝔻 := Metric.isOpen_ball
  refine hasProdLocallyUniformlyOn_of_forall_compact h𝔻open (fun K hK hKcpt => ?_)
  obtain ⟨u, hu, hbound⟩ := hM K hK hKcpt
  have := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun k z => E (n k) (c k) (z / a k) - 1)
    hKcpt hu (Filter.Eventually.of_forall hbound)
    (fun k => ((continuousOn_factor (n := n) (c := c) (k := k)).mono hK).sub continuousOn_const)
  simpa using this

/-- **Holomorphy of the Weierstrass product.**
Under the same hypotheses, the infinite product is holomorphic on `𝔻`. -/
theorem holomorphicOn_tprod_factors
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k) :
    HolomorphicOn (fun z => ∏' k, E (n k) (c k) (z / a k)) := by
  have h𝔻open : IsOpen 𝔻 := Metric.isOpen_ball
  have hconv := (hasProdLocallyUniformlyOn_factors hM).tendstoLocallyUniformlyOn_finsetRange
  have hdiff : DifferentiableOn ℂ (fun z => ∏' k, E (n k) (c k) (z / a k)) 𝔻 := by
    refine hconv.differentiableOn (Filter.Eventually.of_forall fun N => ?_) h𝔻open
    have hglobal : Differentiable ℂ
        (fun z => ∏ i ∈ Finset.range N, E (n i) (c i) (z / a i)) := by
      unfold E; fun_prop
    exact hglobal.differentiableOn
  unfold HolomorphicOn AnalyticOnNhd
  intro z hz
  exact (hdiff.analyticAt (h𝔻open.mem_nhds hz))

/-- **Iterated derivatives pass to a locally uniform limit** of entire functions. -/
private theorem tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hFdiff : ∀ N, Differentiable ℂ (F N))
    (hconv : TendstoLocallyUniformlyOn F f Filter.atTop U)
    (m : ℕ) {x : ℂ} (hx : x ∈ U) :
    Filter.Tendsto (fun N => iteratedDeriv m (F N) x) Filter.atTop
      (nhds (iteratedDeriv m f x)) := by
  induction m generalizing F f with
  | zero => simpa using hconv.tendsto_at hx
  | succ m ih =>
      have hderivconv : TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) Filter.atTop U :=
        hconv.deriv (Filter.Eventually.of_forall fun N => (hFdiff N).differentiableOn) hU
      have hderivdiff : ∀ N, Differentiable ℂ ((deriv ∘ F) N) := fun N x =>
        ((analyticOnNhd_univ_iff_differentiable.mpr (hFdiff N)) x (Set.mem_univ x)).deriv
          |>.differentiableAt
      simp only [iteratedDeriv_succ']
      exact ih hderivdiff hderivconv

/-! ## The order of vanishing of a single factor -/

private theorem analyticOrderAt_E_one (n : ℕ) (c : ℂ) : analyticOrderAt (E n c) 1 = 1 := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => (1 : ℂ) - w) 1 := by fun_prop
  have hlin_deriv : deriv (fun w : ℂ => (1 : ℂ) - w) 1 ≠ 0 := by
    have hd : deriv (fun w : ℂ => (1 : ℂ) - w) = fun _ => (-1 : ℂ) := by
      funext w
      have hc' : HasDerivAt (fun _ : ℂ => (1 : ℂ)) (0 : ℂ) w := hasDerivAt_const w 1
      have hid' : HasDerivAt (fun w : ℂ => w) (1 : ℂ) w := hasDerivAt_id w
      have h1 : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) ((0 : ℂ) - 1) w := hc'.sub hid'
      simp [h1.deriv]
    rw [hd]; norm_num
  have hlin_order : analyticOrderAt (fun w : ℂ => (1 : ℂ) - w) 1 = 1 :=
    hlin.analyticOrderAt_eq_one_of_zero_deriv_ne_zero (by norm_num) hlin_deriv
  have hexp : AnalyticAt ℂ (fun w : ℂ => Complex.exp ((∑ k ∈ Finset.Icc 1 n, w ^ k / k)
      + c * w ^ (n + 1) / (n + 1))) 1 := by fun_prop
  have hexp_order : analyticOrderAt (fun w : ℂ => Complex.exp ((∑ k ∈ Finset.Icc 1 n, w ^ k / k)
      + c * w ^ (n + 1) / (n + 1))) 1 = 0 :=
    hexp.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
  have hE_eq : E n c = fun w : ℂ => (1 - w) * Complex.exp ((∑ k ∈ Finset.Icc 1 n, w ^ k / k)
      + c * w ^ (n + 1) / (n + 1)) := rfl
  have hmul := analyticOrderAt_mul hlin hexp
  rw [hlin_order, hexp_order, add_zero] at hmul
  rw [hE_eq]
  exact hmul

private theorem analyticOrderAt_E_div_self (n : ℕ) (c p : ℂ) (hp : p ≠ 0) :
    analyticOrderAt (fun w => E n c (w / p)) p = 1 := by
  have hg : AnalyticAt ℂ (fun w : ℂ => w / p) p := by fun_prop
  have hg' : deriv (fun w : ℂ => w / p) p ≠ 0 := by
    have hd : deriv (fun w : ℂ => w / p) = fun _ => (p : ℂ)⁻¹ := by
      funext w
      have hid' : HasDerivAt (fun w : ℂ => w) (1 : ℂ) w := hasDerivAt_id w
      have h1 : HasDerivAt (fun w : ℂ => w / p) (1 * p⁻¹) w := by
        simpa [div_eq_mul_inv] using hid'.mul_const p⁻¹
      simp [h1.deriv]
    rw [hd]; exact inv_ne_zero hp
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := E n c) hg hg'
  rw [show (fun w => E n c (w / p)) = (E n c) ∘ (fun w : ℂ => w / p) from rfl, hcomp]
  rw [div_self hp]
  exact analyticOrderAt_E_one n c

private theorem analyticOrderAt_factor (n : ℕ) (c p z : ℂ) (hp : p ≠ 0) :
    analyticOrderAt (fun w => E n c (w / p)) z = if z = p then 1 else 0 := by
  split_ifs with hzp
  · rw [hzp]; exact analyticOrderAt_E_div_self n c p hp
  · have hne : E n c (z / p) ≠ 0 := by
      rw [Ne, E_zero_iff, div_eq_one_iff_eq hp]
      exact hzp
    have hanalytic : AnalyticAt ℂ (fun w => E n c (w / p)) z := by
      have h1 : AnalyticAt ℂ (fun w : ℂ => w / p) z := by fun_prop
      have h2 : AnalyticAt ℂ (E n c) (z / p) := by unfold E; fun_prop
      exact AnalyticAt.comp (f := fun w : ℂ => w / p) (x := z) h2 h1
    exact hanalytic.analyticOrderAt_eq_zero.mpr hne

/-- The order of vanishing of a finite partial product at `z` is the number of factors
vanishing there. -/
private theorem analyticOrderAt_partialProduct_eq (a c : ℕ → ℂ) (n : ℕ → ℕ)
    (ha0 : ∀ k, a k ≠ 0) (z : ℂ) (K : ℕ) :
    analyticOrderAt (fun w => ∏ j ∈ Finset.range K, E (n j) (c j) (w / a j)) z
      = (((Finset.range K).filter (fun k => a k = z)).card : ℕ∞) := by
  induction K with
  | zero =>
      have heq : (fun w : ℂ => ∏ j ∈ Finset.range 0, E (n j) (c j) (w / a j))
          = fun _ : ℂ => (1 : ℂ) := by funext w; simp
      rw [heq]
      have hconst : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z := analyticAt_const
      simp [hconst.analyticOrderAt_eq_zero.mpr (by norm_num : (1 : ℂ) ≠ 0)]
  | succ K ih =>
      have heq : (fun w : ℂ => ∏ j ∈ Finset.range (K + 1), E (n j) (c j) (w / a j))
          = fun w => (∏ j ∈ Finset.range K, E (n j) (c j) (w / a j))
            * E (n K) (c K) (w / a K) :=
        funext fun w => Finset.prod_range_succ _ _
      rw [heq]
      have hK_analytic : AnalyticAt ℂ
          (fun w => ∏ j ∈ Finset.range K, E (n j) (c j) (w / a j)) z := by
        have : Differentiable ℂ (fun w => ∏ j ∈ Finset.range K, E (n j) (c j) (w / a j)) := by
          unfold E; fun_prop
        exact this.analyticAt z
      have hfactor_analytic : AnalyticAt ℂ (fun w => E (n K) (c K) (w / a K)) z := by
        unfold E; fun_prop
      have hmul := analyticOrderAt_mul hK_analytic hfactor_analytic
      rw [ih, analyticOrderAt_factor (n K) (c K) (a K) z (ha0 K)] at hmul
      have hcard : (((Finset.range (K + 1)).filter (fun k => a k = z)).card : ℕ∞)
          = (((Finset.range K).filter (fun k => a k = z)).card : ℕ∞)
            + (if z = a K then 1 else 0) := by
        rw [Finset.range_add_one, Finset.filter_insert]
        by_cases hcond : a K = z
        · rw [if_pos hcond, if_pos hcond.symm,
            Finset.card_insert_of_notMem (by simp)]
          push_cast; ring
        · rw [if_neg hcond, if_neg (Ne.symm hcond)]
          simp
      exact hmul.trans hcard.symm

/-! ## The zero divisor of the product -/

set_option maxHeartbeats 1000000 in
-- the head/tail split and `analyticOrderAt` bookkeeping in this proof involve enough nested
-- `Multipliable`/`HasProd` typeclass search that the default heartbeat limit is too tight.
/-- **Zero-divisor identification** (Section 3, proof of `prop:Zi`, Step 4).
At every point `z ∈ 𝔻`, the order of vanishing of the infinite product equals the sum of the
orders of vanishing of the (finitely many, by local finiteness of the enumeration) factors
vanishing there — which, since each `E (n k) (c k) (· / a k)` has a simple zero exactly at
`z = a k` (`E_zero_iff`), equals the number of `k` with `a k = z`.

Proof sketch: split the product at an index `K` beyond which no factor vanishes at `z` (finite
by the escape property applied to `s := ‖z‖ < 1`, or directly since `{k | a k = z}` is finite —
this needs a finiteness fact packaged alongside `exists_enum_of_effectiveDivisor`, e.g. via the
escape property with `s` slightly above `‖z‖`). The initial finite product has order exactly
`{k | a k = z}.ncard` (additivity of `analyticOrderNatAt` under finite products,
`analyticOrderAt_mul`/`analyticOrderNatAt_mul`, plus `E_zero_iff`); the tail product, by the
same `M`-test and `tprod_one_add_ne_zero_of_summable`-style non-vanishing criterion used in
`holomorphicOn_tprod_factors`, is holomorphic and non-vanishing near `z`, contributing order
`0`. -/
theorem isZeroDivisorOf_tprod_factors (ha0 : ∀ k, a k ≠ 0)
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k) (z : ℂ) (hz : z ∈ 𝔻) :
    analyticOrderNatAt (fun w => ∏' k, E (n k) (c k) (w / a k)) z = {k | a k = z}.ncard := by
  classical
  have h𝔻open : IsOpen 𝔻 := Metric.isOpen_ball
  -- an `M`-test bound at the single point `z`, giving a bound `N` beyond which no factor
  -- vanishes at `z`.
  obtain ⟨u, hu_sum, hu_bound⟩ := hM {z} (Set.singleton_subset_iff.mpr hz) isCompact_singleton
  have hu_bound' : ∀ k, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k := fun k => hu_bound k z rfl
  have hu_nonneg : ∀ k, 0 ≤ u k := fun k => (norm_nonneg _).trans (hu_bound' k)
  have hu0 : Filter.Tendsto u Filter.atTop (nhds 0) := hu_sum.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hu0 1 (by norm_num)
  have hsub : {k | a k = z} ⊆ {k | k < N} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    by_contra hknot
    simp only [Set.mem_setOf_eq, not_lt] at hknot
    have h1 : E (n k) (c k) (z / a k) = 0 := by
      rw [E_zero_iff, div_eq_one_iff_eq (ha0 k)]; exact hk.symm
    have h2 : ‖E (n k) (c k) (z / a k) - 1‖ = 1 := by rw [h1]; norm_num
    have h3 : (1 : ℝ) ≤ u k := h2 ▸ hu_bound' k
    have h4 := hN k hknot
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu_nonneg k)] at h4
    linarith
  -- an `M`-test bound for the shifted sequence.
  have hM_shift : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ i, ∀ w ∈ K, ‖E (n (i + N)) (c (i + N)) (w / a (i + N)) - 1‖ ≤ u i := by
    intro K hK hKcpt
    obtain ⟨uK, huK_sum, huK_bound⟩ := hM K hK hKcpt
    exact ⟨fun i => uK (i + N), (summable_nat_add_iff N).2 huK_sum,
      fun i w hw => huK_bound (i + N) w hw⟩
  -- the head/tail split of the infinite product on `𝔻`.
  have hsplit : ∀ w ∈ 𝔻, (∏ j ∈ Finset.range N, E (n j) (c j) (w / a j))
      * (∏' i, E (n (i + N)) (c (i + N)) (w / a (i + N))) = ∏' k, E (n k) (c k) (w / a k) := by
    intro w hw
    have hmul : Multipliable (fun k => E (n k) (c k) (w / a k)) :=
      ((hasProdLocallyUniformlyOn_factors hM).hasProd hw).multipliable
    have hshift_prod : HasProd (fun i => E (n (i + N)) (c (i + N)) (w / a (i + N)))
        (∏' i, E (n (i + N)) (c (i + N)) (w / a (i + N))) :=
      (hasProdLocallyUniformlyOn_factors hM_shift).hasProd hw
    have hfull_prod : HasProd (fun k => E (n k) (c k) (w / a k))
        ((∏ j ∈ Finset.range N, E (n j) (c j) (w / a j))
          * ∏' i, E (n (i + N)) (c (i + N)) (w / a (i + N))) :=
      hshift_prod.prod_range_mul
    exact hfull_prod.unique hmul.hasProd
  have heq_nhds : (fun w => (∏ j ∈ Finset.range N, E (n j) (c j) (w / a j))
      * ∏' i, E (n (i + N)) (c (i + N)) (w / a (i + N)))
      =ᶠ[nhds z] (fun w => ∏' k, E (n k) (c k) (w / a k)) := by
    filter_upwards [h𝔻open.mem_nhds hz] with w hw using hsplit w hw
  have horder_eq := analyticOrderAt_congr heq_nhds
  -- the tail is holomorphic and non-vanishing at `z`.
  have htail_analytic : AnalyticAt ℂ
      (fun w => ∏' i, E (n (i + N)) (c (i + N)) (w / a (i + N))) z :=
    holomorphicOn_tprod_factors (n := fun i => n (i + N)) (c := fun i => c (i + N))
      (a := fun i => a (i + N)) hM_shift z hz
  obtain ⟨u', hu'_sum, hu'_bound⟩ :=
    hM_shift {z} (Set.singleton_subset_iff.mpr hz) isCompact_singleton
  have hu'_bound' : ∀ i, ‖E (n (i + N)) (c (i + N)) (z / a (i + N)) - 1‖ ≤ u' i :=
    fun i => hu'_bound i z rfl
  have htail_ne : (∏' i, E (n (i + N)) (c (i + N)) (z / a (i + N))) ≠ 0 := by
    have hne1 : ∀ i, (1 : ℂ) + (E (n (i + N)) (c (i + N)) (z / a (i + N)) - 1) ≠ 0 := by
      intro i
      have : (1 : ℂ) + (E (n (i + N)) (c (i + N)) (z / a (i + N)) - 1)
          = E (n (i + N)) (c (i + N)) (z / a (i + N)) := by ring
      rw [this, Ne, E_zero_iff, div_eq_one_iff_eq (ha0 (i + N))]
      intro hcontra
      exact absurd (hsub hcontra.symm) (by simp)
    have hsummable : Summable (fun i => ‖E (n (i + N)) (c (i + N)) (z / a (i + N)) - 1‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) hu'_bound' hu'_sum
    have hne_prod := tprod_one_add_ne_zero_of_summable hne1 hsummable
    have hfun_eq : (fun i => (1 : ℂ) + (E (n (i + N)) (c (i + N)) (z / a (i + N)) - 1))
        = fun i => E (n (i + N)) (c (i + N)) (z / a (i + N)) := by
      funext i; ring
    rwa [hfun_eq] at hne_prod
  have htail_order : analyticOrderAt
      (fun w => ∏' i, E (n (i + N)) (c (i + N)) (w / a (i + N))) z = 0 :=
    htail_analytic.analyticOrderAt_eq_zero.mpr htail_ne
  have hpartial_analytic : AnalyticAt ℂ
      (fun w => ∏ j ∈ Finset.range N, E (n j) (c j) (w / a j)) z := by
    have : Differentiable ℂ (fun w => ∏ j ∈ Finset.range N, E (n j) (c j) (w / a j)) := by
      unfold E; fun_prop
    exact this.analyticAt z
  have hmul_order := analyticOrderAt_mul hpartial_analytic htail_analytic
  rw [htail_order, add_zero] at hmul_order
  have horder_final : analyticOrderAt (fun w => ∏' k, E (n k) (c k) (w / a k)) z
      = analyticOrderAt (fun w => ∏ j ∈ Finset.range N, E (n j) (c j) (w / a j)) z :=
    horder_eq.symm.trans hmul_order
  have hcard_eq : (((Finset.range N).filter (fun k => a k = z)).card : ℕ)
      = {k | a k = z}.ncard := by
    have hset_eq : {k | a k = z} = ↑((Finset.range N).filter (fun k => a k = z)) := by
      ext k
      simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩
    rw [hset_eq, Set.ncard_coe_finset]
  unfold analyticOrderNatAt
  rw [horder_final, analyticOrderAt_partialProduct_eq a c n ha0 z N]
  rw [← hcard_eq]
  simp

/-! ## Passing Taylor coefficients to the limit -/

/-- **Stabilization of Taylor coefficients** (Section 3, proof of `prop:Zi`, Step 2).
For each fixed degree `m`, once `n k > m` the `m`-th Taylor coefficient of the infinite
product agrees with that of the `(k+1)`-st partial product — hence, combined with
`exists_coeffSeq`'s Gaussian-integer forcing and `taylorCoeff_mul_E_eq_of_le`, every Taylor
coefficient of the limit lies in `ℤ[i]`.

Proof sketch: write the infinite product as the `(k+1)`-st partial product times the tail
`∏' j ≥ k+1, E (n j) (c j) (·/a j)`; by `taylorCoeff_mul_E_eq_of_le` applied with `n := n k`
(needs `m ≤ n k`) it suffices that the tail is analytic at `0` with value `1` there — the
value-`1` part holds since every tail factor is `1` at `0` (`E_zero`) and the tail converges
locally uniformly (by the same `M`-test argument, reindexed), and analyticity follows as in
`holomorphicOn_tprod_factors`. -/
theorem taylorCoeff_tprod_factors_eq_partial (hnmono : StrictMono n)
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k)
    (m k : ℕ) (hk : m < n k) :
    taylorCoeff (fun z => ∏' j, E (n j) (c j) (z / a j)) m
      = taylorCoeff (fun z => ∏ j ∈ Finset.range (k + 1), E (n j) (c j) (z / a j)) m := by
  have h𝔻open : IsOpen 𝔻 := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ 𝔻 := by simp [mem_𝔻_iff]
  -- the partial products of degree `≥ k+1` agree with the `(k+1)`-st one at degree `m`.
  have hstable : ∀ K (hK : k + 1 ≤ K),
      taylorCoeff (fun z => ∏ j ∈ Finset.range K, E (n j) (c j) (z / a j)) m
        = taylorCoeff (fun z => ∏ j ∈ Finset.range (k + 1), E (n j) (c j) (z / a j)) m := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base => rfl
    | succ K hK ih =>
        have hanalytic : AnalyticAt ℂ
            (fun z => ∏ j ∈ Finset.range K, E (n j) (c j) (z / a j)) 0 := by
          have : Differentiable ℂ (fun z => ∏ j ∈ Finset.range K, E (n j) (c j) (z / a j)) := by
            unfold E; fun_prop
          exact this.analyticAt 0
        have hmnK : m ≤ n K := by
          have hlt : n k < n K := hnmono (by omega)
          omega
        have hfun_eq : (fun z => ∏ j ∈ Finset.range (K + 1), E (n j) (c j) (z / a j))
            = fun z => (∏ j ∈ Finset.range K, E (n j) (c j) (z / a j)) * E (n K) (c K) (z / a K) :=
          funext fun z => Finset.prod_range_succ _ _
        rw [hfun_eq, taylorCoeff_mul_E_eq_of_le hanalytic hmnK]
        exact ih
  -- the corresponding `iteratedDeriv`s are eventually constant.
  have hne : (Nat.factorial m : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hstable_iter : ∀ K (hK : k + 1 ≤ K),
      iteratedDeriv m (fun z => ∏ j ∈ Finset.range K, E (n j) (c j) (z / a j)) 0
        = iteratedDeriv m (fun z => ∏ j ∈ Finset.range (k + 1), E (n j) (c j) (z / a j)) 0 := by
    intro K hK
    have heq := hstable K hK
    unfold taylorCoeff at heq
    have heq2 := congrArg (· * (Nat.factorial m : ℂ)) heq
    simpa [div_mul_cancel₀ _ hne] using heq2
  -- pass to the limit.
  have hFdiff : ∀ N,
      Differentiable ℂ (fun z => ∏ j ∈ Finset.range N, E (n j) (c j) (z / a j)) := by
    intro N; unfold E; fun_prop
  have hconv : TendstoLocallyUniformlyOn
      (fun N z => ∏ j ∈ Finset.range N, E (n j) (c j) (z / a j))
      (fun z => ∏' j, E (n j) (c j) (z / a j)) Filter.atTop 𝔻 :=
    (hasProdLocallyUniformlyOn_factors hM).tendstoLocallyUniformlyOn_finsetRange
  have htendsto := tendsto_iteratedDeriv_of_tendstoLocallyUniformlyOn h𝔻open hFdiff hconv m h0
  have heventually : (fun K => iteratedDeriv m
      (fun z => ∏ j ∈ Finset.range K, E (n j) (c j) (z / a j)) 0) =ᶠ[Filter.atTop]
      (fun _ => iteratedDeriv m
        (fun z => ∏ j ∈ Finset.range (k + 1), E (n j) (c j) (z / a j)) 0) := by
    filter_upwards [Filter.eventually_ge_atTop (k + 1)] with K hK using hstable_iter K hK
  have hlim_eq : iteratedDeriv m (fun z => ∏' j, E (n j) (c j) (z / a j)) 0
      = iteratedDeriv m
        (fun z => ∏ j ∈ Finset.range (k + 1), E (n j) (c j) (z / a j)) 0 :=
    tendsto_nhds_unique htendsto (tendsto_const_nhds.congr' heventually.symm)
  unfold taylorCoeff
  rw [hlim_eq]

end Weierstrass
