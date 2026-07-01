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
  sorry

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
      change taylorCoeff (fun _ => (1:ℂ)) 0 = ((1 : GaussianInt) : ℂ)
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

/-! ## The zero divisor of the product -/

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
theorem isZeroDivisorOf_tprod_factors
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k) (z : ℂ) (hz : z ∈ 𝔻) :
    analyticOrderNatAt (fun w => ∏' k, E (n k) (c k) (w / a k)) z = {k | a k = z}.ncard := by
  sorry

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
theorem taylorCoeff_tprod_factors_eq_partial
    (hM : ∀ K ⊆ 𝔻, IsCompact K → ∃ u : ℕ → ℝ, Summable u ∧
      ∀ k, ∀ z ∈ K, ‖E (n k) (c k) (z / a k) - 1‖ ≤ u k)
    (m k : ℕ) (hk : m < n k) :
    taylorCoeff (fun z => ∏' j, E (n j) (c j) (z / a j)) m
      = taylorCoeff (fun z => ∏ j ∈ Finset.range (k + 1), E (n j) (c j) (z / a j)) m := by
  sorry

end Weierstrass
