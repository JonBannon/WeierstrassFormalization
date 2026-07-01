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

/-- **Inductive coefficient forcing** (Section 3, proof of `prop:Zi`, Step 1's Claim).
Given points `a : ℕ → ℂ` with `a k ≠ 0`, there is a sequence of correction constants
`c : ℕ → ℂ` such that, writing `P N := partialProduct a c N`:
* every Taylor coefficient of `P N` at degree `N` is (the image of) a Gaussian integer
  (this is the coefficient exactly forced at stage `N`, by rounding to the nearest element
  of `ℤ[i]`; degrees `< N` were already forced, and stay unchanged, at earlier stages by
  `taylorCoeff_mul_E_eq_of_le`);
* the rounding error is controlled: `‖c k - 1‖ ≤ (√2/2) * (k+1) * ‖a k‖ ^ (k+1)`.

Proof sketch: induction on `N`, using `exists_c_taylorCoeff_mul_E_succ_eq` at each step with
`h := P N`, target `:= (nearestGaussianInt (taylorCoeff (P N) (N+1)) : ℂ)`, to choose `c N`
forcing `taylorCoeff (P (N+1)) (N+1) = (nearestGaussianInt (taylorCoeff (P N) (N+1)) : ℂ)`;
then read off the bound on `‖c N - 1‖` from the affine formula in `taylorCoeff_mul_E_succ`
combined with `norm_sub_nearestGaussianInt_le`. The induction also needs, at each step,
`AnalyticAt ℂ (P N) 0` and `P N 0 = 1`, both immediate from `E_zero`/`analyticAt_auxQ`-style
facts about finite products of `E`. -/
theorem exists_coeffSeq (a : ℕ → ℂ) (ha0 : ∀ k, a k ≠ 0) :
    ∃ c : ℕ → ℂ,
      (∀ N, ∃ z : GaussianInt, taylorCoeff (partialProduct a c N) N = z) ∧
      ∀ k, ‖c k - 1‖ ≤ Real.sqrt 2 / 2 * (k + 1) * ‖a k‖ ^ (k + 1) := by
  sorry

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
  sorry

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
