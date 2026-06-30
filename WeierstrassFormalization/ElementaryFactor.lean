/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Basic

/-!
# Modified elementary factors

Formalizes Section 2 of the paper: the modified Weierstrass elementary
factor `E_n(w; c)` and the structural Lemma `lem:structure`.
-/

namespace Weierstrass

open Complex

/-- The modified elementary factor of order `n` with parameter `c`,
\[
  E_n(w;\,c) = (1-w)\exp\Bigl(\sum_{k=1}^{n}\frac{w^k}{k} +
    \frac{c\,w^{n+1}}{n+1}\Bigr).
\]
For `c = 1` this is the classical Weierstrass elementary factor. -/
noncomputable def E (n : ℕ) (c w : ℂ) : ℂ :=
  (1 - w) * Complex.exp ((∑ k ∈ Finset.Icc 1 n, w ^ k / k) + c * w ^ (n + 1) / (n + 1))

/-- The exponent `G_n(w;c)` from \eqref{eq:Gdef}, valid for `w ∈ 𝔻`:
\[
  G_n(w;\,c) = \frac{(c-1)\,w^{n+1}}{n+1} - \sum_{k=n+2}^{\infty}\frac{w^k}{k}.
\]
-/
noncomputable def G (n : ℕ) (c w : ℂ) : ℂ :=
  (c - 1) * w ^ (n + 1) / (n + 1) - ∑' k : ℕ, if k ≥ n + 2 then w ^ k / k else 0

/-- **Lemma (Structure of the modified factor), Eq. (2.3)–(2.4).**
On the disk, `E_n(w;c) = exp(G_n(w;c))`. -/
theorem E_eq_exp_G {n : ℕ} {c w : ℂ} (hw : w ∈ 𝔻) :
    E n c w = Complex.exp (G n c w) := by
  have hw' : ‖w‖ < 1 := mem_𝔻_iff.mp hw
  have hw1 : w ≠ 1 := by
    intro h; rw [h, norm_one] at hw'; exact lt_irrefl 1 hw'
  set f0 : ℕ → ℂ := fun k => w ^ k / k with hf0_def
  have hSum0 : HasSum f0 (-Complex.log (1 - w)) := Complex.hasSum_taylorSeries_neg_log hw'
  have hSummable0 : Summable f0 := hSum0.summable
  have htsum0 : ∑' k, f0 k = -Complex.log (1 - w) := hSum0.tsum_eq
  have hf00 : f0 0 = 0 := by simp [hf0_def]
  -- the tail sum `T` agrees with the shifted tsum `∑' i, f0 (i + (n+2))`
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
  -- split the full series at `n + 2`
  have hsplit : (∑ i ∈ Finset.range (n + 2), f0 i) + ∑' i, f0 (i + (n + 2)) = ∑' i, f0 i :=
    Summable.sum_add_tsum_nat_add (n + 2) hSummable0
  have hrange : ∑ i ∈ Finset.range (n + 2), f0 i
      = (∑ k ∈ Finset.Icc 1 n, f0 k) + f0 (n + 1) := by
    have hLHS : ∑ i ∈ Finset.range (n + 2), f0 i
        = (∑ k ∈ Finset.range n, f0 (k + 1)) + f0 (n + 1) := by
      rw [show n + 2 = n + 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ', hf00,
        add_zero]
    have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hRHS : ∑ k ∈ Finset.Icc 1 n, f0 k = ∑ k ∈ Finset.range n, f0 (k + 1) := by
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel]
      exact Finset.sum_congr rfl (fun k _ => by rw [add_comm])
    rw [hLHS, hRHS]
  have hkey : (∑ k ∈ Finset.Icc 1 n, f0 k) + f0 (n + 1)
      + (∑' k : ℕ, if k ≥ n + 2 then f0 k else 0) = -Complex.log (1 - w) := by
    rw [hT_eq, ← hrange, hsplit, htsum0]
  have hB_eq : G n c w = Complex.log (1 - w)
      + ((∑ k ∈ Finset.Icc 1 n, w ^ k / k) + c * w ^ (n + 1) / (n + 1)) := by
    have hf0_succ : f0 (n + 1) = w ^ (n + 1) / (n + 1) := by
      simp only [hf0_def]; push_cast; ring
    rw [hf0_succ] at hkey
    unfold G
    field_simp at hkey ⊢
    linear_combination -hkey
  rw [hB_eq, Complex.exp_add, Complex.exp_log (sub_ne_zero.mpr hw1.symm)]
  rfl

/-- **Lemma `lem:structure` (i).** `E_n(0;c) = 1`. -/
theorem E_zero (n : ℕ) (c : ℂ) : E n c 0 = 1 := by
  unfold E
  have hsum : ∑ k ∈ Finset.Icc 1 n, (0 : ℂ) ^ k / k = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk
    simp [zero_pow (Nat.one_le_iff_ne_zero.mp hk.1)]
  simp [hsum]

/-- **Lemma `lem:structure` (ii).** The Taylor coefficients of degree
`1, …, n` of `E_n(·;c)` vanish, independently of `c`. -/
theorem taylorCoeff_E_eq_zero {n : ℕ} {c : ℂ} {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    taylorCoeff (E n c) m = 0 := by
  sorry

/-- **Lemma `lem:structure` (iii).** The Taylor coefficient of degree `n+1`
of `E_n(·;c)` is `(c-1)/(n+1)`, affine in `c` with slope `1/(n+1)`. -/
theorem taylorCoeff_E_succ (n : ℕ) (c : ℂ) :
    taylorCoeff (E n c) (n + 1) = (c - 1) / (n + 1) := by
  sorry

/-- **Lemma `lem:structure` (iv).** `E_n(·;c)` is nowhere vanishing on `𝔻`. -/
theorem E_ne_zero {n : ℕ} {c w : ℂ} (hw : w ∈ 𝔻) : E n c w ≠ 0 := by
  sorry

/-- **Lemma `lem:structure` (v).** As an entire function, `E_n(·;c)` has a
simple zero at `w = 1` and no other zeros. -/
theorem E_zero_iff {n : ℕ} {c w : ℂ} : E n c w = 0 ↔ w = 1 := by
  sorry

end Weierstrass
