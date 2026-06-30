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
  sorry

/-- **Lemma `lem:structure` (i).** `E_n(0;c) = 1`. -/
theorem E_zero (n : ℕ) (c : ℂ) : E n c 0 = 1 := by
  sorry

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
