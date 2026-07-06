/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import Mathlib

/-!
# Basic definitions

Common notation and definitions shared across the formalization of
*Integer Coefficients Power Series with Prescribed Zero Sets* (Bannon–Feldman).

This file fixes:
* `𝔻`, the open unit disk in `ℂ`;
* `HolomorphicOn`, holomorphy on `𝔻` (analyticity at every point of `𝔻`);
* `taylorCoeff f n`, the `n`-th Taylor coefficient of `f` at the origin,
  i.e. `[z^n] f` in the paper's notation.
-/

namespace Weierstrass

/-- The open unit disk `𝔻 = {z ∈ ℂ : |z| < 1}`. -/
def 𝔻 : Set ℂ := Metric.ball (0 : ℂ) 1

lemma mem_𝔻_iff {z : ℂ} : z ∈ 𝔻 ↔ ‖z‖ < 1 := by
  simp [𝔻, Metric.mem_ball, dist_eq_norm]

/-- `f` is holomorphic on `𝔻`, i.e. analytic at every point of the open unit disk. -/
def HolomorphicOn (f : ℂ → ℂ) : Prop := AnalyticOnNhd ℂ f 𝔻

/-- The `n`-th Taylor coefficient of `f` at the origin, `[z^n] f`,
defined via the `n`-th iterated derivative: `[z^n] f = f⁽ⁿ⁾(0) / n!`. -/
noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / (Nat.factorial n : ℂ)

end Weierstrass
