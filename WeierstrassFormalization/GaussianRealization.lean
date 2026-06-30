/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Divisor
import WeierstrassFormalization.AffineControl

/-!
# Gaussian-integer realization

Formalizes Theorem `prop:Zi`: every effective divisor on `𝔻` is the zero
divisor of a holomorphic function on `𝔻` with Taylor coefficients in the
Gaussian integers `ℤ[i]`.
-/

namespace Weierstrass

/-- `f` has Taylor coefficients in the Gaussian integers `ℤ[i]`. -/
def HasGaussianIntCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ z : GaussianInt, taylorCoeff f n = (z : ℂ)

/-- **Theorem `prop:Zi` (Gaussian-integer realization).** Every effective
divisor on `𝔻` is the zero divisor of a holomorphic function on `𝔻` with
Taylor coefficients in `ℤ[i]`. -/
theorem exists_holomorphic_gaussianInt_coeffs_of_effectiveDivisor (D : EffectiveDivisor) :
    ∃ f : ℂ → ℂ, HolomorphicOn f ∧ IsZeroDivisorOf D f ∧ HasGaussianIntCoeffs f := by
  sorry

end Weierstrass
