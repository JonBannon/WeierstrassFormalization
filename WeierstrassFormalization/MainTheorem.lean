/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.GaussianRealization

/-!
# Main theorem

Formalizes Theorem `thm:main`: an effective divisor on `𝔻` is the zero
divisor of a holomorphic function on `𝔻` with integer Taylor coefficients
if and only if it is invariant under complex conjugation.
-/

namespace Weierstrass

/-- `f` has Taylor coefficients in `ℤ`. -/
def HasIntCoeffs (f : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ k : ℤ, taylorCoeff f n = (k : ℂ)

/-- **Theorem `thm:main`.** An effective divisor `D` on `𝔻` is the zero
divisor of a holomorphic function on `𝔻` with Taylor coefficients in `ℤ`
if and only if `D` is invariant under complex conjugation. -/
theorem exists_holomorphic_int_coeffs_iff_conjInvariant (D : EffectiveDivisor) :
    (∃ f : ℂ → ℂ, HolomorphicOn f ∧ IsZeroDivisorOf D f ∧ HasIntCoeffs f) ↔
      D.ConjInvariant := by
  sorry

end Weierstrass
