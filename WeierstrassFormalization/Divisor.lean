/-
Copyright (c) 2026 Jon Bannon, David Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, David Feldman
-/
import WeierstrassFormalization.Basic

/-!
# Effective divisors on the disk

Formalizes the paper's notion (Introduction, paragraph 3) of an *effective
divisor* on `𝔻`: a locally finite formal sum `D = Σ_{a ∈ S} m_a [a]` with
non-negative integer multiplicities over a discrete subset `S ⊆ 𝔻`.

We represent `D` directly by its multiplicity function `mult : ℂ → ℕ`
(zero outside the support), with the discreteness/local-finiteness
condition expressed as: every compact subset of `𝔻` meets the support in
only finitely many points.
-/

namespace Weierstrass

/-- An effective divisor on the open unit disk: a multiplicity function
with locally finite support inside `𝔻`. -/
structure EffectiveDivisor where
  /-- The multiplicity assigned to each point. -/
  mult : ℂ → ℕ
  /-- Points outside `𝔻` carry multiplicity zero. -/
  mult_eq_zero_of_not_mem_𝔻 : ∀ z ∉ 𝔻, mult z = 0
  /-- The support is discrete in `𝔻`: every compact `K ⊆ 𝔻` meets it finitely. -/
  finite_inter_compact : ∀ K ⊆ 𝔻, IsCompact K → {z ∈ K | mult z ≠ 0}.Finite

namespace EffectiveDivisor

/-- The support of an effective divisor, `S = {a : m_a ≠ 0}`. -/
def support (D : EffectiveDivisor) : Set ℂ := {z | D.mult z ≠ 0}

/-- `D` is invariant under complex conjugation: `m_{\bar a} = m_a` for all `a`
(Introduction; hypothesis of Theorem `thm:main`). -/
def ConjInvariant (D : EffectiveDivisor) : Prop :=
  ∀ z, D.mult (starRingEnd ℂ z) = D.mult z

end EffectiveDivisor

/-- `D` is *the zero divisor* of `f`: the multiplicity at every point of `𝔻`
equals the order of vanishing of `f` there. This is the relation expressed
throughout the paper by phrases such as "`D` is the zero divisor of a
holomorphic function `f`". -/
def IsZeroDivisorOf (D : EffectiveDivisor) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ 𝔻, D.mult z = analyticOrderNatAt f z

end Weierstrass
