{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSYanRadulescuStationaryPressureExact where

-- Weiping Yan and Vicentiu D. Radulescu (2021),
-- DOI 10.1007/s12215-020-00540-3, Eq. (1.1), Eq. (1.3),
-- Theorem 1.1 and Corollary 1.1.
--
-- Their problem is STEADY, FORCED, bounded-domain Navier-Stokes; this is
-- not an unforced time-dependent Clay A/B continuation result.
--
-- The formal divergence of the steady forced equation reads:
--     Delta(P) = div(f) - sum_ij (d_i U_j)(d_j U_i),
-- when div(U)=0 and the differentiations are justified.
-- The source's displayed Eq. (1.3) omits div(f) even though Eq. (1.1)
-- allows forcing f. Its abbreviated pressure law therefore requires
-- div(f)=0 or an independently justified compensating condition.
--
-- This module keeps the arithmetic owner / analytic witness external,
-- instead of assuming the displayed formula is universally valid.
-- Derivation of the scalar identity from the PDE is a Mathlib-facing task.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record SameSourceForcedPressure
    (PhysicalSource Scalar : Set)
    (selectedSource : PhysicalSource)
    (pressureLaplacian forceDivergence convectiveContraction : Scalar)
    (_-_ : Scalar → Scalar → Scalar)
    (PressureLaplacianBelongsTo : PhysicalSource → Scalar → Set)
    (ForceDivergenceBelongsTo : PhysicalSource → Scalar → Set)
    (ContractionBelongsTo : PhysicalSource → Scalar → Set) : Set where
  field
    pressureIsSourceAttached :
      PressureLaplacianBelongsTo selectedSource pressureLaplacian
    forceIsSourceAttached :
      ForceDivergenceBelongsTo selectedSource forceDivergence
    contractionIsSourceAttached :
      ContractionBelongsTo selectedSource convectiveContraction
    exactForcedPressureEquation :
      pressureLaplacian ≡ (forceDivergence - convectiveContraction)

-- Suppressing the forcing-divergence term is a COROLLARY of its
-- vanishing, not a silent rewrite of a general forced equation.
sourcePressureOfDivergenceFreeForce :
  {PhysicalSource Scalar : Set} →
  {selectedSource : PhysicalSource} →
  {lap divf contraction zero : Scalar} →
  (_-_ : Scalar → Scalar → Scalar) →
  {PressureAttached : PhysicalSource → Scalar → Set} →
  {ForceAttached : PhysicalSource → Scalar → Set} →
  {ContractionAttached : PhysicalSource → Scalar → Set} →
  SameSourceForcedPressure PhysicalSource Scalar selectedSource
    lap divf contraction _-_
    PressureAttached ForceAttached ContractionAttached →
  divf ≡ zero →
  lap ≡ (zero - contraction)
sourcePressureOfDivergenceFreeForce {contraction = contraction} _-_ witness hZero =
  trans
    (SameSourceForcedPressure.exactForcedPressureEquation witness)
    (cong (λ d → _-_ d contraction) hZero)
