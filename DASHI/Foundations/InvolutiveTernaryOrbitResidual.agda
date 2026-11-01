module DASHI.Foundations.InvolutiveTernaryOrbitResidual where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List)

import DASHI.Foundations.InvolutiveTernaryDynamics as ITD

------------------------------------------------------------------------
-- Orbit eigenstates.
--
-- A fixed point is the period-one case already carried by ITD.FixedPoint.
-- This record exposes finite controlled cycles without assuming that every
-- application has a canonical period or a globally minimising orbit.

record ControlledOrbit (D : ITD.InvolutiveDynamics) : Set₁ where
  constructor orbit
  field
    states : List (ITD.State D)
    controls : List (ITD.Control D)
    closes : Set

open ControlledOrbit public

record LowActionOrbit
  (D : ITD.InvolutiveDynamics)
  (A : ITD.EvenAction D) : Set₁ where
  constructor lowActionOrbit
  field
    carrierOrbit : ControlledOrbit D
    meanActionNumerator : Nat
    orbitActionBound : Nat
    boundWitness : Set

open LowActionOrbit public

------------------------------------------------------------------------
-- Equivariant residual comparison.
--
-- Residual is intentionally abstract.  Applications may instantiate it as
-- ternary cancellation, group difference, chart defect, prediction error,
-- curvature defect, or another comparison.  The only generic requirement is
-- compatibility with the involutions on state, reference, and residual.

record EquivariantResidual
  (D : ITD.InvolutiveDynamics) : Set₁ where
  field
    Reference : Set
    referenceι : Reference → Reference
    referenceι-involutive : ∀ e → referenceι (referenceι e) ≡ e

    Residual : Set
    residualι : Residual → Residual
    residualι-involutive : ∀ r → residualι (residualι r) ≡ r

    compare : ITD.State D → Reference → Residual

    compare-equivariant :
      ∀ s e →
      compare (ITD.stateι D s) (referenceι e) ≡
      residualι (compare s e)

open EquivariantResidual public

record ResidualBaseline
  (D : ITD.InvolutiveDynamics)
  (R : EquivariantResidual D) : Set₁ where
  field
    baseline : Reference R
    baseline-fixed : referenceι R baseline ≡ baseline
    vanishesAt : ITD.State D → Set

open ResidualBaseline public

------------------------------------------------------------------------
-- Cross-application boundary.

record OrbitResidualBoundary : Set where
  constructor boundary
  field
    fixedPointIsPeriodOneReading : Bool
    orbitMinimalityRequiresInstantiation : Bool
    residualOperationRequiresInstantiation : Bool
    physicalInterpretationPromoted : Bool

canonicalBoundary : OrbitResidualBoundary
canonicalBoundary = boundary true true true false
