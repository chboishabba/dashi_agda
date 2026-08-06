module DASHI.Physics.Common.ScaledFilteredEstimateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Cardy, "Scaling and Renormalization in Statistical Physics".
-- DOI: 10.1017/CBO9781316036440.
-- Roger Temam, "Navier--Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
-- Tadeusz Balaban, "Propagators and Renormalization Transformations for
-- Lattice Gauge Theories. II". DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
-- Package exact scale representation, rescaling and loss-corrected transport
-- algebra shared by Galerkin, RG and associated-graded filtrations.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

record ScaleRepresentation : Set where
  constructor scaleRepresentation
  field
    rawQuantity : ℚ
    levelSpacing : ℚ
    physicalQuantity : ℚ
    representsPhysical : rawQuantity ≡ levelSpacing * physicalQuantity

open ScaleRepresentation public

rescaleRepresentation : ℚ → ScaleRepresentation → ScaleRepresentation
rescaleRepresentation factor representation =
  scaleRepresentation
    (factor * rawQuantity representation)
    (factor * levelSpacing representation)
    (physicalQuantity representation)
    proof
  where
  proof :
    factor * rawQuantity representation
    ≡ (factor * levelSpacing representation) * physicalQuantity representation
  proof rewrite representsPhysical representation =
    ℚRing.solve-∀ factor (levelSpacing representation) (physicalQuantity representation)

rescalingPreservesPhysicalQuantity :
  ∀ factor representation →
  physicalQuantity (rescaleRepresentation factor representation)
  ≡ physicalQuantity representation
rescalingPreservesPhysicalQuantity factor representation = refl

record FilteredTransportStep : Set where
  constructor filteredTransportStep
  field
    coarseRaw : ℚ
    fineRaw : ℚ
    transferFactor : ℚ
    couplingLoss : ℚ
    remainderLoss : ℚ
    exactTransportBalance :
      coarseRaw ≡ transferFactor * fineRaw + couplingLoss + remainderLoss

open FilteredTransportStep public

lossCorrectedTransportExact :
  ∀ step →
  coarseRaw step - couplingLoss step - remainderLoss step
  ≡ transferFactor step * fineRaw step
lossCorrectedTransportExact step
  rewrite exactTransportBalance step =
  ℚRing.solve-∀
    (transferFactor step) (fineRaw step)
    (couplingLoss step) (remainderLoss step)

record ScaledFilteredLevel : Set where
  constructor scaledFilteredLevel
  field
    filtrationLevel : ℚ
    representedScale : ScaleRepresentation
    levelDefect : ℚ

record ScaledFilteredBoundary : Set where
  constructor scaledFilteredBoundary
  field
    finiteLevelIdentityProvesLimitSurvival : Set
    finiteLevelIdentityDoesNotProveLimitSurvival :
      finiteLevelIdentityProvesLimitSurvival → Set
    vanishingOrSummableDefectStillRequired : Set
    vanishingOrSummableDefectStillRequiredWitness :
      vanishingOrSummableDefectStillRequired

canonicalScaledFilteredBoundary : ScaledFilteredBoundary
canonicalScaledFilteredBoundary =
  scaledFilteredBoundary
    ⊥ (λ impossible → ⊥)
    ⊤ tt
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤; tt)
