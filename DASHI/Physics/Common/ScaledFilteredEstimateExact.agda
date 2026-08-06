module DASHI.Physics.Common.ScaledFilteredEstimateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Cardy,
-- "Scaling and Renormalization in Statistical Physics",
-- Cambridge Lecture Notes in Physics 5, 1996.
-- DOI: 10.1017/CBO9781316036440.
--
-- Roger Temam,
-- "Navier--Stokes Equations: Theory and Numerical Analysis",
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II", Communications in Mathematical Physics 96 (1984), 223--250.
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
--
-- Package the exact common algebra behind:
--
--   * Fourier/Galerkin levels and their selected diagonal limits;
--   * lattice/physical Yang--Mills gap normalization;
--   * filtered/associated-graded carrier levels.
--
-- A raw quantity represents one physical quantity only together with its
-- level spacing.  Simultaneously scaling the raw quantity and spacing leaves
-- the represented physical quantity unchanged.  Physical compatibility and
-- convergence remain separate producers.
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
    representsPhysical :
      rawQuantity ≡ levelSpacing * physicalQuantity

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
    ≡ (factor * levelSpacing representation)
      * physicalQuantity representation
  proof rewrite representsPhysical representation =
    ℚRing.solve-∀
      factor
      (levelSpacing representation)
      (physicalQuantity representation)

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
      coarseRaw
      ≡ transferFactor * fineRaw + couplingLoss + remainderLoss

open FilteredTransportStep public

lossCorrectedTransportExact :
  ∀ step →
  coarseRaw step - couplingLoss step - remainderLoss step
  ≡ transferFactor step * fineRaw step
lossCorrectedTransportExact step
  rewrite exactTransportBalance step =
  ℚRing.solve-∀
    (transferFactor step)
    (fineRaw step)
    (couplingLoss step)
    (remainderLoss step)

record ScaledFilteredLevel : Set where
  constructor scaledFilteredLevel
  field
    filtrationLevel : ℚ
    representedScale : ScaleRepresentation
    levelDefect : ℚ

open ScaledFilteredLevel public

record ScaledFilteredBoundary : Set where
  constructor scaledFilteredBoundary
  field
    finiteLevelIdentityProvesLimitSurvival : Set
    finiteLevelIdentityDoesNotProveLimitSurvival :
      finiteLevelIdentityProvesLimitSurvival → Set

    rawQuantityAloneDeterminesPhysicalQuantity : Set
    rawQuantityAloneDoesNotDeterminePhysicalQuantity :
      rawQuantityAloneDeterminesPhysicalQuantity → Set

    vanishingOrSummableDefectStillRequired : Set
    vanishingOrSummableDefectStillRequiredWitness :
      vanishingOrSummableDefectStillRequired

canonicalScaledFilteredBoundary : ScaledFilteredBoundary
canonicalScaledFilteredBoundary =
  scaledFilteredBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊤ tt
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤; tt)
