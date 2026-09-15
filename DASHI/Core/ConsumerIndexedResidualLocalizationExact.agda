module DASHI.Core.ConsumerIndexedResidualLocalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre

------------------------------------------------------------------------
-- CONSUMER-INDEXED RESIDUAL LOCALIZATION
--
-- A coarse/fine collision tells us that some retained residual matters, but it
-- need not tell us that the whole residual is required.  This owner isolates a
-- smaller observer on RelativeFine and records a proof that this coordinate
-- alone separates the concrete consumer witness.
--
--   FineState -> Coarse x RelativeFine
--                          |
--                          v
--                 ResidualCoordinate
--
-- If two states share Coarse, the consumer distinguishes them, and the selected
-- ResidualCoordinate also distinguishes their RelativeFine values, then
-- (Coarse, ResidualCoordinate) is a strict witness-level refinement of Coarse.
--
-- This does not claim that the localized coordinate is globally adequate or
-- minimal.  It is one proof-guided descent step inside the residual fibre.
------------------------------------------------------------------------

record LocalizedResidualWitness
    {FineState Observation : Set}
    (geometry : Fibre.CoarseFineReopening FineState)
    (observe : FineState -> Observation) : Set₁ where
  constructor localized-residual-witness
  field
    fineSensitiveWitness : Fibre.FineSensitiveConsumer geometry observe

    ResidualCoordinate : Set
    residualCoordinate : Fibre.RelativeFine geometry -> ResidualCoordinate

    residualCoordinateSeparates :
      residualCoordinate
        (Fibre.relativeFine geometry
          (Fibre.left fineSensitiveWitness))
      ≡ residualCoordinate
        (Fibre.relativeFine geometry
          (Fibre.right fineSensitiveWitness))
      -> ⊥

open LocalizedResidualWitness public

localizedObserver :
  ∀ {FineState Observation}
    {geometry : Fibre.CoarseFineReopening FineState}
    {observe : FineState -> Observation} ->
  LocalizedResidualWitness geometry observe ->
  FineState -> Fibre.Coarse geometry × ResidualCoordinate
localizedObserver {geometry = geometry} witness state =
  Fibre.coarse geometry state ,
  residualCoordinate witness (Fibre.relativeFine geometry state)

localizedObserverSeparatesWitness :
  ∀ {FineState Observation}
    {geometry : Fibre.CoarseFineReopening FineState}
    {observe : FineState -> Observation} ->
  (witness : LocalizedResidualWitness geometry observe) ->
  localizedObserver witness (Fibre.left (fineSensitiveWitness witness))
  ≡ localizedObserver witness (Fibre.right (fineSensitiveWitness witness))
  -> ⊥
localizedObserverSeparatesWitness witness same =
  residualCoordinateSeparates witness (cong proj₂ same)

coarseStillAgreesOnLocalizedWitness :
  ∀ {FineState Observation}
    {geometry : Fibre.CoarseFineReopening FineState}
    {observe : FineState -> Observation} ->
  (witness : LocalizedResidualWitness geometry observe) ->
  Fibre.coarse geometry (Fibre.left (fineSensitiveWitness witness))
  ≡ Fibre.coarse geometry (Fibre.right (fineSensitiveWitness witness))
coarseStillAgreesOnLocalizedWitness witness =
  Fibre.sameCoarse (fineSensitiveWitness witness)

consumerStillSeparatesLocalizedWitness :
  ∀ {FineState Observation}
    {geometry : Fibre.CoarseFineReopening FineState}
    {observe : FineState -> Observation} ->
  (witness : LocalizedResidualWitness geometry observe) ->
  observe (Fibre.left (fineSensitiveWitness witness))
  ≡ observe (Fibre.right (fineSensitiveWitness witness))
  -> ⊥
consumerStillSeparatesLocalizedWitness witness =
  Fibre.consumerSeparates (fineSensitiveWitness witness)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ConsumerIndexedResidualLocalizationBoundary : Set where
  constructor consumer-indexed-residual-localization-boundary
  field
    canonicalCoarseFineGeometryReused : Bool
    canonicalFineSensitiveConsumerReused : Bool
    residualMayBeObservedMoreCoarsely : Bool
    localizedCoordinateMaySeparateConcreteWitness : Bool
    localizedObserverStrictlyRefinesCoarseOnWitness : Bool
    localizedCoordinateAutomaticallyGloballyAdequate : Bool
    localizedCoordinateAutomaticallyMinimal : Bool
    exactReopeningAutomaticallyPreservedByLocalization : Bool
    domainSpecificTruthCreatedByGenericLocalization : Bool
open ConsumerIndexedResidualLocalizationBoundary public

canonicalConsumerIndexedResidualLocalizationBoundary :
  ConsumerIndexedResidualLocalizationBoundary
canonicalConsumerIndexedResidualLocalizationBoundary =
  consumer-indexed-residual-localization-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
