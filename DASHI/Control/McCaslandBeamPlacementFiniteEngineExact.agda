module DASHI.Control.McCaslandBeamPlacementFiniteEngineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Control.McCaslandFailureSetPlacementCompilerExact as Placement

------------------------------------------------------------------------
-- FINITE PLACEMENT ENGINE FOR THE MCCASLAND BEAM / FLEXIBLE-STRUCTURE LANE
--
-- The paper/thesis explicitly reports examples for a simply supported beam
-- and a large finite-element model.  The accessible indexed sources used in
-- this branch do not expose the historical numeric placement table itself.
-- Therefore the evaluator is implemented, but historical scores are not
-- fabricated.
------------------------------------------------------------------------

data BeamCandidateSite : Set where
  siteA siteB siteC siteD siteE : BeamCandidateSite

data FiniteFailure : Set where
  nominal
  failA
  failB
  failC
  : FiniteFailure

record FinitePlacementScore : Set where
  constructor finite-placement-score
  field
    site : BeamCandidateSite
    failure : FiniteFailure
    controllabilityScore : Nat
    observabilityScore : Nat
    survivesThreshold : Bool

open FinitePlacementScore public

record PlacementScoreTable : Set where
  constructor placement-score-table
  field
    rows : List FinitePlacementScore
    coordinateScaling : String
    throughputPath : String
    sourceOrFixture : String
    historicalSourceTable : Bool

open PlacementScoreTable public

-- A deliberately synthetic regression fixture for the finite evaluator only.
-- These numbers are NOT attributed to McCasland's paper or thesis.
syntheticBeamRegression : PlacementScoreTable
syntheticBeamRegression =
  placement-score-table
    (finite-placement-score siteA nominal 9 8 true ∷
     finite-placement-score siteA failA 0 0 false ∷
     finite-placement-score siteB nominal 8 8 true ∷
     finite-placement-score siteB failA 6 7 true ∷
     finite-placement-score siteC nominal 7 9 true ∷
     finite-placement-score siteC failA 6 6 true ∷
     [])
    "fixed synthetic state scaling"
    "synthetic throughput path"
    "DASHI regression fixture; not historical McCasland data"
    false

record HistoricalBeamPlacementAcquisition : Set where
  constructor historical-beam-placement-acquisition
  field
    sourceObject : String
    simplySupportedBeamExampleKnownToExist : Bool
    simplySupportedBeamExampleKnownToExistIsTrue :
      simplySupportedBeamExampleKnownToExist ≡ true
    largeFiniteElementExampleKnownToExist : Bool
    largeFiniteElementExampleKnownToExistIsTrue :
      largeFiniteElementExampleKnownToExist ≡ true
    numericPlacementTableLocated : Bool
    numericPlacementTableLocatedIsFalse : numericPlacementTableLocated ≡ false
    requiredNextReceipt : String

mccaslandHistoricalBeamFrontier : HistoricalBeamPlacementAcquisition
mccaslandHistoricalBeamFrontier =
  historical-beam-placement-acquisition
    "McCasland, Fault-Tolerant Sensor and Actuator Selection for Control of Flexible Structures, ACC 1989 / MIT thesis"
    true refl
    true refl
    false refl
    "full paper/thesis numerical beam example: candidate sites, scaling, Gramian norm scores, failure cases and selected placement"

record McCaslandFiniteEngineBoundary : Set where
  constructor mccasland-finite-engine-boundary
  field
    finiteEvaluatorImplemented : Bool
    finiteEvaluatorImplementedIsTrue : finiteEvaluatorImplemented ≡ true
    syntheticFixtureIsHistoricalResult : Bool
    syntheticFixtureIsHistoricalResultIsFalse : syntheticFixtureIsHistoricalResult ≡ false
    indexedAbstractSufficesToReconstructNumericTable : Bool
    indexedAbstractSufficesToReconstructNumericTableIsFalse :
      indexedAbstractSufficesToReconstructNumericTable ≡ false
    sourceTableRequiredForHistoricalPlacementClaim : Bool
    sourceTableRequiredForHistoricalPlacementClaimIsTrue :
      sourceTableRequiredForHistoricalPlacementClaim ≡ true

canonicalMcCaslandFiniteEngineBoundary : McCaslandFiniteEngineBoundary
canonicalMcCaslandFiniteEngineBoundary =
  mccasland-finite-engine-boundary true refl false refl false refl true refl
