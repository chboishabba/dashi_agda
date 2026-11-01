module DASHI.Core.MeasurementAdministrationComparabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- MEASUREMENT ADMINISTRATION COMPARABILITY
--
-- A shared instrument name does not identify a shared administration protocol.
-- Comparability is indexed by the downstream consumer: administration
-- differences irrelevant to one query may matter to another.
------------------------------------------------------------------------

record MeasurementAdministration : Set where
  constructor measurementAdministration
  field
    instrumentReference : String
    subjectReference : String
    administratorReference : String
    contextReference : String
    timingProtocolReference : String
    responseReference : String

------------------------------------------------------------------------
-- Exact finite protocol witness.
--
-- The instrument-name projection deliberately erases administration context.
-- It answers the identity query but cannot answer the declared pairwise
-- comparability query in this specimen.
------------------------------------------------------------------------

data ProtocolWorld : Set where
  standardAdministration : ProtocolWorld
  hurriedAdministration : ProtocolWorld

data InstrumentSurface : Set where
  sameNamedInstrument : InstrumentSurface

data MeasurementQuery : Set where
  instrumentIdentityQuery : MeasurementQuery
  comparisonQuery : MeasurementQuery

data MeasurementAnswer : Set where
  sameInstrumentAnswer : MeasurementAnswer
  comparisonPaid : MeasurementAnswer
  comparisonUnpaid : MeasurementAnswer

instrumentSurface : ProtocolWorld → InstrumentSurface
instrumentSurface world = sameNamedInstrument

measurementAnswer : MeasurementQuery → ProtocolWorld → MeasurementAnswer
measurementAnswer instrumentIdentityQuery world = sameInstrumentAnswer
measurementAnswer comparisonQuery standardAdministration = comparisonPaid
measurementAnswer comparisonQuery hurriedAdministration = comparisonUnpaid

measurementSemantics :
  Query.QuerySemantics ProtocolWorld MeasurementQuery MeasurementAnswer
measurementSemantics = Query.querySemantics measurementAnswer

instrumentIdentityAdequate :
  Query.AdequateFor instrumentSurface measurementSemantics instrumentIdentityQuery
instrumentIdentityAdequate =
  Query.factorsForQuery
    (λ surface → sameInstrumentAnswer)
    (λ world → refl)

ComparisonQueryAdequacyDefect : Set₁
ComparisonQueryAdequacyDefect =
  Query.QueryAdequacyDefect instrumentSurface measurementSemantics comparisonQuery

comparisonQueryAdequacyDefect : ComparisonQueryAdequacyDefect
comparisonQueryAdequacyDefect =
  Query.queryAdequacyDefect
    standardAdministration
    hurriedAdministration
    refl
    (λ ())

ComparisonQueryAdequate : Set₁
ComparisonQueryAdequate =
  Query.AdequateFor instrumentSurface measurementSemantics comparisonQuery

comparisonQueryNotAdequate : ComparisonQueryAdequate → ⊥
comparisonQueryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation comparisonQueryAdequacyDefect

------------------------------------------------------------------------
-- Promotion / WrongType boundary.
------------------------------------------------------------------------

record MeasurementComparabilityBoundary : Set where
  constructor measurementComparabilityBoundary
  field
    sameInstrumentAutomaticallyComparable : Bool
    observedScoreDifferenceAutomaticallyTraitDifference : Bool
    individualValidityAutomaticallyPairwiseComparable : Bool
    instrumentValidityAutomaticallyValidCaseUse : Bool
    comparabilityRequiresConsumerIndex : Bool
    administrationProtocolIsSeparateCoordinate : Bool

open MeasurementComparabilityBoundary public

canonicalMeasurementComparabilityBoundary : MeasurementComparabilityBoundary
canonicalMeasurementComparabilityBoundary =
  measurementComparabilityBoundary
    false
    false
    false
    false
    true
    true

data SameInstrumentAutomaticallyComparable : Set where
data ScoreDifferenceAutomaticallyTraitDifference : Set where
data IndividualValidityAutomaticallyPairwiseComparable : Set where
data InstrumentValidityAutomaticallyValidCaseUse : Set where

sameInstrumentDoesNotAutomaticallyEstablishComparability :
  SameInstrumentAutomaticallyComparable → ⊥
sameInstrumentDoesNotAutomaticallyEstablishComparability ()

scoreDifferenceDoesNotAutomaticallyEstablishTraitDifference :
  ScoreDifferenceAutomaticallyTraitDifference → ⊥
scoreDifferenceDoesNotAutomaticallyEstablishTraitDifference ()

individualValidityDoesNotAutomaticallyEstablishPairwiseComparability :
  IndividualValidityAutomaticallyPairwiseComparable → ⊥
individualValidityDoesNotAutomaticallyEstablishPairwiseComparability ()

instrumentValidityDoesNotAutomaticallyEstablishValidCaseUse :
  InstrumentValidityAutomaticallyValidCaseUse → ⊥
instrumentValidityDoesNotAutomaticallyEstablishValidCaseUse ()
