module DASHI.Law.SensibLawWorldMonitorComparativeAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawChangeLocusExact as Locus
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact as WM
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthSourceAtlasExact as Source

------------------------------------------------------------------------
-- M11 WORLDMONITOR COMPARATIVE ADAPTER
--
-- Forecast/risk/evidence surfaces remain typed away from ontic world identity
-- unless an application supplies explicit world evidence. Repository software
-- is implementation precedent only.
------------------------------------------------------------------------

data WorldMonitorDifferenceKind : Set where
  sourceMeasurementDifference : WorldMonitorDifferenceKind
  forecastRunDifference : WorldMonitorDifferenceKind
  forecastModelDifference : WorldMonitorDifferenceKind
  dashboardProjectionDifference : WorldMonitorDifferenceKind

worldMonitorDifferenceLayer :
  WorldMonitorDifferenceKind → Locus.ChangeLayer
worldMonitorDifferenceLayer sourceMeasurementDifference =
  Locus.worldEvidenceLayer
worldMonitorDifferenceLayer forecastRunDifference =
  Locus.representationLayer
worldMonitorDifferenceLayer forecastModelDifference =
  Locus.theoryLayer
worldMonitorDifferenceLayer dashboardProjectionDifference =
  Locus.consumerProjectionLayer

forecastRunIsRepresentation :
  worldMonitorDifferenceLayer forecastRunDifference ≡ Locus.representationLayer
forecastRunIsRepresentation = refl

forecastModelIsTheory :
  worldMonitorDifferenceLayer forecastModelDifference ≡ Locus.theoryLayer
forecastModelIsTheory = refl

dashboardIsConsumerProjection :
  worldMonitorDifferenceLayer dashboardProjectionDifference
  ≡ Locus.consumerProjectionLayer
dashboardIsConsumerProjection = refl

evidenceBoundary : WM.CounterUASWorldMonitorEvidenceHealthBoundary
evidenceBoundary = WM.canonicalCounterUASWorldMonitorEvidenceHealthBoundary

sourceAtlasBoundary : Source.WorldMonitorEvidenceHealthAttributionBoundary
sourceAtlasBoundary = Source.canonicalWorldMonitorEvidenceHealthAttributionBoundary

signalCountStillNotIndependentEvidence :
  WM.agreementCountEqualsIndependentEvidence evidenceBoundary ≡ false
signalCountStillNotIndependentEvidence = refl

sourceTierStillNotTruth :
  WM.sourceTierEqualsTruth evidenceBoundary ≡ false
sourceTierStillNotTruth = refl

implementationPatternStillNotProof :
  Source.implementationPatternEqualsImportedProof sourceAtlasBoundary ≡ false
implementationPatternStillNotProof = refl

data ForecastChangedImpliesWorldChanged : Set where
data RiskScoreChangedImpliesWorldChanged : Set where
data SignalAppearedImpliesClaimTrue : Set where
data ImplementationPatternCreatesSemanticAuthority : Set where

forecastChangedDoesNotImplyWorldChanged :
  ForecastChangedImpliesWorldChanged → ⊥
forecastChangedDoesNotImplyWorldChanged ()

riskScoreChangedDoesNotImplyWorldChanged :
  RiskScoreChangedImpliesWorldChanged → ⊥
riskScoreChangedDoesNotImplyWorldChanged ()

signalAppearedDoesNotImplyClaimTrue :
  SignalAppearedImpliesClaimTrue → ⊥
signalAppearedDoesNotImplyClaimTrue ()

implementationPatternDoesNotCreateSemanticAuthority :
  ImplementationPatternCreatesSemanticAuthority → ⊥
implementationPatternDoesNotCreateSemanticAuthority ()

record WorldMonitorComparativeBoundary : Set where
  constructor worldMonitorComparativeBoundary
  field
    sourceMeasurementTypedWorldEvidence : Bool
    sourceMeasurementTypedWorldEvidenceIsTrue :
      sourceMeasurementTypedWorldEvidence ≡ true

    forecastRunTypedRepresentation : Bool
    forecastRunTypedRepresentationIsTrue :
      forecastRunTypedRepresentation ≡ true

    forecastModelTypedTheory : Bool
    forecastModelTypedTheoryIsTrue :
      forecastModelTypedTheory ≡ true

    dashboardTypedConsumerProjection : Bool
    dashboardTypedConsumerProjectionIsTrue :
      dashboardTypedConsumerProjection ≡ true

    forecastChangeAutomaticallyChangesWorld : Bool
    forecastChangeAutomaticallyChangesWorldIsFalse :
      forecastChangeAutomaticallyChangesWorld ≡ false

    riskScoreAutomaticallyChangesWorld : Bool
    riskScoreAutomaticallyChangesWorldIsFalse :
      riskScoreAutomaticallyChangesWorld ≡ false

    signalAppearanceCreatesClaimTruth : Bool
    signalAppearanceCreatesClaimTruthIsFalse :
      signalAppearanceCreatesClaimTruth ≡ false

open WorldMonitorComparativeBoundary public

canonicalWorldMonitorComparativeBoundary : WorldMonitorComparativeBoundary
canonicalWorldMonitorComparativeBoundary =
  worldMonitorComparativeBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
