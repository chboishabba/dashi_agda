module DASHI.Applications.CounterUASWorldMonitorEvidenceHealthRegression where

open import DASHI.Core.Prelude

import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact as Bridge
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthSourceAtlasExact as Sources
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

record CounterUASWorldMonitorEvidenceHealthRegression : Set where
  constructor counterUASWorldMonitorEvidenceHealthRegression
  field
    staleDoesNotMeanFalse : Bridge.staleEvidenceMeansFalse ≡ false
    emptyDoesNotMeanPhenomenonAbsent : Bridge.emptyFeedMeansPhenomenonAbsent ≡ false
    sourceCountDoesNotMeanIndependentEvidence : Bridge.multipleSignalsImplyIndependentGenealogy ≡ false
    sourceTierDoesNotMeanTruth : Bridge.highSourceTierGuaranteesTruth ≡ false
    convergenceDoesNotMeanIdentity : Bridge.crossDomainConvergenceCreatesIdentity ≡ false
    baselineAnomalyDoesNotCreateThreatAuthority : Bridge.baselineAnomalyCreatesThreatAuthority ≡ false
    visibleSignalCountHasEvidenceHealthDefect :
      Adequacy.QueryAdequacyDefect
        Bridge.signalCountProjection
        Bridge.evidenceHealthSemantics
        Bridge.promotionEligibilityQuery
    missingObservationHasGapMeaningDefect :
      Adequacy.QueryAdequacyDefect
        Bridge.visibilityProjection
        Bridge.gapSemantics
        Bridge.absenceMeaningQuery
    implementationAtlasNonPromoting :
      Sources.worldMonitorEvidenceHealthSourceAtlasCreatesAuthority ≡ false

canonicalCounterUASWorldMonitorEvidenceHealthRegression :
  CounterUASWorldMonitorEvidenceHealthRegression
canonicalCounterUASWorldMonitorEvidenceHealthRegression =
  counterUASWorldMonitorEvidenceHealthRegression
    refl refl refl refl refl refl
    Bridge.signalCountEvidenceHealthAdequacyDefect
    Bridge.visibilityGapMeaningAdequacyDefect
    Sources.worldMonitorEvidenceHealthSourceAtlasCreatesAuthorityIsFalse
