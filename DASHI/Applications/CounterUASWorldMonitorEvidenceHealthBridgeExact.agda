module DASHI.Applications.CounterUASWorldMonitorEvidenceHealthBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Applications.CounterUASWorldMonitorEvidenceHealthSourceAtlasExact as Sources

------------------------------------------------------------------------
-- WORLDMONITOR -> COUNTER-UAS EVIDENCE-HEALTH BRIDGE
--
-- Retrospective DASHI cross-pollination from commit-pinned WorldMonitor
-- implementation patterns. The software source pays implementation precedent
-- only; the exact factorisation/non-factorisation results below are DASHI
-- constructions and do not claim historical identity or product validation.
------------------------------------------------------------------------

staleEvidenceMeansFalse : Bool
staleEvidenceMeansFalse = false

emptyFeedMeansPhenomenonAbsent : Bool
emptyFeedMeansPhenomenonAbsent = false

multipleSignalsImplyIndependentGenealogy : Bool
multipleSignalsImplyIndependentGenealogy = false

highSourceTierGuaranteesTruth : Bool
highSourceTierGuaranteesTruth = false

crossDomainConvergenceCreatesIdentity : Bool
crossDomainConvergenceCreatesIdentity = false

baselineAnomalyCreatesThreatAuthority : Bool
baselineAnomalyCreatesThreatAuthority = false

implementationPatternImportsProof : Bool
implementationPatternImportsProof = false

------------------------------------------------------------------------
-- I. Visible signal count is inadequate for evidence-health / promotion.
--
-- The same apparent count can arise from fresh, independently genealogised
-- signals or from stale/shared-source echoes. Agreement count therefore cannot
-- pay freshness, genealogy, or diversity obligations by itself.
------------------------------------------------------------------------

data EvidenceWorld : Set where
  freshIndependentCorroboration : EvidenceWorld
  staleSharedEcho : EvidenceWorld

data SignalCountSurface : Set where
  sameVisibleSignalCount : SignalCountSurface

data EvidenceHealthSurface : Set where
  healthyCorroborationSurface : EvidenceHealthSurface
  degradedEchoSurface : EvidenceHealthSurface

data EvidenceHealthQuery : Set where
  visibleSignalQuery : EvidenceHealthQuery
  promotionEligibilityQuery : EvidenceHealthQuery

data EvidenceHealthAnswer : Set where
  visibleSignalsObserved : EvidenceHealthAnswer
  promotionEligible : EvidenceHealthAnswer
  promotionBlocked : EvidenceHealthAnswer

signalCountProjection : EvidenceWorld → SignalCountSurface
signalCountProjection world = sameVisibleSignalCount

evidenceHealthProjection : EvidenceWorld → EvidenceHealthSurface
evidenceHealthProjection freshIndependentCorroboration = healthyCorroborationSurface
evidenceHealthProjection staleSharedEcho = degradedEchoSurface

evidenceHealthAnswer : EvidenceHealthQuery → EvidenceWorld → EvidenceHealthAnswer
evidenceHealthAnswer visibleSignalQuery world = visibleSignalsObserved
evidenceHealthAnswer promotionEligibilityQuery freshIndependentCorroboration = promotionEligible
evidenceHealthAnswer promotionEligibilityQuery staleSharedEcho = promotionBlocked

evidenceHealthSemantics :
  Adequacy.QuerySemantics EvidenceWorld EvidenceHealthQuery EvidenceHealthAnswer
evidenceHealthSemantics = Adequacy.querySemantics evidenceHealthAnswer

signalCountEvidenceHealthAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    signalCountProjection
    evidenceHealthSemantics
    promotionEligibilityQuery
signalCountEvidenceHealthAdequacyDefect =
  Adequacy.queryAdequacyDefect
    freshIndependentCorroboration
    staleSharedEcho
    refl
    (λ ())

signalCountCannotDeterminePromotionEligibility :
  Adequacy.AdequateFor
    signalCountProjection
    evidenceHealthSemantics
    promotionEligibilityQuery →
  ⊥
signalCountCannotDeterminePromotionEligibility =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    signalCountEvidenceHealthAdequacyDefect

evidenceHealthAnswerFromJoinedSurface : EvidenceHealthSurface → EvidenceHealthAnswer
evidenceHealthAnswerFromJoinedSurface healthyCorroborationSurface = promotionEligible
evidenceHealthAnswerFromJoinedSurface degradedEchoSurface = promotionBlocked

evidenceHealthJoinedSurfaceDeterminesPromotion :
  Adequacy.AdequateFor
    evidenceHealthProjection
    evidenceHealthSemantics
    promotionEligibilityQuery
evidenceHealthJoinedSurfaceDeterminesPromotion =
  Adequacy.factorsForQuery
    evidenceHealthAnswerFromJoinedSurface
    (λ { freshIndependentCorroboration → refl
       ; staleSharedEcho → refl
       })

------------------------------------------------------------------------
-- II. No visible observation is inadequate for the meaning of absence.
--
-- A coverage/source-health gap and an observed negative state can expose the
-- same public surface: no current visible observation. The missing gap-state
-- coordinate is therefore consumer-relevant.
------------------------------------------------------------------------

data GapWorld : Set where
  unavailableCoverageWorld : GapWorld
  observedAbsenceWorld : GapWorld

data VisibilitySurface : Set where
  noVisibleObservation : VisibilitySurface

data GapStateSurface : Set where
  coverageUnavailable : GapStateSurface
  observationSupportsAbsence : GapStateSurface

data GapQuery : Set where
  visibilityQuery : GapQuery
  absenceMeaningQuery : GapQuery

data GapAnswer : Set where
  nothingVisible : GapAnswer
  coverageGapAnswer : GapAnswer
  observedAbsenceAnswer : GapAnswer

visibilityProjection : GapWorld → VisibilitySurface
visibilityProjection world = noVisibleObservation

gapStateProjection : GapWorld → GapStateSurface
gapStateProjection unavailableCoverageWorld = coverageUnavailable
gapStateProjection observedAbsenceWorld = observationSupportsAbsence

gapAnswer : GapQuery → GapWorld → GapAnswer
gapAnswer visibilityQuery world = nothingVisible
gapAnswer absenceMeaningQuery unavailableCoverageWorld = coverageGapAnswer
gapAnswer absenceMeaningQuery observedAbsenceWorld = observedAbsenceAnswer

gapSemantics : Adequacy.QuerySemantics GapWorld GapQuery GapAnswer
gapSemantics = Adequacy.querySemantics gapAnswer

visibilityGapMeaningAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    visibilityProjection
    gapSemantics
    absenceMeaningQuery
visibilityGapMeaningAdequacyDefect =
  Adequacy.queryAdequacyDefect
    unavailableCoverageWorld
    observedAbsenceWorld
    refl
    (λ ())

visibilityAloneCannotDetermineAbsenceMeaning :
  Adequacy.AdequateFor visibilityProjection gapSemantics absenceMeaningQuery → ⊥
visibilityAloneCannotDetermineAbsenceMeaning =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    visibilityGapMeaningAdequacyDefect

gapStateAnswer : GapStateSurface → GapAnswer
gapStateAnswer coverageUnavailable = coverageGapAnswer
gapStateAnswer observationSupportsAbsence = observedAbsenceAnswer

gapStateDeterminesAbsenceMeaning :
  Adequacy.AdequateFor gapStateProjection gapSemantics absenceMeaningQuery
gapStateDeterminesAbsenceMeaning =
  Adequacy.factorsForQuery
    gapStateAnswer
    (λ { unavailableCoverageWorld → refl
       ; observedAbsenceWorld → refl
       })

------------------------------------------------------------------------
-- III. Raw count is inadequate for baseline-relative anomaly status.
------------------------------------------------------------------------

data BaselineWorld : Set where
  expectedCountWorld : BaselineWorld
  anomalousCountWorld : BaselineWorld

data RawCountSurface : Set where
  sameRawCount : RawCountSurface

data BaselineContextSurface : Set where
  expectedAgainstBaseline : BaselineContextSurface
  elevatedAgainstBaseline : BaselineContextSurface

data BaselineQuery : Set where
  rawCountQuery : BaselineQuery
  anomalyStatusQuery : BaselineQuery

data BaselineAnswer : Set where
  rawCountObserved : BaselineAnswer
  baselineExpectedAnswer : BaselineAnswer
  baselineAnomalousAnswer : BaselineAnswer

rawCountProjection : BaselineWorld → RawCountSurface
rawCountProjection world = sameRawCount

baselineContextProjection : BaselineWorld → BaselineContextSurface
baselineContextProjection expectedCountWorld = expectedAgainstBaseline
baselineContextProjection anomalousCountWorld = elevatedAgainstBaseline

baselineAnswer : BaselineQuery → BaselineWorld → BaselineAnswer
baselineAnswer rawCountQuery world = rawCountObserved
baselineAnswer anomalyStatusQuery expectedCountWorld = baselineExpectedAnswer
baselineAnswer anomalyStatusQuery anomalousCountWorld = baselineAnomalousAnswer

baselineSemantics :
  Adequacy.QuerySemantics BaselineWorld BaselineQuery BaselineAnswer
baselineSemantics = Adequacy.querySemantics baselineAnswer

rawCountBaselineAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    rawCountProjection
    baselineSemantics
    anomalyStatusQuery
rawCountBaselineAdequacyDefect =
  Adequacy.queryAdequacyDefect
    expectedCountWorld
    anomalousCountWorld
    refl
    (λ ())

rawCountCannotDetermineBaselineAnomaly :
  Adequacy.AdequateFor rawCountProjection baselineSemantics anomalyStatusQuery → ⊥
rawCountCannotDetermineBaselineAnomaly =
  Adequacy.queryAdequacyDefectBlocksFactorisation rawCountBaselineAdequacyDefect

baselineContextAnswer : BaselineContextSurface → BaselineAnswer
baselineContextAnswer expectedAgainstBaseline = baselineExpectedAnswer
baselineContextAnswer elevatedAgainstBaseline = baselineAnomalousAnswer

baselineContextDeterminesAnomaly :
  Adequacy.AdequateFor
    baselineContextProjection
    baselineSemantics
    anomalyStatusQuery
baselineContextDeterminesAnomaly =
  Adequacy.factorsForQuery
    baselineContextAnswer
    (λ { expectedCountWorld → refl
       ; anomalousCountWorld → refl
       })

------------------------------------------------------------------------
-- IV. Typed evidence-health receipt.
------------------------------------------------------------------------

data FreshnessState : Set where
  freshState staleState unavailableState : FreshnessState

data GenealogyState : Set where
  independentSources sharedSourceAncestry unresolvedGenealogy : GenealogyState

data DiversityState : Set where
  oneSourceFamily multipleSourceFamilies unresolvedDiversity : DiversityState

data GapState : Set where
  noDeclaredGap sourceUnavailableGap sourceStaleGap notQueriedGap : GapState

record EvidenceHealthReceipt : Set where
  constructor evidenceHealthReceipt
  field
    freshness : FreshnessState
    genealogy : GenealogyState
    diversity : DiversityState
    gapState : GapState
    baselineContextRetained : Bool
    baselineContextRetainedIsTrue : baselineContextRetained ≡ true
    sourceProvenanceRetained : Bool
    sourceProvenanceRetainedIsTrue : sourceProvenanceRetained ≡ true
    receiptCreatesIdentity : Bool
    receiptCreatesIdentityIsFalse : receiptCreatesIdentity ≡ false
    receiptCreatesThreatAuthority : Bool
    receiptCreatesThreatAuthorityIsFalse : receiptCreatesThreatAuthority ≡ false

open EvidenceHealthReceipt public

canonicalHealthyEvidenceReceipt : EvidenceHealthReceipt
canonicalHealthyEvidenceReceipt =
  evidenceHealthReceipt
    freshState
    independentSources
    multipleSourceFamilies
    noDeclaredGap
    true refl
    true refl
    false refl
    false refl

canonicalGapEvidenceReceipt : EvidenceHealthReceipt
canonicalGapEvidenceReceipt =
  evidenceHealthReceipt
    unavailableState
    unresolvedGenealogy
    unresolvedDiversity
    sourceUnavailableGap
    true refl
    true refl
    false refl
    false refl

worldMonitorImplementationAtlasCreatesAuthority : Bool
worldMonitorImplementationAtlasCreatesAuthority =
  Sources.worldMonitorEvidenceHealthSourceAtlasCreatesAuthority

record CounterUASWorldMonitorEvidenceHealthBoundary : Set where
  constructor counterUASWorldMonitorEvidenceHealthBoundary
  field
    staleEqualsFalse : Bool
    staleEqualsFalseIsFalse : staleEqualsFalse ≡ false
    emptyEqualsPhenomenonAbsent : Bool
    emptyEqualsPhenomenonAbsentIsFalse : emptyEqualsPhenomenonAbsent ≡ false
    agreementCountEqualsIndependentEvidence : Bool
    agreementCountEqualsIndependentEvidenceIsFalse :
      agreementCountEqualsIndependentEvidence ≡ false
    sourceTierEqualsTruth : Bool
    sourceTierEqualsTruthIsFalse : sourceTierEqualsTruth ≡ false
    convergenceEqualsIdentity : Bool
    convergenceEqualsIdentityIsFalse : convergenceEqualsIdentity ≡ false
    anomalyEqualsThreatAuthority : Bool
    anomalyEqualsThreatAuthorityIsFalse : anomalyEqualsThreatAuthority ≡ false
    implementationPrecedentEqualsImportedProof : Bool
    implementationPrecedentEqualsImportedProofIsFalse :
      implementationPrecedentEqualsImportedProof ≡ false

canonicalCounterUASWorldMonitorEvidenceHealthBoundary :
  CounterUASWorldMonitorEvidenceHealthBoundary
canonicalCounterUASWorldMonitorEvidenceHealthBoundary =
  counterUASWorldMonitorEvidenceHealthBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
