module DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.RelationalHistoryFabricExact as HistoryFabric

------------------------------------------------------------------------
-- PHENOMENON EVIDENCE FIBRES OVER TIME
--
-- Evidence is not a terminal scalar.  For phenomenon p and time t, the live
-- evidential fibre is the set/predicate of interpretations still compatible
-- with the evidence available at t.  Updates can refine, reopen, or preserve
-- that fibre.  A present evidence summary does not erase the path by which it
-- was reached.
------------------------------------------------------------------------

data EvidenceCoordinate : Set where
  reportReliability
  anomalyStrength
  controlStrength
  independentReplication
  mechanismDiscrimination
  generalisation
  operationalUtility
  ontologicalInference
  : EvidenceCoordinate

data CoordinateStanding : Set where
  unsupported
  sourceReported
  empiricallySupported
  contested
  downgraded
  unresolved
  : CoordinateStanding

data EvidenceUpdateKind : Set where
  newObservation
  controlledReplication
  failedReplication
  successfulReplication
  methodologicalCritique
  reanalysis
  sourceDisclosure
  clinicalTrial
  metaAnalysis
  : EvidenceUpdateKind

record TemporalEvidenceSystem : Set₁ where
  field
    Time : Set
    Interpretation : Set
    Compatible : Time → Interpretation → Set
    Summary : Set
    summarize : Time → Summary
    timeReference : Time → String

open TemporalEvidenceSystem public

EvidenceFibre : (system : TemporalEvidenceSystem) → Time system → Set₁
EvidenceFibre system t = (h : Interpretation system) → Compatible system t h → Set

-- Refinement means that every interpretation live after the update was already
-- live before it.  It does not require a numerical confidence score.
record FibreRefinement
    (system : TemporalEvidenceSystem)
    (before after : Time system) : Set₁ where
  field
    retainedWasPreviouslyLive :
      ∀ h → Compatible system after h → Compatible system before h

-- Strict refinement additionally carries one concrete interpretation removed
-- by the later evidence.
record StrictFibreRefinement
    (system : TemporalEvidenceSystem)
    (before after : Time system) : Set₁ where
  field
    refinement : FibreRefinement system before after
    removedInterpretation : Interpretation system
    removedWasLive : Compatible system before removedInterpretation
    removedIsNoLongerLive : Compatible system after removedInterpretation → ⊥

-- Reopening is the opposite local event: one interpretation that was excluded
-- before becomes live again after new evidence/reanalysis/disclosure.
record FibreReopening
    (system : TemporalEvidenceSystem)
    (before after : Time system) : Set₁ where
  field
    reopenedInterpretation : Interpretation system
    reopenedNowLive : Compatible system after reopenedInterpretation
    reopenedWasNotLive : Compatible system before reopenedInterpretation → ⊥

record FibreUnchanged
    (system : TemporalEvidenceSystem)
    (before after : Time system) : Set₁ where
  field
    forward : ∀ h → Compatible system before h → Compatible system after h
    backward : ∀ h → Compatible system after h → Compatible system before h

record EvidenceTransition
    (system : TemporalEvidenceSystem)
    (before after : Time system) : Set₁ where
  constructor evidenceTransition
  field
    updateKind : EvidenceUpdateKind
    updateReference : String
    transitionDoesNotClaimMonotonicity : Bool
    transitionDoesNotClaimMonotonicityIsTrue :
      transitionDoesNotClaimMonotonicity ≡ true

------------------------------------------------------------------------
-- Proof-relevant ordered evidence paths.
------------------------------------------------------------------------

data EvidencePath
    (system : TemporalEvidenceSystem) :
    Time system → Time system → Set₁ where
  pathId : ∀ {t} → EvidencePath system t t
  pathStep : ∀ {t u v} →
    EvidenceTransition system t u →
    EvidencePath system u v →
    EvidencePath system t v

------------------------------------------------------------------------
-- Evidence ladder is an observer of a time-indexed fibre, not the fibre itself.
------------------------------------------------------------------------

record EvidenceLadderObservation
    (system : TemporalEvidenceSystem)
    (t : Time system) : Set where
  constructor evidenceLadderObservation
  field
    coordinateStanding : EvidenceCoordinate → CoordinateStanding
    observationReference : String

------------------------------------------------------------------------
-- Same present summary can hide different histories and therefore different
-- next-experiment priorities.
------------------------------------------------------------------------

data ToyTime : Set where earlyA lateA earlyB lateB : ToyTime

data ToyInterpretation : Set where broadHypothesis narrowHypothesis : ToyInterpretation

data ToySummary : Set where samePresentSummary : ToySummary

toyCompatible : ToyTime → ToyInterpretation → Set
toyCompatible earlyA broadHypothesis = ⊤
toyCompatible earlyA narrowHypothesis = ⊤
toyCompatible lateA broadHypothesis = ⊥
toyCompatible lateA narrowHypothesis = ⊤
toyCompatible earlyB broadHypothesis = ⊥
toyCompatible earlyB narrowHypothesis = ⊤
toyCompatible lateB broadHypothesis = ⊥
toyCompatible lateB narrowHypothesis = ⊤

toySystem : TemporalEvidenceSystem
toySystem = record
  { Time = ToyTime
  ; Interpretation = ToyInterpretation
  ; Compatible = toyCompatible
  ; Summary = ToySummary
  ; summarize = λ _ → samePresentSummary
  ; timeReference = λ _ → "finite temporal evidence-fibre fixture"
  }

toyStrictRefinement : StrictFibreRefinement toySystem earlyA lateA
toyStrictRefinement = record
  { refinement = record
      { retainedWasPreviouslyLive = λ
          { broadHypothesis ()
          ; narrowHypothesis _ → tt
          }
      }
  ; removedInterpretation = broadHypothesis
  ; removedWasLive = tt
  ; removedIsNoLongerLive = λ ()
  }

-- Two present states can have the same coarse evidence summary while differing
-- in whether a major hypothesis was actually tested away along the path.
data ToyHistory : Set where refinementHistory inheritedNarrowHistory : ToyHistory

data ToyNextExperiment : Set where testMechanism auditSelectionHistory : ToyNextExperiment

historySummary : ToyHistory → ToySummary
historySummary _ = samePresentSummary

nextExperiment : ToyHistory → ToyNextExperiment
nextExperiment refinementHistory = testMechanism
nextExperiment inheritedNarrowHistory = auditSelectionHistory

historySummarySame :
  historySummary refinementHistory ≡ historySummary inheritedNarrowHistory
historySummarySame = refl

nextExperimentDiffers :
  nextExperiment refinementHistory ≡ nextExperiment inheritedNarrowHistory → ⊥
nextExperimentDiffers ()

presentSummaryCannotRecoverNextExperiment :
  INF.FactorsThrough historySummary nextExperiment → ⊥
presentSummaryCannotRecoverNextExperiment =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      refinementHistory
      inheritedNarrowHistory
      refl
      nextExperimentDiffers)

------------------------------------------------------------------------
-- Canonical donor boundaries retained explicitly.
------------------------------------------------------------------------

historyChoiceBoundary : HistoryChoice.HistoryConditionedChoiceBoundary
historyChoiceBoundary = HistoryChoice.canonicalHistoryConditionedChoiceBoundary

historyFabricBoundary : HistoryFabric.RelationalHistoryFabricBoundary
historyFabricBoundary = HistoryFabric.canonicalRelationalHistoryFabricBoundary

data CurrentStandingErasesEvidencePath : Set where

data RefinementIsAlwaysMonotoneForever : Set where

data FailedReplicationProvesNullOntology : Set where

data SuccessfulReplicationProvesMechanism : Set where

data HistoricalPositiveFindingMustRemainCurrent : Set where

currentStandingDoesNotEraseEvidencePath : CurrentStandingErasesEvidencePath → ⊥
currentStandingDoesNotEraseEvidencePath ()

refinementDoesNotMeanForeverMonotone : RefinementIsAlwaysMonotoneForever → ⊥
refinementDoesNotMeanForeverMonotone ()

failedReplicationDoesNotProveNullOntology : FailedReplicationProvesNullOntology → ⊥
failedReplicationDoesNotProveNullOntology ()

successfulReplicationDoesNotProveMechanism : SuccessfulReplicationProvesMechanism → ⊥
successfulReplicationDoesNotProveMechanism ()

historicalPositiveNeedNotRemainCurrent : HistoricalPositiveFindingMustRemainCurrent → ⊥
historicalPositiveNeedNotRemainCurrent ()

record PhenomenonEvidenceFibreOverTimeBoundary : Set where
  constructor phenomenonEvidenceFibreOverTimeBoundary
  field
    evidenceIsTimeIndexedFibre : Bool
    evidenceIsTimeIndexedFibreIsTrue : evidenceIsTimeIndexedFibre ≡ true
    presentSummaryErasesHistory : Bool
    presentSummaryErasesHistoryIsFalse : presentSummaryErasesHistory ≡ false
    everyUpdateMustShrinkFibre : Bool
    everyUpdateMustShrinkFibreIsFalse : everyUpdateMustShrinkFibre ≡ false
    replicationEqualsMechanismProof : Bool
    replicationEqualsMechanismProofIsFalse : replicationEqualsMechanismProof ≡ false

canonicalPhenomenonEvidenceFibreOverTimeBoundary :
  PhenomenonEvidenceFibreOverTimeBoundary
canonicalPhenomenonEvidenceFibreOverTimeBoundary =
  phenomenonEvidenceFibreOverTimeBoundary
    true refl false refl false refl false refl
