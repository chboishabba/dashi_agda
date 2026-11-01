module DASHI.Ontology.WikidataConsumerResidualRefinementExact where

------------------------------------------------------------------------
-- WIKIDATA INSTANCE OF THE TOP-DOWN CONSUMER/RESIDUAL CALCULUS
--
-- A pass/fail checker is useful for the pass/fail consumer, but it is not
-- sufficient for the exact diagnostic-origin consumer.  The provenance origin
-- is therefore not arbitrary extra metadata: every exact-diagnosis repair is
-- forced to distinguish the collisions erased by the checker bit.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Ontology.WikidataCheckerResultAttributionExact as Checker

exactOriginConsumer : Checker.DiagnosticOrigin → Checker.DiagnosticOrigin
exactOriginConsumer origin = origin

sourceAlignmentCollision :
  Consumer.ConsumerRelevantCollision Checker.checkerBit exactOriginConsumer
sourceAlignmentCollision =
  Consumer.consumer-relevant-collision
    Checker.sourceFailure
    Checker.alignmentFailure
    Checker.sourceAndAlignmentShareFailBit
    Checker.sourceIsNotAlignment

targetMissingEvidenceCollision :
  Consumer.ConsumerRelevantCollision Checker.checkerBit exactOriginConsumer
targetMissingEvidenceCollision =
  Consumer.consumer-relevant-collision
    Checker.targetGraphFailure
    Checker.missingRequiredEvidence
    Checker.targetAndMissingShareFailBit
    Checker.targetIsNotMissing

checkerBitCannotServeExactDiagnosis :
  Consumer.ConsumerSufficient Checker.checkerBit exactOriginConsumer → ⊥
checkerBitCannotServeExactDiagnosis =
  Consumer.coarseCollisionBlocksSufficiency sourceAlignmentCollision

exactAttributionObserver : Checker.DiagnosticOrigin → Checker.DiagnosticOrigin
exactAttributionObserver origin = origin

exactAttributionSeparating : Observer.Separating exactAttributionObserver
exactAttributionSeparating left right same = same

exactAttributionSufficient :
  Consumer.ConsumerSufficient exactAttributionObserver exactOriginConsumer
exactAttributionSufficient =
  Consumer.separatingObserverIsSufficientForEveryConsumer
    exactAttributionSeparating exactOriginConsumer

checkerPlusAttributionRepair :
  Consumer.ResidualRepair
    Checker.checkerBit
    exactAttributionObserver
    exactOriginConsumer
checkerPlusAttributionRepair =
  Consumer.residual-repair
    (λ left right pairSame → cong proj₂ pairSame)

attributionMustSeparateSourceFromAlignment :
  exactAttributionObserver Checker.sourceFailure
  ≡ exactAttributionObserver Checker.alignmentFailure → ⊥
attributionMustSeparateSourceFromAlignment =
  Consumer.residualMustSeparateRelevantCollision
    sourceAlignmentCollision
    checkerPlusAttributionRepair

attributionMustSeparateTargetFromMissing :
  exactAttributionObserver Checker.targetGraphFailure
  ≡ exactAttributionObserver Checker.missingRequiredEvidence → ⊥
attributionMustSeparateTargetFromMissing =
  Consumer.residualMustSeparateRelevantCollision
    targetMissingEvidenceCollision
    checkerPlusAttributionRepair

checkerPlusAttributionStrictlyRefinesChecker :
  Observer.StrictRefinement
    Checker.checkerBit
    (Observer.pairObserver Checker.checkerBit exactAttributionObserver)
checkerPlusAttributionStrictlyRefinesChecker =
  Consumer.consumerRelevantResidualGivesStrictRefinement
    sourceAlignmentCollision
    checkerPlusAttributionRepair

-- Strong necessity statement: ANY proposed exact-diagnosis observer must split
-- the source/alignment collision; this is independent of its carrier shape.
anyExactDiagnosisObserverMustSplitSourceAlignment :
  ∀ {Surface : Set}
    (observe : Checker.DiagnosticOrigin → Surface) →
  Consumer.ConsumerSufficient observe exactOriginConsumer →
  observe Checker.sourceFailure ≡ observe Checker.alignmentFailure → ⊥
anyExactDiagnosisObserverMustSplitSourceAlignment observe sufficient =
  Consumer.everySufficientObserverSeparatesRelevantCollision
    sourceAlignmentCollision sufficient

-- Likewise target-graph failure and missing evidence cannot remain collapsed
-- under an observer claiming to recover exact diagnostic origin.
anyExactDiagnosisObserverMustSplitTargetMissing :
  ∀ {Surface : Set}
    (observe : Checker.DiagnosticOrigin → Surface) →
  Consumer.ConsumerSufficient observe exactOriginConsumer →
  observe Checker.targetGraphFailure ≡ observe Checker.missingRequiredEvidence → ⊥
anyExactDiagnosisObserverMustSplitTargetMissing observe sufficient =
  Consumer.everySufficientObserverSeparatesRelevantCollision
    targetMissingEvidenceCollision sufficient

record WikidataConsumerResidualRefinementBoundary : Set where
  field
    checkerUsefulButInsufficientForExactOrigin : Bool
    provenanceResidualNecessityDerived : Bool
    exactAttributionRepairStrictlyRefinesChecker : Bool
    arbitrarySufficientRepairMustSplitKnownCollisions : Bool
    exactDiagnosisMeansTargetTruth : Bool
    exactDiagnosisMeansEditAuthority : Bool

canonicalWikidataConsumerResidualRefinementBoundary :
  WikidataConsumerResidualRefinementBoundary
canonicalWikidataConsumerResidualRefinementBoundary = record
  { checkerUsefulButInsufficientForExactOrigin = true
  ; provenanceResidualNecessityDerived = true
  ; exactAttributionRepairStrictlyRefinesChecker = true
  ; arbitrarySufficientRepairMustSplitKnownCollisions = true
  ; exactDiagnosisMeansTargetTruth = false
  ; exactDiagnosisMeansEditAuthority = false
  }
