module DASHI.Philosophy.PhilosophyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat using (_+_)

import DASHI.Philosophy.AgonisticRelationalPluralism as Plural
import DASHI.Philosophy.ExistingFormalismBridge as Existing
import DASHI.Philosophy.InterpretationStrata as Strata
import DASHI.Philosophy.LocalChartNormalisation as Local
import DASHI.Philosophy.MarkedRelationalExtension as Marked
import DASHI.Philosophy.MaterialFeedbackIntervention as Feedback
import DASHI.Philosophy.PatternPreservingTeaching as Teaching
import DASHI.Philosophy.PhilosophicalPromotionBoundary as Promotion
import DASHI.Philosophy.ProcessOntology as Process
import DASHI.Philosophy.TopologyChangeBoundary as Topology

strataRemainSeparated :
  Strata.directCrossStratumPromotionAllowed
    Strata.structuralInterpretationBoundary
  ≡
  false
strataRemainSeparated =
  refl

markedExtensionIndexRegression :
  Marked.relationalMarkedIndex ≡ 11
markedExtensionIndexRegression =
  refl

jPlusOneRegression :
  Local.globalStarIndex + 1
  ≡
  Local.relationalExtensionIndex
jPlusOneRegression =
  refl

observerAloneDoesNotChangeTopology :
  Local.observerAloneChangesTopology
    Local.canonicalSymbolicJObserverBridge
  ≡
  false
observerAloneDoesNotChangeTopology =
  refl

topologyPromotionStillFalse :
  Topology.topologyChangePromoted
    Topology.canonicalObserverTopologyBoundary
  ≡
  false
topologyPromotionStillFalse =
  refl

outputRemovalIsNotSystemClosure :
  Feedback.removingOneOutputProvesSystemicClosure
    Feedback.canonicalInterventionBoundary
  ≡
  false
outputRemovalIsNotSystemClosure =
  refl

lessonIsNotWholeTradition :
  Teaching.localLessonEqualsWholeTradition
    Teaching.canonicalTeachingBoundary
  ≡
  false
lessonIsNotWholeTradition =
  refl

pluralAttachmentDoesNotImplyEquivalence :
  Plural.allRealAttachmentsAreEquivalent
    Plural.canonicalAgonisticPluralismBoundary
  ≡
  false
pluralAttachmentDoesNotImplyEquivalence =
  refl

legacySymbolicGateRemainsClosed :
  Existing.legacyNumerologyGateClosed
    Existing.canonicalExistingFormalismBridge
  ≡
  true
legacySymbolicGateRemainsClosed =
  refl

philosophyPromotionRemainsEmpty :
  Promotion.promotionTokens
    Promotion.canonicalPhilosophyNonClaimBoundary
  ≡
  []
philosophyPromotionRemainsEmpty =
  refl

processTenAndElevenRemainChartIndices :
  Process.stageIndex Process.markedExtension ≡ 10
processTenAndElevenRemainChartIndices =
  refl
