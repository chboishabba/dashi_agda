module DASHI.Philosophy.PhilosophyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat using (_+_)

import DASHI.Philosophy.ActionDominationCost as Domination
import DASHI.Philosophy.AgonisticRelationalPluralism as Plural
import DASHI.Philosophy.BreadthProfile as Breadth
import DASHI.Philosophy.ContextTopology as ContextTopology
import DASHI.Philosophy.DeterritorialisationReceipt as Deterritorialisation
import DASHI.Philosophy.ExistingFormalismBridge as Existing
import DASHI.Philosophy.InterpretationStrata as Strata
import DASHI.Philosophy.LocalChartNormalisation as Local
import DASHI.Philosophy.MarkedRelationalExtension as Marked
import DASHI.Philosophy.MaterialFeedbackIntervention as Feedback
import DASHI.Philosophy.PatternPreservingTeaching as Teaching
import DASHI.Philosophy.PhilosophicalPromotionBoundary as Promotion
import DASHI.Philosophy.PolyphonicRelation as Polyphony
import DASHI.Philosophy.ProcessOntology as Process
import DASHI.Philosophy.RepresentationReadingBoundary as Reading
import DASHI.Philosophy.RetroactiveMeaning as Retroactive
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

pantsAndBallsRemainDistinct :
  ContextTopology.pantsAndBallsAreIdenticalStructures
    ContextTopology.canonicalContextTopologyBoundary
  ≡
  false
pantsAndBallsRemainDistinct =
  refl

breadthDoesNotCollapseToOptionCount :
  Breadth.manyOptionsAloneSuffice
    Breadth.canonicalBroadMindednessBoundary
  ≡
  false
breadthDoesNotCollapseToOptionCount =
  refl

retroactiveMeaningIsNotBackwardCausation :
  Retroactive.reinterpretationEqualsBackwardCausation
    Retroactive.canonicalRetroactiveMeaningBoundary
  ≡
  false
retroactiveMeaningIsNotBackwardCausation =
  refl

deterritorialisationIsNotAutomaticallyEmancipatory :
  Deterritorialisation.everyDeterritorialisationIsEmancipatory
    Deterritorialisation.canonicalDeterritorialisationBoundary
  ≡
  false
deterritorialisationIsNotAutomaticallyEmancipatory =
  refl

polyphonyDoesNotRequireFinalUnity :
  Polyphony.oneFinalSynthesisRequired
    Polyphony.canonicalPolyphonyBoundary
  ≡
  false
polyphonyDoesNotRequireFinalUnity =
  refl

symbolicReadingDoesNotProveStructure :
  Reading.symbolicResonanceProvesStructuralProperty
    Reading.canonicalRepresentationReadingBoundary
  ≡
  false
symbolicReadingDoesNotProveStructure =
  refl

contractionAloneIsNotDomination :
  Domination.everyContractionIsDomination
    Domination.canonicalDominationBoundary
  ≡
  false
contractionAloneIsNotDomination =
  refl
