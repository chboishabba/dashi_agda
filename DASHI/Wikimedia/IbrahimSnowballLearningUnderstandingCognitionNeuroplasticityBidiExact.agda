module DASHI.Wikimedia.IbrahimSnowballLearningUnderstandingCognitionNeuroplasticityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.IbrahimSnowballLearningMemoryTraumaReplicationConsensusBidiExact as Prior

------------------------------------------------------------------------
-- IBRAHIM LIVE FIRST-LINK / CONCRETE-CONSUMER FOLLOW
--
-- Current English Wikipedia, inspected 2026-09-11:
--   Learning -> Understanding is the first qualifying lead-body link after the
--   article's disambiguation/header material.
--   Understanding -> cognitive/cognition is the first qualifying lead-body link.
-- These are CURRENT-page navigation observations only; they are not asserted
-- to be Ibrahim et al.'s November-2014 dump edges.
--
-- Concrete consumer:
--   learning/understanding/cognition -> neuroplasticity/synaptic plasticity ->
--   memory reconsolidation mechanism.
-- The consumer forces a noncollapse between cognitive/behavioural function,
-- neural plasticity, a measured synaptic mechanism, memory updating, and
-- therapeutic/diagnostic claims.
------------------------------------------------------------------------

record CurrentFirstLinkReceipt : Set where
  constructor current-first-link-receipt
  field
    sourcePage : String
    targetPage : String
    inspectedDate : String
    canonicalSourceURL : String
    canonicalTargetURL : String
    currentRevisionOnly : Bool
    historical2014EdgeClaimed : Bool
open CurrentFirstLinkReceipt public

learningToUnderstanding : CurrentFirstLinkReceipt
learningToUnderstanding = current-first-link-receipt
  "Learning"
  "Understanding"
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Learning"
  "https://en.wikipedia.org/wiki/Understanding"
  true false

understandingToCognition : CurrentFirstLinkReceipt
understandingToCognition = current-first-link-receipt
  "Understanding"
  "Cognition"
  "2026-09-11"
  "https://en.wikipedia.org/wiki/Understanding"
  "https://en.wikipedia.org/wiki/Cognition"
  true false

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim learning/understanding/cognition/neuroplasticity BIDI"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create causal mechanism, understanding, memory update, therapeutic efficacy or diagnosis")

understandingQid : Identity.ExternalIdentityDemand
understandingQid = mkQid "understanding" "Q46744"

cognitionQid : Identity.ExternalIdentityDemand
cognitionQid = mkQid "cognition" "Q2200417"

cognitiveScienceQid : Identity.ExternalIdentityDemand
cognitiveScienceQid = mkQid "cognitive science" "Q147638"

neuroscienceQid : Identity.ExternalIdentityDemand
neuroscienceQid = mkQid "neuroscience" "Q207011"

neuroplasticityQid : Identity.ExternalIdentityDemand
neuroplasticityQid = mkQid "neuroplasticity" "Q849491"

longTermPotentiationQid : Identity.ExternalIdentityDemand
longTermPotentiationQid = mkQid "long-term potentiation" "Q1805481"

memoryReconsolidationQid : Identity.ExternalIdentityDemand
memoryReconsolidationQid = Identity.mkOptionalIdentityDemand
  "Ibrahim learning/understanding/cognition/neuroplasticity BIDI"
  "external concept identity"
  "memory reconsolidation as a process"
  Identity.wikidataQid
  (Identity.unresolved
    "article-level Wikidata identities exist, but no exact process-level QID was promoted in this pass")

------------------------------------------------------------------------
-- Dewey coordinates: retain every inspected coordinate without forcing one.
------------------------------------------------------------------------

understandingDewey : Dewey.DeweyCoordinate
understandingDewey = Dewey.mkVerifiedDewey
  "understanding"
  "001"
  "Wikidata Q46744 DDC statement inspected 2026-09-11"

cognitionDewey : Dewey.DeweyCoordinate
cognitionDewey = Dewey.mkUnresolvedDewey
  "cognition"
  "no exact DDC statement promoted from the inspected Q2200417 page"

cognitiveScienceDeweyComputing : Dewey.DeweyCoordinate
cognitiveScienceDeweyComputing = Dewey.mkVerifiedDewey
  "cognitive science"
  "006.3"
  "Wikidata Q147638 DDC statement inspected 2026-09-11"

cognitiveScienceDeweyNeuro : Dewey.DeweyCoordinate
cognitiveScienceDeweyNeuro = Dewey.mkVerifiedDewey
  "cognitive science"
  "612.8233"
  "Wikidata Q147638 DDC statement inspected 2026-09-11"

cognitiveScienceDeweyPsychology : Dewey.DeweyCoordinate
cognitiveScienceDeweyPsychology = Dewey.mkVerifiedDewey
  "cognitive science"
  "153"
  "Wikidata Q147638 DDC statement inspected 2026-09-11"

neuroscienceDeweyBiology : Dewey.DeweyCoordinate
neuroscienceDeweyBiology = Dewey.mkVerifiedDewey
  "neuroscience"
  "573.8"
  "Wikidata Q207011 DDC statement inspected 2026-09-11"

neuroscienceDeweyPhysiology : Dewey.DeweyCoordinate
neuroscienceDeweyPhysiology = Dewey.mkVerifiedDewey
  "neuroscience"
  "612.8"
  "Wikidata Q207011 DDC statement inspected 2026-09-11"

neuroplasticityDewey : Dewey.DeweyCoordinate
neuroplasticityDewey = Dewey.mkUnresolvedDewey
  "neuroplasticity"
  "no DDC statement observed on inspected Q849491 page"

------------------------------------------------------------------------
-- Primary/source-bounded scientific line.
------------------------------------------------------------------------

blissLomoLtpPrimary : Attribution.AttributedSource
blissLomoLtpPrimary = Attribution.mkDOISource
  "Tim V. P. Bliss; Terje Lomo"
  "Long-lasting potentiation of synaptic transmission in the dentate area of the anaesthetized rabbit following stimulation of the perforant path"
  "The Journal of Physiology 232(2), 331-356"
  "1973"
  "10.1113/jphysiol.1973.sp010273"
  "https://doi.org/10.1113/jphysiol.1973.sp010273"
  Attribution.academicArticleSource
  "primary electrophysiological LTP experiment; supports a synaptic-plasticity mechanism in its preparation, not a complete theory of human learning, understanding, autobiographical memory or trauma"
  Attribution.publicAttribution

naderReconsolidationPrimary : Attribution.AttributedSource
naderReconsolidationPrimary = Prior.naderReconsolidationSource

schillerReconsolidationPrimary : Attribution.AttributedSource
schillerReconsolidationPrimary = Prior.schillerReconsolidationUpdateSource

bayerReconsolidationBoundaryReview : Attribution.AttributedSource
bayerReconsolidationBoundaryReview = Attribution.mkDOISource
  "Hugo Bayer; Leandro J. Bertoglio; Stephen Maren; Cristina A. J. Stern"
  "Windows of change: Revisiting temporal and molecular dynamics of memory reconsolidation and persistence"
  "Neuroscience & Biobehavioral Reviews 174, 106198"
  "2025"
  "10.1016/j.neubiorev.2025.106198"
  "https://doi.org/10.1016/j.neubiorev.2025.106198"
  Attribution.academicArticleSource
  "review of temporal/molecular reconsolidation boundary conditions; motivates consumer-specific mechanism gates and does not promote a universal reconsolidation window or treatment claim"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Regression 1: apparent understanding/performance cannot recover mechanism.
------------------------------------------------------------------------

data UnderstandingCase : Set where
  sameUnderstandingBehaviourMechanismA sameUnderstandingBehaviourMechanismB : UnderstandingCase

data UnderstandingSurface : Set where sameIntelligentPerformance : UnderstandingSurface
data MechanismStatus : Set where neuralMechanismA neuralMechanismB : MechanismStatus

understandingSurface : UnderstandingCase → UnderstandingSurface
understandingSurface _ = sameIntelligentPerformance

mechanismStatus : UnderstandingCase → MechanismStatus
mechanismStatus sameUnderstandingBehaviourMechanismA = neuralMechanismA
mechanismStatus sameUnderstandingBehaviourMechanismB = neuralMechanismB

understandingMechanismDefect : INF.NonFactorabilityWitness understandingSurface mechanismStatus
understandingMechanismDefect = INF.nonFactorabilityWitness
  sameUnderstandingBehaviourMechanismA sameUnderstandingBehaviourMechanismB refl (λ ())

understandingSurfaceCannotFactorNeuralMechanism :
  INF.FactorsThrough understandingSurface mechanismStatus → ⊥
understandingSurfaceCannotFactorNeuralMechanism =
  INF.witnessRulesOutEveryFlatFactorisation understandingMechanismDefect

------------------------------------------------------------------------
-- Regression 2: neural plasticity observation cannot recover memory-update role.
------------------------------------------------------------------------

data PlasticityCase : Set where
  samePlasticityMemoryUpdate samePlasticityOtherAdaptation : PlasticityCase

data PlasticitySurface : Set where sameNeuralPlasticityObservation : PlasticitySurface
data MemoryUpdateRole : Set where reconsolidationRelevant otherPlasticityRole : MemoryUpdateRole

plasticitySurface : PlasticityCase → PlasticitySurface
plasticitySurface _ = sameNeuralPlasticityObservation

memoryUpdateRole : PlasticityCase → MemoryUpdateRole
memoryUpdateRole samePlasticityMemoryUpdate = reconsolidationRelevant
memoryUpdateRole samePlasticityOtherAdaptation = otherPlasticityRole

plasticityMemoryDefect : INF.NonFactorabilityWitness plasticitySurface memoryUpdateRole
plasticityMemoryDefect = INF.nonFactorabilityWitness
  samePlasticityMemoryUpdate samePlasticityOtherAdaptation refl (λ ())

neuroplasticityCannotFactorReconsolidationRole :
  INF.FactorsThrough plasticitySurface memoryUpdateRole → ⊥
neuroplasticityCannotFactorReconsolidationRole =
  INF.witnessRulesOutEveryFlatFactorisation plasticityMemoryDefect

------------------------------------------------------------------------
-- Regression 3: mechanistic evidence cannot recover therapeutic efficacy.
------------------------------------------------------------------------

data TranslationCase : Set where
  sameMechanismEfficacyPaid sameMechanismEfficacyOpen : TranslationCase

data MechanismSurface : Set where sameMechanisticEvidence : MechanismSurface
data EfficacyStatus : Set where therapeuticEfficacyPaid therapeuticEfficacyOpen : EfficacyStatus

mechanismSurface : TranslationCase → MechanismSurface
mechanismSurface _ = sameMechanisticEvidence

efficacyStatus : TranslationCase → EfficacyStatus
efficacyStatus sameMechanismEfficacyPaid = therapeuticEfficacyPaid
efficacyStatus sameMechanismEfficacyOpen = therapeuticEfficacyOpen

translationDefect : INF.NonFactorabilityWitness mechanismSurface efficacyStatus
translationDefect = INF.nonFactorabilityWitness
  sameMechanismEfficacyPaid sameMechanismEfficacyOpen refl (λ ())

mechanismCannotFactorTherapeuticEfficacy :
  INF.FactorsThrough mechanismSurface efficacyStatus → ⊥
mechanismCannotFactorTherapeuticEfficacy =
  INF.witnessRulesOutEveryFlatFactorisation translationDefect

------------------------------------------------------------------------
-- Exact prior boundary retained.
------------------------------------------------------------------------

priorBoundary : Prior.LearningMemoryTraumaReplicationConsensusBoundary
priorBoundary = Prior.canonicalLearningMemoryTraumaReplicationConsensusBoundary

record LearningUnderstandingCognitionNeuroplasticityBoundary : Set where
  constructor learning-understanding-cognition-neuroplasticity-boundary
  field
    currentFirstLinkReceiptsRevisionSensitive : Bool
    historical2014EdgeNotManufactured : Bool
    qidDeweyDoiCoordinatesRetained : Bool
    primarySourcesDistinguishedFromReviews : Bool
    understandingSeparatedFromNeuralMechanism : Bool
    neuroplasticitySeparatedFromReconsolidation : Bool
    mechanismSeparatedFromTherapeuticEfficacy : Bool
    traumaDiagnosisStillNotPromoted : Bool
    presentAxisVocabularyClaimedComplete : Bool
open LearningUnderstandingCognitionNeuroplasticityBoundary public

canonicalLearningUnderstandingCognitionNeuroplasticityBoundary :
  LearningUnderstandingCognitionNeuroplasticityBoundary
canonicalLearningUnderstandingCognitionNeuroplasticityBoundary =
  learning-understanding-cognition-neuroplasticity-boundary
    true true true true true true true true false
