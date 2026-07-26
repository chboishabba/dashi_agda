module DASHI.Biology.StudentIdentifiedSupportStrategiesBridge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Sources
import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Student-identified online-learning support families.
--
-- These five themes are retained as candidate +1 families sourced from the
-- 2026 Getenet/Burke/Fanshawe/Brown study.  They are related many-to-many to
-- OEF fibres and never promoted to universal prescriptions.

data SupportStrategy : Set where
  autonomyFlexibility : SupportStrategy
  accessibleCentralisedResources : SupportStrategy
  meaningfulInteraction : SupportStrategy
  selfOrganisation : SupportStrategy
  guidedScaffolding : SupportStrategy

canonicalSupportStrategies : List SupportStrategy
canonicalSupportStrategies =
  autonomyFlexibility
  ∷ accessibleCentralisedResources
  ∷ meaningfulInteraction
  ∷ selfOrganisation
  ∷ guidedScaffolding
  ∷ []

supportStrategyName : SupportStrategy → String
supportStrategyName autonomyFlexibility = "learner autonomy and flexibility"
supportStrategyName accessibleCentralisedResources = "accessible and centralised resources"
supportStrategyName meaningfulInteraction = "meaningful interaction with peers and teachers"
supportStrategyName selfOrganisation = "self-organisation"
supportStrategyName guidedScaffolding = "guided scaffolding"

supportCandidatesFor : OEF.OEFElement → List SupportStrategy
supportCandidatesFor OEF.social =
  meaningfulInteraction ∷ guidedScaffolding ∷ []
supportCandidatesFor OEF.cognitive =
  guidedScaffolding ∷ meaningfulInteraction ∷ []
supportCandidatesFor OEF.behavioural =
  selfOrganisation ∷ accessibleCentralisedResources ∷ autonomyFlexibility ∷ []
supportCandidatesFor OEF.collaborative =
  meaningfulInteraction ∷ guidedScaffolding ∷ []
supportCandidatesFor OEF.emotional =
  autonomyFlexibility ∷ guidedScaffolding ∷ meaningfulInteraction ∷ []

record StrategyRoutingRow : Set where
  constructor mkStrategyRoutingRow
  field
    engagementFibre : OEF.OEFElement
    candidateStrategies : List SupportStrategy
    candidatesMatchCanonicalRouting :
      candidateStrategies ≡ supportCandidatesFor engagementFibre
    sourceBound : Bool
    sourceBoundIsTrue : sourceBound ≡ true
    localChoiceRequired : Bool
    localChoiceRequiredIsTrue : localChoiceRequired ≡ true
    noUniversalInterventionClaim : Bool
    noUniversalInterventionClaimIsTrue :
      noUniversalInterventionClaim ≡ true
    note : String

open StrategyRoutingRow public

canonicalSocialRouting : StrategyRoutingRow
canonicalSocialRouting =
  mkStrategyRoutingRow OEF.social (supportCandidatesFor OEF.social) refl
    true refl true refl true refl
    "Social-engagement residuals may route attention toward meaningful interaction and scaffolding, subject to student choice and local context."

canonicalCognitiveRouting : StrategyRoutingRow
canonicalCognitiveRouting =
  mkStrategyRoutingRow OEF.cognitive (supportCandidatesFor OEF.cognitive) refl
    true refl true refl true refl
    "Cognitive-engagement residuals may route attention toward guided scaffolding and meaningful interaction, without assuming a universal causal handle."

canonicalBehaviouralRouting : StrategyRoutingRow
canonicalBehaviouralRouting =
  mkStrategyRoutingRow OEF.behavioural (supportCandidatesFor OEF.behavioural) refl
    true refl true refl true refl
    "Behavioural-engagement residuals may route attention toward self-organisation, accessible resources and autonomy/flexibility."

canonicalCollaborativeRouting : StrategyRoutingRow
canonicalCollaborativeRouting =
  mkStrategyRoutingRow OEF.collaborative (supportCandidatesFor OEF.collaborative) refl
    true refl true refl true refl
    "Collaborative-engagement residuals may route attention toward interaction and scaffolding."

canonicalEmotionalRouting : StrategyRoutingRow
canonicalEmotionalRouting =
  mkStrategyRoutingRow OEF.emotional (supportCandidatesFor OEF.emotional) refl
    true refl true refl true refl
    "Emotional-engagement residuals may route attention toward flexibility, scaffolding and chosen interaction, with no wellbeing or treatment inference."

canonicalStrategyRoutingRows : List StrategyRoutingRow
canonicalStrategyRoutingRows =
  canonicalSocialRouting
  ∷ canonicalCognitiveRouting
  ∷ canonicalBehaviouralRouting
  ∷ canonicalCollaborativeRouting
  ∷ canonicalEmotionalRouting
  ∷ []

record StudentIdentifiedSupportStrategiesBridge : Set where
  constructor mkStudentIdentifiedSupportStrategiesBridge
  field
    sourcePaper : Sources.PaperReference
    sourcePaperIsCanonical :
      sourcePaper ≡ Sources.onlineSupportStrategiesPaper
    sourceResponseCount : Nat
    sourceResponseCountIs584 : sourceResponseCount ≡ 584
    supportStrategies : List SupportStrategy
    supportStrategiesAreCanonical :
      supportStrategies ≡ canonicalSupportStrategies
    routingRows : List StrategyRoutingRow
    routingRowsAreCanonical : routingRows ≡ canonicalStrategyRoutingRows
    manyToManyRoutingPreserved : Bool
    manyToManyRoutingPreservedIsTrue : manyToManyRoutingPreserved ≡ true
    studentChoiceRequired : Bool
    studentChoiceRequiredIsTrue : studentChoiceRequired ≡ true
    noAutomaticCausalEffect : Bool
    noAutomaticCausalEffectIsTrue : noAutomaticCausalEffect ≡ true
    noUniversalPrescription : Bool
    noUniversalPrescriptionIsTrue : noUniversalPrescription ≡ true
    reading : String

open StudentIdentifiedSupportStrategiesBridge public

canonicalStudentIdentifiedSupportStrategiesBridge :
  StudentIdentifiedSupportStrategiesBridge
canonicalStudentIdentifiedSupportStrategiesBridge =
  mkStudentIdentifiedSupportStrategiesBridge
    Sources.onlineSupportStrategiesPaper refl
    584 refl
    canonicalSupportStrategies refl
    canonicalStrategyRoutingRows refl
    true refl
    true refl
    true refl
    true refl
    "The five student-identified support themes supply candidate +1 families for OEF residuals. The relation is many-to-many and remains local, optional and reviewable; the study does not establish a universal intervention table or causal effect."
