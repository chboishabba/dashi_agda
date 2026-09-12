module DASHI.Biology.AliceBrownThreadInquirySynthesisExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Provenance-bounded synthesis of the conversation thread around Alice Brown,
-- early-childhood child voice / wellbeing, and HERDSA SoTL capacity-building.
--
-- IMPORTANT: thread-supplied project claims are not promoted to Alice-source
-- claims. Existing repository theorem owners remain authoritative for the
-- boundaries they already establish.
------------------------------------------------------------------------

data EvidenceClass : Set where
  repoSourceBound : EvidenceClass
  threadSupplied : EvidenceClass
  crossThreadInference : EvidenceClass
  empiricalHypothesis : EvidenceClass
  unresolved : EvidenceClass

data Theme : Set where
  childVoiceParticipation : Theme
  responsiveWellbeingPedagogy : Theme
  protectiveBehavioursPrevention : Theme
  SoTLParticipationBarrier : Theme
  enablingLeadership : Theme
  inclusiveLeadership : Theme
  pedagogicalDesignLeadership : Theme
  valuesBasedLeadership : Theme
  learnerEmpathy : Theme
  disciplinedCuration : Theme
  capabilityExpansionWithoutDomination : Theme
  effectivenessEvidence : Theme
  snowballReferent : Theme

record ThemeReceipt : Set where
  constructor themeReceipt
  field
    theme : Theme
    evidenceClass : EvidenceClass
    provenance : String
    boundary : String

open ThemeReceipt public

canonicalThemeReceipts : List ThemeReceipt
canonicalThemeReceipts =
  themeReceipt childVoiceParticipation repoSourceBound
    "Alice Brown corpus / StudentVoiceEpistemicAgencyBridge and early-years stakeholder coverage"
    "Invitation, survey or feedback capture does not automatically become voice, agency or partnership."
  ∷ themeReceipt responsiveWellbeingPedagogy threadSupplied
    "Conversation-supplied Responsive Wellbeing Pedagogy Framework and design-principle discussion"
    "The thread-supplied framework is not promoted to an Alice-source claim or universal wellbeing effect."
  ∷ themeReceipt protectiveBehavioursPrevention threadSupplied
    "Conversation-supplied protective-behaviours / preventive-health application"
    "Capability support and policy alignment do not by themselves establish child outcomes or causal prevention effects."
  ∷ themeReceipt SoTLParticipationBarrier threadSupplied
    "Conversation-supplied HERDSA project background and cited SoTL barrier literature"
    "Interest in SoTL and resource availability do not imply meaningful or sustained participation."
  ∷ themeReceipt enablingLeadership crossThreadInference
    "Thread leadership account cross-pollinated with repository agency / capability surfaces"
    "Making tacit expertise explicit should expand reachability without manufacturing participant authority or dependence."
  ∷ themeReceipt inclusiveLeadership crossThreadInference
    "Thread leadership account cross-pollinated with participation / choice boundaries"
    "Lowering entry barriers does not entail lowering scholarly standards."
  ∷ themeReceipt pedagogicalDesignLeadership crossThreadInference
    "Thread module-design account cross-pollinated with candidate support / scaffolding surfaces"
    "Scaffolding and sequencing remain supports, not universal prescriptions."
  ∷ themeReceipt valuesBasedLeadership crossThreadInference
    "Thread leadership account cross-pollinated with agency and non-domination boundaries"
    "Normalising uncertainty does not waive methodological soundness or evidence obligations."
  ∷ themeReceipt learnerEmpathy crossThreadInference
    "Thread-defined value: empathy for the learner"
    "Empathy is represented as disciplined attention to useful complexity, not dilution of intellectual demand."
  ∷ themeReceipt disciplinedCuration crossThreadInference
    "Thread design practice: remove nonessential expert-preferred content, rewrite dense material accessibly"
    "Content completeness is not identified with learner usefulness; simplification is not identified with dilution."
  ∷ themeReceipt capabilityExpansionWithoutDomination repoSourceBound
    "Existing early-years capability / empowerment lane"
    "Reachability may increase while choice, decline, contestability and authority boundaries remain intact."
  ∷ themeReceipt effectivenessEvidence threadSupplied
    "Conversation-supplied presentation/webinar, expert-review and post-launch participant feedback"
    "Positive response supports bounded usefulness/confidence claims but not causal sector-wide effectiveness."
  ∷ themeReceipt snowballReferent unresolved
    "Earlier repository search found no explicit Snowball referent"
    "No source-backed Snowball construct is introduced until explicit provenance is supplied."
  ∷ []

------------------------------------------------------------------------
-- Anti-collapse routes. Admissible candidate routes preserve distinctions;
-- blocked routes encode the thread's recurrent overclaim boundaries.
------------------------------------------------------------------------

data Never : Set where

data PromotionRoute : Set where
  capabilityExpandingSupportRoute : PromotionRoute
  responsiveParticipationRoute : PromotionRoute
  accessEqualsAgencyRoute : PromotionRoute
  invitationEqualsVoiceRoute : PromotionRoute
  scaffoldingEqualsPrescriptionRoute : PromotionRoute
  lowerThresholdEqualsLowerStandardRoute : PromotionRoute
  simplificationEqualsDilutionRoute : PromotionRoute
  expertGuidanceEqualsExpertControlRoute : PromotionRoute
  adultObservationEqualsChildExperienceRoute : PromotionRoute
  confidenceEqualsMethodologicalSoundnessRoute : PromotionRoute
  positiveFeedbackEqualsCausalEffectivenessRoute : PromotionRoute
  frameworkEqualsUniversalEffectRoute : PromotionRoute
  policyAlignmentEqualsDemonstratedOutcomeRoute : PromotionRoute

AdmissiblePromotionRoute : PromotionRoute → Set
AdmissiblePromotionRoute capabilityExpandingSupportRoute = ⊤
AdmissiblePromotionRoute responsiveParticipationRoute = ⊤
AdmissiblePromotionRoute accessEqualsAgencyRoute = Never
AdmissiblePromotionRoute invitationEqualsVoiceRoute = Never
AdmissiblePromotionRoute scaffoldingEqualsPrescriptionRoute = Never
AdmissiblePromotionRoute lowerThresholdEqualsLowerStandardRoute = Never
AdmissiblePromotionRoute simplificationEqualsDilutionRoute = Never
AdmissiblePromotionRoute expertGuidanceEqualsExpertControlRoute = Never
AdmissiblePromotionRoute adultObservationEqualsChildExperienceRoute = Never
AdmissiblePromotionRoute confidenceEqualsMethodologicalSoundnessRoute = Never
AdmissiblePromotionRoute positiveFeedbackEqualsCausalEffectivenessRoute = Never
AdmissiblePromotionRoute frameworkEqualsUniversalEffectRoute = Never
AdmissiblePromotionRoute policyAlignmentEqualsDemonstratedOutcomeRoute = Never

accessDoesNotEqualAgency : AdmissiblePromotionRoute accessEqualsAgencyRoute → Never
accessDoesNotEqualAgency ()

invitationDoesNotEqualVoice : AdmissiblePromotionRoute invitationEqualsVoiceRoute → Never
invitationDoesNotEqualVoice ()

scaffoldingDoesNotEqualPrescription :
  AdmissiblePromotionRoute scaffoldingEqualsPrescriptionRoute → Never
scaffoldingDoesNotEqualPrescription ()

lowerThresholdDoesNotLowerStandard :
  AdmissiblePromotionRoute lowerThresholdEqualsLowerStandardRoute → Never
lowerThresholdDoesNotLowerStandard ()

simplificationDoesNotEqualDilution :
  AdmissiblePromotionRoute simplificationEqualsDilutionRoute → Never
simplificationDoesNotEqualDilution ()

expertGuidanceDoesNotEqualControl :
  AdmissiblePromotionRoute expertGuidanceEqualsExpertControlRoute → Never
expertGuidanceDoesNotEqualControl ()

adultObservationDoesNotEqualChildExperience :
  AdmissiblePromotionRoute adultObservationEqualsChildExperienceRoute → Never
adultObservationDoesNotEqualChildExperience ()

confidenceDoesNotEqualMethodologicalSoundness :
  AdmissiblePromotionRoute confidenceEqualsMethodologicalSoundnessRoute → Never
confidenceDoesNotEqualMethodologicalSoundness ()

positiveFeedbackDoesNotEqualCausalEffectiveness :
  AdmissiblePromotionRoute positiveFeedbackEqualsCausalEffectivenessRoute → Never
positiveFeedbackDoesNotEqualCausalEffectiveness ()

frameworkDoesNotEqualUniversalEffect :
  AdmissiblePromotionRoute frameworkEqualsUniversalEffectRoute → Never
frameworkDoesNotEqualUniversalEffect ()

policyAlignmentDoesNotEqualDemonstratedOutcome :
  AdmissiblePromotionRoute policyAlignmentEqualsDemonstratedOutcomeRoute → Never
policyAlignmentDoesNotEqualDemonstratedOutcome ()

------------------------------------------------------------------------
-- Bounded responsive-wellbeing surface. This records the conversation-level
-- synthesis only; it is not an empirical theorem about a named framework.
------------------------------------------------------------------------

record ResponsiveWellbeingSurface : Set where
  constructor responsiveWellbeingSurface
  field
    childPerspectiveRequiredForDirectChildExperienceClaim : Bool
    meaningfulParticipationBeyondInvitation : Bool
    adultInterpretationRemainsPartial : Bool
    sustainedRelationalAccessRelevant : Bool
    responsivenessToSituatedChangeRelevant : Bool
    evidenceReviewAndRevisionRelevant : Bool
    universalWellbeingEffectEstablished : Bool

canonicalResponsiveWellbeingSurface : ResponsiveWellbeingSurface
canonicalResponsiveWellbeingSurface =
  responsiveWellbeingSurface true true true true true true false

------------------------------------------------------------------------
-- Bounded SoTL leadership/capability surface.
------------------------------------------------------------------------

record SoTLLeadershipSurface : Set where
  constructor soTLLeadershipSurface
  field
    tacitExpertPracticeMadeExplicit : Bool
    barriersLowered : Bool
    scholarlyStandardsRetained : Bool
    scaffoldingAvailable : Bool
    localChoiceRetained : Bool
    uncertaintyNormalised : Bool
    learnerDisciplinaryContextRetained : Bool
    confidenceSupported : Bool
    methodologicalSoundnessStillRequired : Bool
    expertControlManufactured : Bool

canonicalSoTLLeadershipSurface : SoTLLeadershipSurface
canonicalSoTLLeadershipSurface =
  soTLLeadershipSurface true true true true true true true true true false

------------------------------------------------------------------------
-- Effectiveness evidence remains bounded unless stronger causal design is
-- supplied.
------------------------------------------------------------------------

record EffectivenessBoundary : Set where
  constructor effectivenessBoundary
  field
    positiveSectorResponseObserved : Bool
    positiveExpertReviewObserved : Bool
    participantConfidenceReportsObserved : Bool
    reportedPracticeChangeObserved : Bool
    longTermPracticeChangeIndependentlyVerified : Bool
    sectorWideCausalEffectEstablished : Bool

canonicalEffectivenessBoundary : EffectivenessBoundary
canonicalEffectivenessBoundary =
  effectivenessBoundary true true true true false false

------------------------------------------------------------------------
-- Aggregate certificate for this inquiry thread.
------------------------------------------------------------------------

record AliceBrownThreadInquirySynthesis : Set where
  constructor aliceBrownThreadInquirySynthesis
  field
    receipts : List ThemeReceipt
    receiptsAreCanonical : receipts ≡ canonicalThemeReceipts
    wellbeingSurface : ResponsiveWellbeingSurface
    wellbeingSurfaceIsCanonical : wellbeingSurface ≡ canonicalResponsiveWellbeingSurface
    leadershipSurface : SoTLLeadershipSurface
    leadershipSurfaceIsCanonical : leadershipSurface ≡ canonicalSoTLLeadershipSurface
    effectivenessBoundary : EffectivenessBoundary
    effectivenessBoundaryIsCanonical : effectivenessBoundary ≡ canonicalEffectivenessBoundary
    capabilityRoute : PromotionRoute
    capabilityRouteIsCanonical : capabilityRoute ≡ capabilityExpandingSupportRoute
    capabilityRouteAdmissible : AdmissiblePromotionRoute capabilityRoute
    participationRoute : PromotionRoute
    participationRouteIsCanonical : participationRoute ≡ responsiveParticipationRoute
    participationRouteAdmissible : AdmissiblePromotionRoute participationRoute
    aliceSourceClaimsRemainDistinctFromThreadClaims : Bool
    aliceSourceClaimsRemainDistinctFromThreadClaimsIsTrue :
      aliceSourceClaimsRemainDistinctFromThreadClaims ≡ true
    unresolvedSnowballNotPromoted : Bool
    unresolvedSnowballNotPromotedIsTrue : unresolvedSnowballNotPromoted ≡ true
    reading : String

open AliceBrownThreadInquirySynthesis public

canonicalAliceBrownThreadInquirySynthesis : AliceBrownThreadInquirySynthesis
canonicalAliceBrownThreadInquirySynthesis =
  aliceBrownThreadInquirySynthesis
    canonicalThemeReceipts refl
    canonicalResponsiveWellbeingSurface refl
    canonicalSoTLLeadershipSurface refl
    canonicalEffectivenessBoundary refl
    capabilityExpandingSupportRoute refl tt
    responsiveParticipationRoute refl tt
    true refl
    true refl
    "Across the thread, responsive pedagogy and enabling leadership share a bounded theorem shape: increase reachability and capability while preserving local agency, scholarly or safety standards, provenance, contestability and revision. The synthesis does not collapse conversation-supplied projects into Alice-source claims, and reported effectiveness is not promoted to causal effectiveness without additional evidence."
