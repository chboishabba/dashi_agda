module DASHI.Reasoning.CrossCulturalCompassionAccountabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.DefensiveReversalRepair as Defensive
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared
import DASHI.Governance.SituatedAuthorityRoutingExact as Situated

------------------------------------------------------------------------
-- Cross-cultural compassion / accountability boundary.
--
-- This owner is deliberately role-general.  It formalises three distinctions
-- prompted by practitioner material about family relationships across cultures:
--
--   * cultural and family context can change the cost and feasibility of a
--     boundary without determining the correct boundary for a person;
--   * compassion and causal explanation can coexist with accountability;
--   * a practitioner label such as "emotionally immature" is not a diagnosis,
--     a motive finding, or a proof about any named parent or family.
--
-- The source rows below are attribution coordinates, not imported authority.
------------------------------------------------------------------------

kohliSource : Attr.AttributedSource
kohliSource = Attr.mkNoDOISource
  "Sahaj Kaur Kohli"
  "But What Will People Say? Navigating Mental Health, Identity, Love, and Family Between Cultures"
  "Penguin Life / Penguin Random House"
  "2024"
  "https://www.penguinrandomhouse.com/books/705868/but-what-will-people-say-by-sahaj-kaur-kohli-maed-lgpc/"
  Attr.practitionerSource
  "Practitioner and lived-experience provenance for treating family, community, migration, bicultural identity, safety and relational obligation as relevant coordinates when evaluating therapeutic advice.  It does not establish what any culture, family or person must value, and it does not make any boundary universally safe or correct."
  Attr.publicAttribution

gibsonSource : Attr.AttributedSource
gibsonSource = Attr.mkNoDOISource
  "Lindsay C. Gibson"
  "Disentangling from Emotionally Immature People"
  "New Harbinger Publications"
  "2023"
  "https://www.newharbinger.com/9781648481512/disentangling-from-emotionally-immature-people/"
  Attr.practitionerSource
  "Practitioner provenance for examining coercive relational patterns, emotional domination, self-protection and the difference between understanding another person and surrendering one's own agency.  The source label does not diagnose a named person or prove motive, abuse, incapacity or misconduct."
  Attr.publicAttribution

kagitcibasiAutonomyRelatednessSource : Attr.AttributedSource
kagitcibasiAutonomyRelatednessSource = Attr.mkDOISource
  "Cigdem Kagitcibasi"
  "Autonomy and Relatedness in Cultural Context: Implications for Self and Family"
  "Journal of Cross-Cultural Psychology 36(4), 403-422"
  "2005"
  "10.1177/0022022105275959"
  "https://doi.org/10.1177/0022022105275959"
  Attr.academicArticleSource
  "Academic precedent for treating agency/autonomy and interpersonal relatedness as distinct dimensions that can be jointly present.  It does not prove DASHI's boundary construction, prescribe a boundary for any person, establish facts about a named family, or create clinical, cultural, or moral authority."
  Attr.publicAttribution

crossCulturalCompassionSources : List Attr.AttributedSource
crossCulturalCompassionSources =
  kohliSource ∷
  gibsonSource ∷
  kagitcibasiAutonomyRelatednessSource ∷
  []

crossCulturalCompassionSourceAtlas : Attr.AttributedSourceAtlas
crossCulturalCompassionSourceAtlas = Attr.mkSourceAtlas
  "cross-cultural compassion and accountability sources"
  "DASHI.Reasoning.CrossCulturalCompassionAccountabilityExact"
  crossCulturalCompassionSources
  "Bounded practitioner provenance for situated boundary feasibility and relational vocabulary, plus academic precedent for the compatibility of autonomy/agency with relatedness.  No citation imports proof, diagnosis, a culturally correct action, or authority over a particular relationship."

crossCulturalCompassionSourceCount : Nat
crossCulturalCompassionSourceCount = Attr.sourceCount crossCulturalCompassionSources

crossCulturalCompassionSourceCountIsThree :
  crossCulturalCompassionSourceCount ≡ 3
crossCulturalCompassionSourceCountIsThree = refl

crossCulturalCompassionAtlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority crossCulturalCompassionSourceAtlas ≡ false
crossCulturalCompassionAtlasDoesNotCreateAuthority =
  Attr.atlasCreatesAuthorityIsFalse crossCulturalCompassionSourceAtlas

------------------------------------------------------------------------
-- A boundary decision is situated rather than a one-dimensional command to
-- "put yourself first" or, conversely, to preserve harmony at any cost.
------------------------------------------------------------------------

data NormCoordinate : Set where
  personalValue : NormCoordinate
  familyExpectation : NormCoordinate
  communityExpectation : NormCoordinate
  heritageCultureExpectation : NormCoordinate
  hostCultureExpectation : NormCoordinate
  institutionalExpectation : NormCoordinate

data BoundaryAction : Set where
  continueUnchanged : BoundaryAction
  clarifyExpectation : BoundaryAction
  limitTopic : BoundaryAction
  limitTask : BoundaryAction
  limitAccess : BoundaryAction
  temporaryPause : BoundaryAction
  supportedContact : BoundaryAction
  endContact : BoundaryAction
  unresolvedBoundaryAction : BoundaryAction

record SituatedBoundaryContext : Set where
  constructor situatedBoundaryContext
  field
    salientNorms : List NormCoordinate
    familyDependencyPresent : Bool
    communityDependencyPresent : Bool
    materialDependencyPresent : Bool
    relationalContinuityValued : Bool
    reputationCostPresent : Bool
    practicalRetaliationRiskPresent : Bool
    physicalSafetyRiskPresent : Bool
    exitCostPresent : Bool
    selectedAction : BoundaryAction
    contextReceipt : String

open SituatedBoundaryContext public

record BoundaryAdviceFirewall : Set where
  field
    westernIndividualistAdviceUniversallyApplicable : Bool
    familyHarmonyUniversallyOverridesAutonomy : Bool
    culturalNormDeterminesIndividualPreference : Bool
    dependencyImpliesConsent : Bool
    costlyBoundaryImpliesInvalidBoundary : Bool
    preservingRelationshipImpliesNoBoundary : Bool
    boundaryRequiresEstrangement : Bool
    firewallNote : String

canonicalBoundaryAdviceFirewall : BoundaryAdviceFirewall
canonicalBoundaryAdviceFirewall = record
  { westernIndividualistAdviceUniversallyApplicable = false
  ; familyHarmonyUniversallyOverridesAutonomy = false
  ; culturalNormDeterminesIndividualPreference = false
  ; dependencyImpliesConsent = false
  ; costlyBoundaryImpliesInvalidBoundary = false
  ; preservingRelationshipImpliesNoBoundary = false
  ; boundaryRequiresEstrangement = false
  ; firewallNote =
      "Cultural, family, dependency and safety coordinates alter feasibility and cost.  They do not mechanically choose a person's values, consent, or boundary action."
  }

------------------------------------------------------------------------
-- Compassion and explanation are different coordinates from waiver.
------------------------------------------------------------------------

data ExplanationKind : Set where
  developmentalExplanation : ExplanationKind
  culturalExplanation : ExplanationKind
  traumaExplanation : ExplanationKind
  stressExplanation : ExplanationKind
  neurocognitiveExplanation : ExplanationKind
  situationalExplanation : ExplanationKind
  unknownExplanation : ExplanationKind

record CompassionAccountabilityState : Set where
  constructor compassionAccountabilityState
  field
    explanationKinds : List ExplanationKind
    perspectiveTakingPresent : Bool
    compassionPresent : Bool
    impactRecorded : Bool
    conductParticularised : Bool
    requestedChangeRecorded : Bool
    accountabilityStillLive : Bool
    accessStillNegotiable : Bool
    forgivenessRequired : Bool
    reconciliationRequired : Bool
    responsibilityErasedByExplanation : Bool
    responsibilityErasedByCompassion : Bool
    stateReceipt : String

open CompassionAccountabilityState public

canonicalCompassionAccountabilityState : CompassionAccountabilityState
canonicalCompassionAccountabilityState = compassionAccountabilityState
  (culturalExplanation ∷ developmentalExplanation ∷ [])
  true
  true
  true
  true
  true
  true
  true
  false
  false
  false
  false
  "A person may understand context and retain compassion while keeping impact, requested change, responsibility and access conditions separately reviewable."

compassionDoesNotEraseAccountability :
  responsibilityErasedByCompassion canonicalCompassionAccountabilityState ≡ false
compassionDoesNotEraseAccountability = refl

explanationDoesNotEraseAccountability :
  responsibilityErasedByExplanation canonicalCompassionAccountabilityState ≡ false
explanationDoesNotEraseAccountability = refl

compassionDoesNotRequireForgiveness :
  forgivenessRequired canonicalCompassionAccountabilityState ≡ false
compassionDoesNotRequireForgiveness = refl

compassionDoesNotRequireReconciliation :
  reconciliationRequired canonicalCompassionAccountabilityState ≡ false
compassionDoesNotRequireReconciliation = refl

------------------------------------------------------------------------
-- Audience pressure: "what will people say?" is modelled as a constraint on
-- the decision environment, not as evidence that the audience is correct.
------------------------------------------------------------------------

record AudiencePressure : Set where
  constructor audiencePressure
  field
    anticipatedAudience : String
    anticipatedJudgement : String
    familyReputationLinked : Bool
    belongingCostLinked : Bool
    shameResponseLinked : Bool
    materialConsequenceLinked : Bool
    audienceJudgementTrue : Bool
    audienceJudgementAuthoritative : Bool
    pressureReceipt : String

open AudiencePressure public

canonicalAudiencePressureBoundary : AudiencePressure
canonicalAudiencePressureBoundary = audiencePressure
  "family, community or other socially salient audience"
  "anticipated negative evaluation"
  true
  true
  true
  false
  false
  false
  "Anticipated social judgement may materially constrain choice or belonging without becoming a truth-maker or moral authority."

audienceSalienceDoesNotCreateTruth :
  audienceJudgementTrue canonicalAudiencePressureBoundary ≡ false
audienceSalienceDoesNotCreateTruth = refl

audienceSalienceDoesNotCreateAuthority :
  audienceJudgementAuthoritative canonicalAudiencePressureBoundary ≡ false
audienceSalienceDoesNotCreateAuthority = refl

------------------------------------------------------------------------
-- Non-diagnostic use of "emotionally immature" and related practitioner
-- vocabulary.  Behavioural particulars remain the admissible object.
------------------------------------------------------------------------

record PractitionerLabelBoundary : Set where
  field
    practitionerLabel : String
    labelMayOrganiseQuestions : Bool
    labelDiagnosesNamedPerson : Bool
    labelProvesMotive : Bool
    labelProvesMisconduct : Bool
    labelProvesIncapacity : Bool
    particularsStillRequired : Bool
    chronologyStillRequired : Bool
    authorityBoundary : String

canonicalEmotionallyImmatureLabelBoundary : PractitionerLabelBoundary
canonicalEmotionallyImmatureLabelBoundary = record
  { practitionerLabel = "emotionally immature"
  ; labelMayOrganiseQuestions = true
  ; labelDiagnosesNamedPerson = false
  ; labelProvesMotive = false
  ; labelProvesMisconduct = false
  ; labelProvesIncapacity = false
  ; particularsStillRequired = true
  ; chronologyStillRequired = true
  ; authorityBoundary =
      "Use the label, if at all, as a question-organising practitioner construct.  Findings attach to particular acts, contexts, effects, evidence and chronology rather than to the label itself."
  }

emotionallyImmatureLabelDoesNotDiagnose :
  PractitionerLabelBoundary.labelDiagnosesNamedPerson
    canonicalEmotionallyImmatureLabelBoundary ≡ false
emotionallyImmatureLabelDoesNotDiagnose = refl

emotionallyImmatureLabelDoesNotProveMisconduct :
  PractitionerLabelBoundary.labelProvesMisconduct
    canonicalEmotionallyImmatureLabelBoundary ≡ false
emotionallyImmatureLabelDoesNotProveMisconduct = refl

------------------------------------------------------------------------
-- Care / gratitude / compassion are not substitutes for complaint merits.
-- This mirrors the existing parent-child process template while staying
-- role-general and source-bounded.
------------------------------------------------------------------------

record CareComplaintBoundary : Set where
  field
    careProvided : Bool
    gratitudePresent : Bool
    complaintParticularised : Bool
    careErasesComplaint : Bool
    gratitudeWaivesConsent : Bool
    compassionWaivesBoundary : Bool
    dependencyCreatesMoralSubordination : Bool
    complaintMeritsRemainReviewable : Bool

canonicalCareComplaintBoundary : CareComplaintBoundary
canonicalCareComplaintBoundary = record
  { careProvided = true
  ; gratitudePresent = true
  ; complaintParticularised = true
  ; careErasesComplaint = false
  ; gratitudeWaivesConsent = false
  ; compassionWaivesBoundary = false
  ; dependencyCreatesMoralSubordination = false
  ; complaintMeritsRemainReviewable = true
  }

careDoesNotEraseComplaint :
  CareComplaintBoundary.careErasesComplaint canonicalCareComplaintBoundary ≡ false
careDoesNotEraseComplaint = refl

gratitudeDoesNotWaiveConsent :
  CareComplaintBoundary.gratitudeWaivesConsent canonicalCareComplaintBoundary ≡ false
gratitudeDoesNotWaiveConsent = refl

compassionDoesNotWaiveBoundary :
  CareComplaintBoundary.compassionWaivesBoundary canonicalCareComplaintBoundary ≡ false
compassionDoesNotWaiveBoundary = refl

------------------------------------------------------------------------
-- Positive construction: compassion without self-erasure.
--
-- The earlier boundaries mostly say what does not follow.  This witness is
-- intentionally stronger and constructive: perspective-taking, cultural
-- belonging and continued relationship can coexist with accountability,
-- consent, complaint review and scoped access.  Bounded access is therefore
-- not definitionally estrangement, and relationship preservation is not
-- definitionally self-abandonment.
--
-- Kağıtçıbaşı's autonomy/relatedness model pays only the narrow academic
-- precedent that agency and relatedness need not be collapsed into opposite
-- ends of a single axis.  The record below and its exact fields are DASHI's
-- construction, not a theorem attributed to that source.
------------------------------------------------------------------------

record CompassionWithoutSelfErasure : Set where
  constructor compassionWithoutSelfErasure
  field
    situatedContext : SituatedBoundaryContext
    compassionState : CompassionAccountabilityState
    selectedBoundaryAction : BoundaryAction
    perspectiveTakingRetained : Bool
    continuedRelationshipPossible : Bool
    culturalBelongingPreserved : Bool
    accountabilityPreserved : Bool
    boundedAccessPreserved : Bool
    consentPreserved : Bool
    complaintReviewPreserved : Bool
    forgivenessStillOptional : Bool
    reconciliationStillOptional : Bool
    selfErasureRequired : Bool
    constructionReceipt : String

open CompassionWithoutSelfErasure public

canonicalCompassionWithoutSelfErasureContext : SituatedBoundaryContext
canonicalCompassionWithoutSelfErasureContext = situatedBoundaryContext
  (personalValue
    ∷ familyExpectation
    ∷ communityExpectation
    ∷ heritageCultureExpectation
    ∷ [])
  true
  true
  false
  true
  true
  false
  false
  true
  limitAccess
  "The relationship and cultural belonging remain valued while access is scoped rather than treated as all-or-nothing."

canonicalCompassionWithoutSelfErasure : CompassionWithoutSelfErasure
canonicalCompassionWithoutSelfErasure = compassionWithoutSelfErasure
  canonicalCompassionWithoutSelfErasureContext
  canonicalCompassionAccountabilityState
  limitAccess
  true
  true
  true
  true
  true
  true
  true
  true
  true
  false
  "Constructive witness: perspective-taking plus continued relationship plus cultural belonging plus accountability plus bounded access plus consent plus complaint review, without requiring self-erasure, forgiveness, reconciliation or unrestricted access."

compassionWithoutSelfErasureDoesNotRequireSelfErasure :
  selfErasureRequired canonicalCompassionWithoutSelfErasure ≡ false
compassionWithoutSelfErasureDoesNotRequireSelfErasure = refl

compassionWithoutSelfErasureKeepsAccountability :
  accountabilityPreserved canonicalCompassionWithoutSelfErasure ≡ true
compassionWithoutSelfErasureKeepsAccountability = refl

compassionWithoutSelfErasureKeepsBelonging :
  culturalBelongingPreserved canonicalCompassionWithoutSelfErasure ≡ true
compassionWithoutSelfErasureKeepsBelonging = refl

compassionWithoutSelfErasureKeepsBoundedAccess :
  boundedAccessPreserved canonicalCompassionWithoutSelfErasure ≡ true
compassionWithoutSelfErasureKeepsBoundedAccess = refl

------------------------------------------------------------------------
-- Pareto cross-pollination with the existing relational shared-state and
-- situated-authority owners.
--
-- This is deliberately a weld, not a replacement ontology.  Cultural
-- belonging and continued relationship do not weaken the already-formalised
-- requirements around assent, explicit commitment, complaint/accountability,
-- pause-without-erasure, current authority, or repair capacity.
------------------------------------------------------------------------

record CompassionAuthorityWeld : Set where
  constructor compassionAuthorityWeld
  field
    compassionWitness : CompassionWithoutSelfErasure
    sharedStateInvariants : Shared.SharedStateInvariants
    minimalRepairProtocol : Shared.MinimalRepairProtocol
    situatedAuthorityBoundary : Situated.SituatedAuthorityRoutingBoundary
    weldReceipt : String

open CompassionAuthorityWeld public

canonicalCompassionAuthorityWeld : CompassionAuthorityWeld
canonicalCompassionAuthorityWeld = compassionAuthorityWeld
  canonicalCompassionWithoutSelfErasure
  Shared.canonicalSharedStateInvariants
  Shared.canonicalMinimalRepairProtocol
  Situated.canonicalSituatedAuthorityRoutingBoundary
  "The positive compassion/belonging witness composes with existing shared-state and situated-authority constraints; it does not promote belonging, care or community standing into assent, obligation or authority."

sharedStateSilenceStillNeedsAssentWitness : Bool
sharedStateSilenceStillNeedsAssentWitness =
  Shared.silenceNeverPromotedToAssentWithoutWitness
    (sharedStateInvariants canonicalCompassionAuthorityWeld)

sharedStateFutureObligationStillNeedsCommitment : Bool
sharedStateFutureObligationStillNeedsCommitment =
  Shared.futureObligationsRequireExplicitCommitment
    (sharedStateInvariants canonicalCompassionAuthorityWeld)

sharedStateCareAndAccountabilityRemainDistinct : Bool
sharedStateCareAndAccountabilityRemainDistinct =
  Shared.careAndAccountabilityRemainDistinct
    (sharedStateInvariants canonicalCompassionAuthorityWeld)

minimalRepairStillPermitsPauseWithoutErasure : Bool
minimalRepairStillPermitsPauseWithoutErasure =
  Shared.permitPauseWithoutErasure
    (minimalRepairProtocol canonicalCompassionAuthorityWeld)

situatedRouteStillRequiresCurrentAuthority : Bool
situatedRouteStillRequiresCurrentAuthority =
  Situated.routeAdmissibilityRequiresCurrentAuthority
    (situatedAuthorityBoundary canonicalCompassionAuthorityWeld)

situatedRouteStillRequiresRepairCapacity : Bool
situatedRouteStillRequiresRepairCapacity =
  Situated.routeAdmissibilityRequiresRepairCapacity
    (situatedAuthorityBoundary canonicalCompassionAuthorityWeld)

------------------------------------------------------------------------
-- Compatibility with the existing defensive-reversal owner: the new source
-- lane does not weaken its requirement to reconstruct incidents and preserve
-- both the initiating event and the delivery of the objection.
------------------------------------------------------------------------

canonicalRepairSequenceStillApplies : Defensive.RepairSequence
canonicalRepairSequenceStillApplies = Defensive.canonicalRepairSequence
