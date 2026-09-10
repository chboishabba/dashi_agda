module DASHI.Wikimedia.IbrahimSnowballMoralDevelopmentParentingProsocialityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballChildhoodCategorisationConformityPsychologyBidiExact as Prior

------------------------------------------------------------------------
-- IBRAHIM / SNOWBALL BIDI CONTINUATION
--
-- childhood / social psychology / ethics
--   <-> parenting / child rearing / parenting style
--   <-> moral development / prosocial behaviour
--
-- QIDs are navigation/identity coordinates only. They do not establish causal
-- parenting effects, moral truth, legitimate authority, consent, or source
-- authority. Acquisition may snowball out of order; payment remains gated.
------------------------------------------------------------------------

parentingQid : Identity.ExternalIdentityDemand
parentingQid = Identity.mkOptionalIdentityDemand
  "Ibrahim parenting/moral-development BIDI" "external concept identity"
  "parenting" Identity.wikidataQid
  (Identity.verified "Q1217379" "Wikidata identity checked 2026-09-10")

childRearingQid : Identity.ExternalIdentityDemand
childRearingQid = Identity.mkOptionalIdentityDemand
  "Ibrahim parenting/moral-development BIDI" "external concept identity"
  "child rearing" Identity.wikidataQid
  (Identity.verified "Q69886747" "Wikidata identity checked 2026-09-10; retained separately from parenting")

parentingStyleQid : Identity.ExternalIdentityDemand
parentingStyleQid = Identity.mkOptionalIdentityDemand
  "Ibrahim parenting/moral-development BIDI" "external construct identity"
  "parenting style" Identity.wikidataQid
  (Identity.verified "Q1366259" "Wikidata identity checked 2026-09-10")

moralDevelopmentQid : Identity.ExternalIdentityDemand
moralDevelopmentQid = Identity.mkOptionalIdentityDemand
  "Ibrahim parenting/moral-development BIDI" "external concept identity"
  "moral development" Identity.wikidataQid
  (Identity.verified "Q6909101" "Wikidata identity checked 2026-09-10")

prosocialBehaviourQid : Identity.ExternalIdentityDemand
prosocialBehaviourQid = Identity.mkOptionalIdentityDemand
  "Ibrahim parenting/moral-development BIDI" "external concept identity"
  "prosocial behavior / prosociality" Identity.wikidataQid
  (Identity.verified "Q2990613" "Wikidata identity checked 2026-09-10")

------------------------------------------------------------------------
-- BIDI constraints.
------------------------------------------------------------------------

data ParentingMoralNode : Set where
  parentingNode childRearingNode parentingStyleNode moralDevelopmentNode prosocialNode : ParentingMoralNode

record ParentingMoralAudit : Set where
  constructor parenting-moral-audit
  field
    node : ParentingMoralNode
    upwardReading : String
    downwardConstraint : String
    wrongTypeRisk : String
    qidIsIdentityOnly : Bool
    attributionRequired : Bool
    parentExplainsEveryChildCase : Bool

open ParentingMoralAudit public

parentingAudit : ParentingMoralAudit
parentingAudit = parenting-moral-audit parentingNode
  "raising-a-child parent coordinate spanning care, education, discipline and socialisation"
  "child voice, refusal, dependence, attachment, material care and authority must remain separately observable"
  "parenting != legitimate authority != child assent != developmental benefit"
  true true false

moralDevelopmentAudit : ParentingMoralAudit
moralDevelopmentAudit = parenting-moral-audit moralDevelopmentNode
  "developmental navigation coordinate linking psychology, education, ethics and social learning"
  "reported norm-following or prosocial behaviour cannot recover private reasoning, coercion, autonomy or moral endorsement"
  "moral development != obedience != conformity != externally approved behaviour"
  true true false

prosocialAudit : ParentingMoralAudit
prosocialAudit = parenting-moral-audit prosocialNode
  "social-behaviour coordinate describing intent/behaviour oriented toward benefiting others"
  "surface helping behaviour does not by itself recover motive, voluntariness, cost, authority pressure or ethical justification"
  "prosocial surface != autonomous motive != moral truth"
  true true false

------------------------------------------------------------------------
-- Snowball acquisition/payment split.
------------------------------------------------------------------------

record IbrahimParentingAcquisitionState : Set where
  constructor ibrahim-parenting-acquisition-state
  field
    parentingQidAcquired : Bool
    childRearingQidAcquired : Bool
    parentingStyleQidAcquired : Bool
    moralDevelopmentQidAcquired : Bool
    prosocialQidAcquired : Bool
    exactPrimaryWorkAcquired : Bool
    participantVoiceEvidenceAcquired : Bool
    developmentalOutcomeEvidenceAcquired : Bool
    authorityContextEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool

open IbrahimParentingAcquisitionState public

record IbrahimParentingPaymentState : Set where
  constructor ibrahim-parenting-payment-state
  field
    qidIdentityPaid : Bool
    conceptSenseDisambiguationPaid : Bool
    exactSourceWorkPaid : Bool
    sourceRoleAttributionPaid : Bool
    participantRolePaid : Bool
    authorityContextPaid : Bool
    comparatorDesignPaid : Bool
    measurementValidityPaid : Bool
    developmentalOutcomePaid : Bool
    moralInterpretationPaid : Bool
    transportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String

open IbrahimParentingPaymentState public

snowballAcquisitionDoesNotAdvanceIbrahimParentingPayment :
  IbrahimParentingAcquisitionState → IbrahimParentingPaymentState → IbrahimParentingPaymentState
snowballAcquisitionDoesNotAdvanceIbrahimParentingPayment _ payment = payment

------------------------------------------------------------------------
-- Attribution role remains explicit.
------------------------------------------------------------------------

record IbrahimGraphSourceAdmission : Set where
  constructor ibrahim-graph-source-admission
  field
    sourceReference : String
    sourceStrength : Attribution.SourceStrength
    externalClaimOwner : Attribution.ClaimOwner
    externalOwnerIsSource : externalClaimOwner ≡ Attribution.externalSourceOwner
    qidOrCitationCreatesProof : Bool
    qidOrCitationCreatesDomainAuthority : Bool

open IbrahimGraphSourceAdmission public

attributionSnowballBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionSnowballBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

------------------------------------------------------------------------
-- WrongType barriers.
------------------------------------------------------------------------

data ParentingMeansLegitimateAuthority : Set where
data ChildRearingMeansDevelopmentalBenefit : Set where
data ParentingStyleMeansIndividualParentTruth : Set where
data ProsocialSurfaceMeansAutonomousMotive : Set where
data MoralDevelopmentMeansObedience : Set where
data QidMeansEmpiricalEvidence : Set where
data AcquisitionMeansPayment : Set where

parentingDoesNotCreateLegitimateAuthority : ParentingMeansLegitimateAuthority → ⊥
parentingDoesNotCreateLegitimateAuthority ()

childRearingDoesNotDefinitionallyCreateBenefit : ChildRearingMeansDevelopmentalBenefit → ⊥
childRearingDoesNotDefinitionallyCreateBenefit ()

parentingStyleDoesNotIdentifyIndividualParentTruth : ParentingStyleMeansIndividualParentTruth → ⊥
parentingStyleDoesNotIdentifyIndividualParentTruth ()

prosocialSurfaceDoesNotRecoverAutonomousMotive : ProsocialSurfaceMeansAutonomousMotive → ⊥
prosocialSurfaceDoesNotRecoverAutonomousMotive ()

moralDevelopmentDoesNotEqualObedience : MoralDevelopmentMeansObedience → ⊥
moralDevelopmentDoesNotEqualObedience ()

qidDoesNotCreateEmpiricalEvidence : QidMeansEmpiricalEvidence → ⊥
qidDoesNotCreateEmpiricalEvidence ()

acquisitionDoesNotManufacturePayment : AcquisitionMeansPayment → ⊥
acquisitionDoesNotManufacturePayment ()

record IbrahimParentingMoralBoundary : Set where
  constructor ibrahim-parenting-moral-boundary
  field
    qidsAttachedWhenSafelyResolved : Bool
    parentingAndChildRearingRemainDistinct : Bool
    conformityObedienceProsocialityAndMoralDevelopmentRemainDistinct : Bool
    childVoiceAndAuthorityRemainIndependentAxes : Bool
    attributionTravelsWithEvidence : Bool
    qidCreatesProof : Bool
    acquisitionAdvancesPaymentAutomatically : Bool
    currentAxisVocabularyClaimedComplete : Bool

canonicalIbrahimParentingMoralBoundary : IbrahimParentingMoralBoundary
canonicalIbrahimParentingMoralBoundary =
  ibrahim-parenting-moral-boundary true true true true true false false false

priorBoundary : Prior.ChildhoodCategorisationConformityPsychologyBidiBoundary
priorBoundary = Prior.canonicalChildhoodCategorisationConformityPsychologyBidiBoundary
