module DASHI.Wikimedia.IbrahimSnowballSocialInfluenceConsentCoercionPrimarySourcesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSocialPsychologyEthicsSecondOrderExact as Prior

------------------------------------------------------------------------
-- THIRD-ORDER ACTIVE-LANE WALK:
-- social psychology -> social influence / peer pressure
-- conformity/obedience -> consent/coercion discriminators
-- plus exact primary empirical sources for classic conformity/obedience tasks.
--
-- QID identity, graph adjacency and publication evidence remain separate roles.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim social-influence/consent/coercion walk"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity checked 2026-09-10")

socialInfluenceQid : Identity.ExternalIdentityDemand
socialInfluenceQid = mkQid "social influence" "Q1307337"

peerPressureQid : Identity.ExternalIdentityDemand
peerPressureQid = mkQid "peer pressure" "Q784843"

coercionQid : Identity.ExternalIdentityDemand
coercionQid = mkQid "coercion" "Q325980"

consentQid : Identity.ExternalIdentityDemand
consentQid = mkQid "consent" "Q231043"

milgramExperimentQid : Identity.ExternalIdentityDemand
milgramExperimentQid = mkQid "Milgram experiment" "Q191474"

asch1951WorkQid : Identity.ExternalIdentityDemand
asch1951WorkQid = mkQid
  "Effects of group pressure upon the modification and distortion of judgments"
  "Q130231918"

------------------------------------------------------------------------
-- Exact primary-source attribution. These publications own their empirical
-- reports. DASHI owns only the source-bounded graph/formalisation weld.
------------------------------------------------------------------------

asch1956Attribution : Attribution.ScientificWorkAttribution
asch1956Attribution = Attribution.scientific-work-attribution
  "Solomon E. Asch"
  "Studies of Independence and Conformity: I. A Minority of One Against a Unanimous Majority"
  "Psychological Monographs: General and Applied 70(9), 1-70"
  Attribution.namedAuthor
  Attribution.primaryPublicationRecord
  "DOI 10.1037/h0093718"
  "Primary conformity experiment/report about independence and conformity under unanimous group pressure; bounded to its task, sample, design and measurements."
  Attribution.externalSourceOwner

milgram1963Attribution : Attribution.ScientificWorkAttribution
milgram1963Attribution = Attribution.scientific-work-attribution
  "Stanley Milgram"
  "Behavioral Study of obedience"
  "The Journal of Abnormal and Social Psychology 67(4), 371-378"
  Attribution.namedAuthor
  Attribution.primaryPublicationRecord
  "DOI 10.1037/h0040525; PMID 14049516"
  "Primary laboratory obedience report using experimenter commands and a shock-generator task; bounded to that experimental carrier and dependent variable."
  Attribution.externalSourceOwner

record DashiSourceWeldAttribution : Set where
  constructor dashi-source-weld-attribution
  field
    sourceClaimsRemainExternal : Bool
    graphWeldOwner : Attribution.ClaimOwner
    dashiOwnsGraphWeld : graphWeldOwner ≡ Attribution.dashiFormalisationOwner
    crossSourceInferenceOwner : Attribution.ClaimOwner
    dashiOwnsCrossSourceInference : crossSourceInferenceOwner ≡ Attribution.dashiInferenceOwner

canonicalDashiSourceWeldAttribution : DashiSourceWeldAttribution
canonicalDashiSourceWeldAttribution =
  dashi-source-weld-attribution true Attribution.dashiFormalisationOwner refl Attribution.dashiInferenceOwner refl

------------------------------------------------------------------------
-- Mechanism discriminator: identical visible compliance cannot recover whether
-- the relation was peer pressure, authority instruction, coercion or consent.
------------------------------------------------------------------------

data ComplianceContext : Set where
  peerPressureCase authorityInstructionCase coerciveCase consensualCase : ComplianceContext

data ComplianceSurface : Set where sameVisibleCompliance : ComplianceSurface

data RelationReading : Set where peerPressureReading authorityReading coercionReading consentReading : RelationReading

complianceSurface : ComplianceContext → ComplianceSurface
complianceSurface _ = sameVisibleCompliance

relationReading : ComplianceContext → RelationReading
relationReading peerPressureCase = peerPressureReading
relationReading authorityInstructionCase = authorityReading
relationReading coerciveCase = coercionReading
relationReading consensualCase = consentReading

peerAuthorityDefect : INF.NonFactorabilityWitness complianceSurface relationReading
peerAuthorityDefect = INF.nonFactorabilityWitness
  peerPressureCase authorityInstructionCase refl (λ ())

complianceCannotFactorRelation : INF.FactorsThrough complianceSurface relationReading → ⊥
complianceCannotFactorRelation = INF.witnessRulesOutEveryFlatFactorisation peerAuthorityDefect

------------------------------------------------------------------------
-- Snowball acquisition/payment: later source/method evidence may be retained,
-- but QIDs/publications do not pay mechanism, ethics, transport or authority.
------------------------------------------------------------------------

record SocialInfluenceAcquisitionState : Set where
  constructor social-influence-acquisition-state
  field
    qidsAcquired : Bool
    aschPrimarySourceAcquired : Bool
    milgramPrimarySourceAcquired : Bool
    taskProtocolAcquired : Bool
    participantPopulationAcquired : Bool
    responseMeasureAcquired : Bool
    refusalOrDissentEvidenceAcquired : Bool
    distressEvidenceAcquired : Bool
    ethicsContextAcquired : Bool
    replicationEvidenceAcquired : Bool
    outOfOrderEvidenceRetained : Bool
open SocialInfluenceAcquisitionState public

record SocialInfluencePaymentState : Set where
  constructor social-influence-payment-state
  field
    qidIdentityPaid : Bool
    exactPublicationIdentityPaid : Bool
    sourceRolePaid : Bool
    taskCarrierPaid : Bool
    samplePopulationPaid : Bool
    responseMeasurePaid : Bool
    conformityVsObediencePaid : Bool
    consentVsCoercionPaid : Bool
    privateBeliefPaid : Bool
    ethicsPermissionPaid : Bool
    replicationPaid : Bool
    populationTransportPaid : Bool
    recommendationPaid : Bool
    firstUnpaidGateReference : String
open SocialInfluencePaymentState public

snowballAcquisitionDoesNotAdvanceSocialInfluencePayment :
  SocialInfluenceAcquisitionState → SocialInfluencePaymentState → SocialInfluencePaymentState
snowballAcquisitionDoesNotAdvanceSocialInfluencePayment _ payment = payment

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data QidCreatesExperimentEvidence : Set where
data AschCreatesUniversalConformityLaw : Set where
data MilgramCreatesLegitimateAuthority : Set where
data ComplianceCreatesPrivateBelief : Set where
data HistoricalExperimentCreatesCurrentEthicalPermission : Set where
data PeerPressureEqualsCoercion : Set where
data ConsentEqualsCompliance : Set where

data CitationTransfersAuthorshipToDashi : Set where

qidDoesNotCreateExperimentEvidence : QidCreatesExperimentEvidence → ⊥
qidDoesNotCreateExperimentEvidence ()

aschDoesNotCreateUniversalConformityLaw : AschCreatesUniversalConformityLaw → ⊥
aschDoesNotCreateUniversalConformityLaw ()

milgramDoesNotCreateLegitimateAuthority : MilgramCreatesLegitimateAuthority → ⊥
milgramDoesNotCreateLegitimateAuthority ()

complianceDoesNotCreatePrivateBelief : ComplianceCreatesPrivateBelief → ⊥
complianceDoesNotCreatePrivateBelief ()

historicalExperimentDoesNotCreateCurrentEthicalPermission :
  HistoricalExperimentCreatesCurrentEthicalPermission → ⊥
historicalExperimentDoesNotCreateCurrentEthicalPermission ()

peerPressureDoesNotEqualCoercion : PeerPressureEqualsCoercion → ⊥
peerPressureDoesNotEqualCoercion ()

consentDoesNotEqualCompliance : ConsentEqualsCompliance → ⊥
consentDoesNotEqualCompliance ()

citationDoesNotTransferAuthorshipToDashi : CitationTransfersAuthorshipToDashi → ⊥
citationDoesNotTransferAuthorshipToDashi ()

attributionBoundary : AttributionSnowball.AttributionSnowballBoundary
attributionBoundary = AttributionSnowball.canonicalAttributionSnowballBoundary

priorBoundary : Prior.SocialPsychologyEthicsSecondOrderBoundary
priorBoundary = Prior.canonicalSocialPsychologyEthicsSecondOrderBoundary
