module DASHI.Education.EarlyLearningReappropriationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.BrownKimberGovernanceProfileBridge as BrownKimber
import DASHI.Education.EKindyRelationalCommonsExact as EKindy
import DASHI.Education.EarlyLearningIntersectionalCapabilityExact as Intersectional

------------------------------------------------------------------------
-- CONSERVATIVE RE-APPROPRIATION / ENDORSEMENT BOUNDARY
--
-- The purpose is not to classify persons or infer votes/motives.  It separates
-- (a) a policy atom, (b) the frame in which it is embedded, (c) evidence of
-- transnational/shared political ecology, and (d) the authority effect of an
-- expert endorsement.
------------------------------------------------------------------------

data PolicyAtom : Set where
  familyCarePayment homeLearningResources qualifiedTeacherAccess : PolicyAtom
  universalProfessionalEntitlement publicPedagogicalCommons : PolicyAtom

data PolicyFrame : Set where
  situatedCapabilityFrame parentalSovereigntyFrame institutionalExitFrame : PolicyFrame
  antiWokeFrame publicEntitlementFrame : PolicyFrame

data InfluenceEvidenceClass : Set where
  publicStatement publishedPolicy lobbyingSubmission disclosedDonation : InfluenceEvidenceClass
  sharedConference transnationalNetworkStudy observedFrameConvergence inferredEcology : InfluenceEvidenceClass

data ActorKind : Set where
  childActor familyActor kinCommunityActor educatorActor governmentActor : ActorKind
  politicalPartyActor lobbyActor expertActor transnationalNetworkActor : ActorKind

record FramedPolicyAtom : Set where
  constructor framedPolicyAtom
  field
    atom : PolicyAtom
    frame : PolicyFrame
    provenanceLabel : String

open FramedPolicyAtom public

------------------------------------------------------------------------
-- Same atom, different frame: support for family care is not semantically
-- identical to parental-sovereignty or institutional-exit politics.
------------------------------------------------------------------------

progressiveFamilyCareAtom : FramedPolicyAtom
progressiveFamilyCareAtom =
  framedPolicyAtom familyCarePayment situatedCapabilityFrame
    "family-care recognition within retained professional/public entitlement"

exitFamilyCareAtom : FramedPolicyAtom
exitFamilyCareAtom =
  framedPolicyAtom familyCarePayment institutionalExitFrame
    "family-care payment used as a route for moving public support out of professional provision"

samePolicyAtomDifferentFrame : atom progressiveFamilyCareAtom ≡ atom exitFamilyCareAtom
samePolicyAtomDifferentFrame = refl

------------------------------------------------------------------------
-- Shared frame/evidence is not command or coordination.
------------------------------------------------------------------------

data CoordinationPermission : Set where

data MotiveInferencePermission : Set where

data VoteInferencePermission : Set where

sharedFrameDoesNotProveCoordination : CoordinationPermission → ⊥
sharedFrameDoesNotProveCoordination ()

politicalProvenanceDoesNotProvePrivateMotive : MotiveInferencePermission → ⊥
politicalProvenanceDoesNotProvePrivateMotive ()

conservativeReligiousContextDoesNotProveVote : VoteInferencePermission → ⊥
conservativeReligiousContextDoesNotProveVote ()

------------------------------------------------------------------------
-- Re-appropriation-resistant architecture.
------------------------------------------------------------------------

record ReappropriationResistanceGate : Set where
  constructor reappropriationResistanceGate
  field
    professionalFloorRetained : Bool
    professionalFloorRetainedIsTrue : professionalFloorRetained ≡ true
    qualifiedRelationshipRetained : Bool
    qualifiedRelationshipRetainedIsTrue : qualifiedRelationshipRetained ≡ true
    childPublicEntitlementRetained : Bool
    childPublicEntitlementRetainedIsTrue : childPublicEntitlementRetained ≡ true
    familyRouteAdditionalNotSubstitutionary : Bool
    familyRouteAdditionalNotSubstitutionaryIsTrue : familyRouteAdditionalNotSubstitutionary ≡ true
    supportVariesBySituatedNeed : Bool
    supportVariesBySituatedNeedIsTrue : supportVariesBySituatedNeed ≡ true
    resourcesDoNotReplaceRelationship : Bool
    resourcesDoNotReplaceRelationshipIsTrue : resourcesDoNotReplaceRelationship ≡ true
    nudgesRemainOptionalContextual : Bool
    nudgesRemainOptionalContextualIsTrue : nudgesRemainOptionalContextual ≡ true
    publicSafeguardingRetained : Bool
    publicSafeguardingRetainedIsTrue : publicSafeguardingRetained ≡ true
    curriculumExitNotAutomatic : Bool
    curriculumExitNotAutomaticIsTrue : curriculumExitNotAutomatic ≡ true
    pluralAuthorityRetained : Bool
    pluralAuthorityRetainedIsTrue : pluralAuthorityRetained ≡ true
    commonsNotConditionalOnExit : Bool
    commonsNotConditionalOnExitIsTrue : commonsNotConditionalOnExit ≡ true

open ReappropriationResistanceGate public

canonicalReappropriationResistanceGate : ReappropriationResistanceGate
canonicalReappropriationResistanceGate =
  reappropriationResistanceGate
    true refl true refl true refl true refl true refl
    true refl true refl true refl true refl true refl true refl

------------------------------------------------------------------------
-- Endorsement is itself a governance event.  The question is not only whether
-- an expert likes one atom, but which framing/provenance conditions travel with
-- the public use of that authority.
------------------------------------------------------------------------

data EndorsementScope : Set where
  atomOnly conditionalArchitecture fullProgramme : EndorsementScope

data EndorsementUse : Set where
  faithfulConditionalUse decontextualisedChoiceQuote : EndorsementUse

record ExpertEndorsementReceipt : Set where
  constructor expertEndorsementReceipt
  field
    expertLabel : String
    endorsedAtom : PolicyAtom
    scope : EndorsementScope
    conditionText : String
    resistanceGate : ReappropriationResistanceGate
    quotationConditionsTravel : Bool
    quotationConditionsTravelIsTrue : quotationConditionsTravel ≡ true
    endorsementIsNotProgrammeIdentity : Bool
    endorsementIsNotProgrammeIdentityIsTrue : endorsementIsNotProgrammeIdentity ≡ true

open ExpertEndorsementReceipt public

canonicalConditionalExpertEndorsement : ExpertEndorsementReceipt
canonicalConditionalExpertEndorsement =
  expertEndorsementReceipt
    "education/ECEC expert"
    homeLearningResources
    conditionalArchitecture
    "Support applies only where family/home pathways extend rather than replace professional entitlement and retain relational, equity, safeguarding and public-commons conditions."
    canonicalReappropriationResistanceGate
    true refl true refl

------------------------------------------------------------------------
-- Brown/Kimber connection: being asked for feedback or endorsement is not the
-- same thing as having constitutive authority over the problem framing.
------------------------------------------------------------------------

feedbackSourceStillHasNoConstitutiveAuthority =
  BrownKimber.feedbackSourceStillHasNoConstitutiveAuthority

------------------------------------------------------------------------
-- Constructive witnesses imported from the intersectional/eKindy modules.
------------------------------------------------------------------------

canonicalRelationalLoop : EKindy.RelationalLearningLoop
canonicalRelationalLoop = EKindy.canonicalEKindyRelationalLoop

parentalSovereigntyRejected : Intersectional.parentalSovereigntyOverEveryDomain ≡ false
parentalSovereigntyRejected = refl

reappropriationBoundaryReading : String
reappropriationBoundaryReading =
  "A family-care or home-learning policy atom can be shared across opposed political architectures. Provenance and frame therefore travel separately from the atom. Shared frames do not prove coordination or motive, while expert endorsement is safe only when its architectural conditions remain attached and cannot be silently promoted into endorsement of parental sovereignty, institutional exit, deprofessionalisation or the whole programme."
