module DASHI.Wikimedia.IbrahimSnowballAliceBrownSocialPsychologyEthicsBidiExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSocialPsychologyEthicsSecondOrderExact as Prior
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Alice
import DASHI.Biology.BrownKimberGovernanceProfileBridge as BrownKimber

------------------------------------------------------------------------
-- ALICE BROWN <-> SOCIAL PSYCHOLOGY / ETHICS BIDI SNOWBALL
--
-- External identities inspected 2026-09-10:
--   psychology         Q9418
--   sociology          Q21201
--   social psychology  Q161272
--   ethics             Q9465
--   philosophy         Q5891
--   teaching           Q352842
--   parenting          Q1217379
--
-- External graph structure proposes candidate seams only.  Alice Brown's
-- source-bound observer/agency and Brown-Kimber coordinate-wise governance
-- constrain those parent meanings in reverse.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Alice Brown / Ibrahim BIDI snowball"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10")

psychologyQid : Identity.ExternalIdentityDemand
psychologyQid = mkQid "psychology" "Q9418"

sociologyQid : Identity.ExternalIdentityDemand
sociologyQid = mkQid "sociology" "Q21201"

socialPsychologyQid : Identity.ExternalIdentityDemand
socialPsychologyQid = mkQid "social psychology" "Q161272"

ethicsQid : Identity.ExternalIdentityDemand
ethicsQid = mkQid "ethics" "Q9465"

philosophyQid : Identity.ExternalIdentityDemand
philosophyQid = mkQid "philosophy" "Q5891"

teachingQid : Identity.ExternalIdentityDemand
teachingQid = mkQid "teaching" "Q352842"

parentingQid : Identity.ExternalIdentityDemand
parentingQid = mkQid "parenting" "Q1217379"

------------------------------------------------------------------------
-- Exact BIDI regression 1: identical participation/response surface cannot
-- recover whether affected subjects have constitutive authority in the inquiry.
------------------------------------------------------------------------

data ParticipationCase : Set where
  sameResponseFeedbackOnly sameResponseConstitutiveVoice : ParticipationCase

data ParticipationSurface : Set where sameObservedParticipation : ParticipationSurface

data GovernanceReading : Set where informationOnly constitutiveAuthority : GovernanceReading

participationSurface : ParticipationCase → ParticipationSurface
participationSurface _ = sameObservedParticipation

governanceReading : ParticipationCase → GovernanceReading
governanceReading sameResponseFeedbackOnly = informationOnly
governanceReading sameResponseConstitutiveVoice = constitutiveAuthority

participationGovernanceDefect :
  INF.NonFactorabilityWitness participationSurface governanceReading
participationGovernanceDefect = INF.nonFactorabilityWitness
  sameResponseFeedbackOnly sameResponseConstitutiveVoice refl (λ ())

participationCannotFactorGovernanceAuthority :
  INF.FactorsThrough participationSurface governanceReading → ⊥
participationCannotFactorGovernanceAuthority =
  INF.witnessRulesOutEveryFlatFactorisation participationGovernanceDefect

------------------------------------------------------------------------
-- Exact BIDI regression 2: the same descriptive social-psychology observation
-- cannot recover the ethical status of an intervention when consent,
-- contestability, refusal, or authority relations differ.
------------------------------------------------------------------------

data InterventionCase : Set where
  sameEffectContestable sameEffectNoncontestable : InterventionCase

data EffectSurface : Set where sameObservedEffect : EffectSurface

data EthicalGovernanceReading : Set where contestableContext noncontestableContext : EthicalGovernanceReading

effectSurface : InterventionCase → EffectSurface
effectSurface _ = sameObservedEffect

ethicalGovernanceReading : InterventionCase → EthicalGovernanceReading
ethicalGovernanceReading sameEffectContestable = contestableContext
ethicalGovernanceReading sameEffectNoncontestable = noncontestableContext

effectEthicsDefect : INF.NonFactorabilityWitness effectSurface ethicalGovernanceReading
effectEthicsDefect = INF.nonFactorabilityWitness
  sameEffectContestable sameEffectNoncontestable refl (λ ())

socialEffectCannotFactorEthicalGovernance :
  INF.FactorsThrough effectSurface ethicalGovernanceReading → ⊥
socialEffectCannotFactorEthicalGovernance =
  INF.witnessRulesOutEveryFlatFactorisation effectEthicsDefect

------------------------------------------------------------------------
-- Existing Alice Brown boundaries reused directly.
------------------------------------------------------------------------

aliceBoundary : Alice.AliceInstitutionalChoiceBoundary
aliceBoundary = Alice.canonicalAliceInstitutionalChoiceBoundary

formalOptionStillDoesNotCreateAgency : Alice.FormalOptionPromotesAgency → ⊥
formalOptionStillDoesNotCreateAgency = Alice.formalOptionDoesNotPromoteAgency

parentReportStillDoesNotCreateChildVoice :
  Alice.ParentReportPromotesChildVoiceIdentity → ⊥
parentReportStillDoesNotCreateChildVoice =
  Alice.parentReportDoesNotPromoteChildVoiceIdentity

institutionRecordStillDoesNotCreateWholeSystem :
  Alice.InstitutionRecordPromotesWholeSystemView → ⊥
institutionRecordStillDoesNotCreateWholeSystem =
  Alice.institutionRecordDoesNotPromoteWholeSystemView

feedbackStillHasNoConstitutiveAuthority :
  (coordinate : DASHI.Core.EpistemicInquiryGovernance.InquiryCoordinate) →
  BrownKimber.RefinedStageAuthorises
    DASHI.Biology.StudentVoiceEpistemicAgencyBridge.feedbackSourceStage coordinate → ⊥
feedbackStillHasNoConstitutiveAuthority =
  BrownKimber.feedbackSourceStillHasNoConstitutiveAuthority

------------------------------------------------------------------------
-- WrongType / no-promotion firewalls.
------------------------------------------------------------------------

data SocialPsychologyEqualsStudentVoice : Set where
data ParticipationEqualsAgency : Set where
data ObservedEffectCreatesEthicalPermission : Set where
data ParentVoiceEqualsChildVoice : Set where
data DescriptiveMechanismCreatesNormativeVerdict : Set where

socialPsychologyDoesNotCreateVoice : SocialPsychologyEqualsStudentVoice → ⊥
socialPsychologyDoesNotCreateVoice ()

participationDoesNotCreateAgency : ParticipationEqualsAgency → ⊥
participationDoesNotCreateAgency ()

observedEffectDoesNotCreateEthicalPermission : ObservedEffectCreatesEthicalPermission → ⊥
observedEffectDoesNotCreateEthicalPermission ()

parentVoiceDoesNotBecomeChildVoice : ParentVoiceEqualsChildVoice → ⊥
parentVoiceDoesNotBecomeChildVoice ()

descriptiveMechanismDoesNotCreateNormativeVerdict :
  DescriptiveMechanismCreatesNormativeVerdict → ⊥
descriptiveMechanismDoesNotCreateNormativeVerdict ()

record AliceBrownSocialPsychologyEthicsBidiBoundary : Set where
  constructor alice-brown-social-psychology-ethics-bidi-boundary
  field
    qidsRetainedWhenSafelyResolved : Bool
    observerFibresRemainDistinct : Bool
    participationDoesNotSelfCreateAgency : Bool
    constitutiveAuthorityIsCoordinateWise : Bool
    socialMechanismDoesNotCreateEthicalVerdict : Bool
    ethicalVerdictDoesNotCreatePsychologicalMechanism : Bool
    attributionTravelsWithGraphExpansion : Bool
    twoEyedComparisonMayReopenParentNode : Bool
    presentAxisVocabularyClaimedComplete : Bool
open AliceBrownSocialPsychologyEthicsBidiBoundary public

canonicalAliceBrownSocialPsychologyEthicsBidiBoundary :
  AliceBrownSocialPsychologyEthicsBidiBoundary
canonicalAliceBrownSocialPsychologyEthicsBidiBoundary =
  alice-brown-social-psychology-ethics-bidi-boundary
    true true true true true true true true false

priorBoundary : Prior.SocialPsychologyEthicsSecondOrderBoundary
priorBoundary = Prior.canonicalSocialPsychologyEthicsSecondOrderBoundary

discoveryBoundary : Discovery.SnowballDiscoveryBoundary
discoveryBoundary = Discovery.canonicalSnowballDiscoveryBoundary
