module DASHI.Wikimedia.IbrahimSnowballSocialPsychologyEthicsSecondOrderExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballChildPsychologyDissentParentingSecondOrderExact as Prior

------------------------------------------------------------------------
-- SECOND-ORDER BIDI WALK: SOCIAL PSYCHOLOGY <-> PSYCHOLOGY/SOCIOLOGY,
-- ETHICS <-> PHILOSOPHY.
--
-- Current Wikidata identities inspected 2026-09-10:
--   social psychology Q161272
--   psychology        Q9418
--   sociology         Q21201
--   ethics            Q9465
--   philosophy        Q5891
--
-- External graph relations nominate search seams only. A descriptive account
-- of social influence is not an ethical verdict; an ethical classification is
-- not a psychological causal mechanism.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim social-psychology/ethics second-order walk"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10")

socialPsychologyQid : Identity.ExternalIdentityDemand
socialPsychologyQid = mkQid "social psychology" "Q161272"

psychologyQid : Identity.ExternalIdentityDemand
psychologyQid = mkQid "psychology" "Q9418"

sociologyQid : Identity.ExternalIdentityDemand
sociologyQid = mkQid "sociology" "Q21201"

ethicsQid : Identity.ExternalIdentityDemand
ethicsQid = mkQid "ethics" "Q9465"

philosophyQid : Identity.ExternalIdentityDemand
philosophyQid = mkQid "philosophy" "Q5891"

------------------------------------------------------------------------
-- BIDI regression: same social-behaviour surface can differ in ethical status
-- because context/authority/consent/harm can differ. Therefore social-psychology
-- description alone cannot factor an ethical verdict.
------------------------------------------------------------------------

data SocialBehaviourCase : Set where
  sameBehaviourConsensual sameBehaviourCoercive : SocialBehaviourCase

data SocialBehaviourSurface : Set where sameSocialBehaviour : SocialBehaviourSurface

data EthicalReading : Set where ethicallyPermissible ethicallyProblematic : EthicalReading

socialBehaviourSurface : SocialBehaviourCase → SocialBehaviourSurface
socialBehaviourSurface _ = sameSocialBehaviour

ethicalReading : SocialBehaviourCase → EthicalReading
ethicalReading sameBehaviourConsensual = ethicallyPermissible
ethicalReading sameBehaviourCoercive = ethicallyProblematic

socialBehaviourEthicsDefect :
  INF.NonFactorabilityWitness socialBehaviourSurface ethicalReading
socialBehaviourEthicsDefect = INF.nonFactorabilityWitness
  sameBehaviourConsensual sameBehaviourCoercive refl (λ ())

socialBehaviourCannotFactorEthicalVerdict :
  INF.FactorsThrough socialBehaviourSurface ethicalReading → ⊥
socialBehaviourCannotFactorEthicalVerdict =
  INF.witnessRulesOutEveryFlatFactorisation socialBehaviourEthicsDefect

------------------------------------------------------------------------
-- Reverse regression: same ethical label need not identify the psychological
-- or sociological mechanism producing the observed behaviour.
------------------------------------------------------------------------

data EthicalLabelCase : Set where
  sameEthicalLabelPeerNorm sameEthicalLabelAuthorityCommand : EthicalLabelCase

data EthicalLabelSurface : Set where sameEthicalLabel : EthicalLabelSurface

data SocialMechanism : Set where peerNormMechanism authorityCommandMechanism : SocialMechanism

ethicalLabelSurface : EthicalLabelCase → EthicalLabelSurface
ethicalLabelSurface _ = sameEthicalLabel

socialMechanism : EthicalLabelCase → SocialMechanism
socialMechanism sameEthicalLabelPeerNorm = peerNormMechanism
socialMechanism sameEthicalLabelAuthorityCommand = authorityCommandMechanism

ethicalLabelMechanismDefect :
  INF.NonFactorabilityWitness ethicalLabelSurface socialMechanism
ethicalLabelMechanismDefect = INF.nonFactorabilityWitness
  sameEthicalLabelPeerNorm sameEthicalLabelAuthorityCommand refl (λ ())

ethicalLabelCannotFactorSocialMechanism :
  INF.FactorsThrough ethicalLabelSurface socialMechanism → ⊥
ethicalLabelCannotFactorSocialMechanism =
  INF.witnessRulesOutEveryFlatFactorisation ethicalLabelMechanismDefect

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SocialPsychologyEqualsPsychology : Set where
data SocialPsychologyEqualsSociology : Set where
data EthicsEqualsPsychology : Set where
data EthicsEqualsSociology : Set where
data DescriptiveMechanismCreatesEthicalVerdict : Set where
data EthicalVerdictCreatesPsychologicalMechanism : Set where

socialPsychologyDoesNotCollapseToPsychology : SocialPsychologyEqualsPsychology → ⊥
socialPsychologyDoesNotCollapseToPsychology ()

socialPsychologyDoesNotCollapseToSociology : SocialPsychologyEqualsSociology → ⊥
socialPsychologyDoesNotCollapseToSociology ()

ethicsDoesNotBecomePsychology : EthicsEqualsPsychology → ⊥
ethicsDoesNotBecomePsychology ()

ethicsDoesNotBecomeSociology : EthicsEqualsSociology → ⊥
ethicsDoesNotBecomeSociology ()

descriptionDoesNotCreateNormativeVerdict : DescriptiveMechanismCreatesEthicalVerdict → ⊥
descriptionDoesNotCreateNormativeVerdict ()

normativeVerdictDoesNotCreateMechanism : EthicalVerdictCreatesPsychologicalMechanism → ⊥
normativeVerdictDoesNotCreateMechanism ()

record SocialPsychologyEthicsSecondOrderBoundary : Set where
  constructor social-psychology-ethics-second-order-boundary
  field
    qidsRetainedWhenSafelyResolved : Bool
    socialPsychologyBridgesPsychologyAndSociologyWithoutIdentity : Bool
    ethicsRetainsPhilosophySourceRole : Bool
    descriptiveAndNormativeConsumersRemainDistinct : Bool
    factorsThroughCheckedBidirectionally : Bool
    attributionTravelsWithClaims : Bool
    presentVocabularyClaimedComplete : Bool
open SocialPsychologyEthicsSecondOrderBoundary public

canonicalSocialPsychologyEthicsSecondOrderBoundary : SocialPsychologyEthicsSecondOrderBoundary
canonicalSocialPsychologyEthicsSecondOrderBoundary =
  social-psychology-ethics-second-order-boundary true true true true true true false

priorBoundary : Prior.ChildSecondOrderSnowballBoundary
priorBoundary = Prior.canonicalChildSecondOrderSnowballBoundary

discoveryBoundary : Discovery.SnowballDiscoveryBoundary
discoveryBoundary = Discovery.canonicalSnowballDiscoveryBoundary
