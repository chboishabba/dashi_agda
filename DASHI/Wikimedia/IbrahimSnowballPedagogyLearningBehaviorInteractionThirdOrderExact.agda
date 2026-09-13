module DASHI.Wikimedia.IbrahimSnowballPedagogyLearningBehaviorInteractionThirdOrderExact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballAliceBrownSocialPsychologyEthicsBidiExact as AliceBidi

------------------------------------------------------------------------
-- THIRD-ORDER CHILD / SOCIAL-SCIENCE WALK
--
-- External identities inspected 2026-09-10:
--   teaching           Q352842
--   pedagogy           Q7922
--   learning           Q133500
--   psychology         Q9418
--   human behavior     Q3769299
--   social relation    Q853725
--   social interaction Q609298
--
-- Current Wikidata: teaching is used/faceted by pedagogy and has effect
-- learning; psychology studies human behaviour; social relation is explicitly
-- different from social interaction. These are graph/navigation observations,
-- not causal, normative, or authority proofs.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim third-order pedagogy/behaviour walk"
  "verified external concept identity"
  label Identity.wikidataQid
  (Identity.verified qid "Wikidata identity inspected 2026-09-10")

teachingQid : Identity.ExternalIdentityDemand
teachingQid = mkQid "teaching" "Q352842"

pedagogyQid : Identity.ExternalIdentityDemand
pedagogyQid = mkQid "pedagogy" "Q7922"

learningQid : Identity.ExternalIdentityDemand
learningQid = mkQid "learning" "Q133500"

psychologyQid : Identity.ExternalIdentityDemand
psychologyQid = mkQid "psychology" "Q9418"

humanBehaviorQid : Identity.ExternalIdentityDemand
humanBehaviorQid = mkQid "human behavior" "Q3769299"

socialRelationQid : Identity.ExternalIdentityDemand
socialRelationQid = mkQid "social relation" "Q853725"

socialInteractionQid : Identity.ExternalIdentityDemand
socialInteractionQid = mkQid "social interaction" "Q609298"

------------------------------------------------------------------------
-- Regression 1: same learning outcome cannot recover agency/voice conditions.
------------------------------------------------------------------------

data LearningCase : Set where
  sameLearningContestable sameLearningNoncontestable : LearningCase

data LearningSurface : Set where sameLearningOutcome : LearningSurface

data AgencyReading : Set where learnerCanContest learnerCannotContest : AgencyReading

learningSurface : LearningCase → LearningSurface
learningSurface _ = sameLearningOutcome

agencyReading : LearningCase → AgencyReading
agencyReading sameLearningContestable = learnerCanContest
agencyReading sameLearningNoncontestable = learnerCannotContest

learningAgencyDefect : INF.NonFactorabilityWitness learningSurface agencyReading
learningAgencyDefect = INF.nonFactorabilityWitness
  sameLearningContestable sameLearningNoncontestable refl (λ ())

learningOutcomeCannotFactorAgency :
  INF.FactorsThrough learningSurface agencyReading → ⊥
learningOutcomeCannotFactorAgency =
  INF.witnessRulesOutEveryFlatFactorisation learningAgencyDefect

------------------------------------------------------------------------
-- Regression 2: same visible behaviour cannot recover situated meaning/motive.
------------------------------------------------------------------------

data BehaviorCase : Set where
  sameBehaviorVoluntary sameBehaviorAuthorityDriven : BehaviorCase

data BehaviorSurface : Set where sameVisibleBehavior : BehaviorSurface

data BehaviorMeaning : Set where voluntaryMeaning authorityDrivenMeaning : BehaviorMeaning

behaviorSurface : BehaviorCase → BehaviorSurface
behaviorSurface _ = sameVisibleBehavior

behaviorMeaning : BehaviorCase → BehaviorMeaning
behaviorMeaning sameBehaviorVoluntary = voluntaryMeaning
behaviorMeaning sameBehaviorAuthorityDriven = authorityDrivenMeaning

behaviorMeaningDefect : INF.NonFactorabilityWitness behaviorSurface behaviorMeaning
behaviorMeaningDefect = INF.nonFactorabilityWitness
  sameBehaviorVoluntary sameBehaviorAuthorityDriven refl (λ ())

behaviorCannotFactorSituatedMeaning :
  INF.FactorsThrough behaviorSurface behaviorMeaning → ⊥
behaviorCannotFactorSituatedMeaning =
  INF.witnessRulesOutEveryFlatFactorisation behaviorMeaningDefect

------------------------------------------------------------------------
-- Regression 3: interaction event surface does not recover durable relation.
------------------------------------------------------------------------

data InteractionCase : Set where
  sameInteractionPeerRelation sameInteractionHierarchicalRelation : InteractionCase

data InteractionSurface : Set where sameInteractionEvent : InteractionSurface

data RelationReading : Set where peerRelation hierarchicalRelation : RelationReading

interactionSurface : InteractionCase → InteractionSurface
interactionSurface _ = sameInteractionEvent

relationReading : InteractionCase → RelationReading
relationReading sameInteractionPeerRelation = peerRelation
relationReading sameInteractionHierarchicalRelation = hierarchicalRelation

interactionRelationDefect : INF.NonFactorabilityWitness interactionSurface relationReading
interactionRelationDefect = INF.nonFactorabilityWitness
  sameInteractionPeerRelation sameInteractionHierarchicalRelation refl (λ ())

interactionCannotFactorSocialRelation :
  INF.FactorsThrough interactionSurface relationReading → ⊥
interactionCannotFactorSocialRelation =
  INF.witnessRulesOutEveryFlatFactorisation interactionRelationDefect

------------------------------------------------------------------------
-- WrongType/no-promotion boundaries.
------------------------------------------------------------------------

data TeachingEqualsPedagogy : Set where
data LearningCreatesAgency : Set where
data BehaviorCreatesMotive : Set where
data InteractionEqualsRelation : Set where
data PsychologyCreatesEthicalVerdict : Set where

teachingDoesNotBecomePedagogy : TeachingEqualsPedagogy → ⊥
teachingDoesNotBecomePedagogy ()

learningDoesNotCreateAgency : LearningCreatesAgency → ⊥
learningDoesNotCreateAgency ()

behaviorDoesNotCreateMotive : BehaviorCreatesMotive → ⊥
behaviorDoesNotCreateMotive ()

interactionDoesNotBecomeRelation : InteractionEqualsRelation → ⊥
interactionDoesNotBecomeRelation ()

psychologyDoesNotCreateEthicalVerdict : PsychologyCreatesEthicalVerdict → ⊥
psychologyDoesNotCreateEthicalVerdict ()

record PedagogyLearningBehaviorInteractionBoundary : Set where
  constructor pedagogy-learning-behavior-interaction-boundary
  field
    qidsRetainedWhenSafelyResolved : Bool
    teachingPedagogyLearningRemainDistinct : Bool
    learningOutcomeDoesNotExhaustAgency : Bool
    behaviorDoesNotExhaustSituatedMeaning : Bool
    interactionDoesNotExhaustSocialRelation : Bool
    AliceBrownAgencyConstraintPropagatesUpward : Bool
    attributionTravelsWithGraphExpansion : Bool
    presentVocabularyClaimedComplete : Bool
open PedagogyLearningBehaviorInteractionBoundary public

canonicalPedagogyLearningBehaviorInteractionBoundary :
  PedagogyLearningBehaviorInteractionBoundary
canonicalPedagogyLearningBehaviorInteractionBoundary =
  pedagogy-learning-behavior-interaction-boundary
    true true true true true true true false

aliceBidiBoundary : AliceBidi.AliceBrownSocialPsychologyEthicsBidiBoundary
aliceBidiBoundary = AliceBidi.canonicalAliceBrownSocialPsychologyEthicsBidiBoundary
