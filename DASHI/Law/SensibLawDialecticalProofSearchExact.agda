module DASHI.Law.SensibLawDialecticalProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query

------------------------------------------------------------------------
-- DIALECTICAL / EPISTEMIC SEARCH DISCIPLINE
--
-- Search for a proposed proof payment together with structurally relevant
-- defeaters, comparators and counterexamples. "Antithesis" here is a DASHI
-- search role, not a claim that legal doctrine is mechanically Hegelian.
------------------------------------------------------------------------

data EpistemicSearchRole : Set where
  supportRole
  defeaterRole
  comparatorRole
  contradictionRole
  counterexampleRole
  vocabularyDiscoveryRole
  authorityDiscoveryRole
  : EpistemicSearchRole

data DefeaterKind : Set where
  separationOfPowersDefeater
  policyOrInstitutionalCompetenceDefeater
  statutorySchemeCoherenceDefeater
  indeterminacyDefeater
  nonJusticiabilityDefeater
  authorityHierarchyDefeater
  temporalValidityDefeater
  factualDiscriminatorDefeater
  otherDeclaredDefeater
  : DefeaterKind

record DialecticalProbePair : Set₁ where
  constructor dialecticalProbePair
  field
    targetPropositionReference : String
    supportingHypothesis : Query.SearchHypothesis
    defeatingHypothesis : Query.SearchHypothesis
    defeaterKind : DefeaterKind
    sharedConsumerReceipt : Set
    pairReference : String

open DialecticalProbePair public

record SearchDiscriminator : Set where
  constructor searchDiscriminator
  field
    propositionReference : String
    supportShapeReference : String
    defeaterShapeReference : String
    distinguishingCoordinateReference : String
    discriminatorReference : String

open SearchDiscriminator public

record DialecticalSearchPlan : Set₁ where
  constructor dialecticalSearchPlan
  field
    thesisReference : String
    supportQueries : List Query.SearchHypothesis
    defeaterQueries : List Query.SearchHypothesis
    comparatorQueries : List Query.SearchHypothesis
    contradictionQueries : List Query.SearchHypothesis
    targetDiscriminator : SearchDiscriminator
    planReference : String

open DialecticalSearchPlan public

------------------------------------------------------------------------
-- Epistemic closure boundary.
------------------------------------------------------------------------

data RetrievedSupportMeansTruth : Set where
data RetrievedDefeaterMeansFalsity : Set where
data MoreSupportMayReplaceDefeaterSearch : Set where
data DialecticalOppositionMeansLogicalNegation : Set where
data SearchDiscriminatorAutomaticallyLegalRule : Set where

supportDoesNotMeanTruth : RetrievedSupportMeansTruth → ⊥
supportDoesNotMeanTruth ()

defeaterDoesNotMeanFalsity : RetrievedDefeaterMeansFalsity → ⊥
defeaterDoesNotMeanFalsity ()

supportDoesNotReplaceDefeaterSearch : MoreSupportMayReplaceDefeaterSearch → ⊥
supportDoesNotReplaceDefeaterSearch ()

dialecticalOppositionNeedNotBeLiteralNegation :
  DialecticalOppositionMeansLogicalNegation → ⊥
dialecticalOppositionNeedNotBeLiteralNegation ()

discriminatorDoesNotBecomeRuleByDiscovery :
  SearchDiscriminatorAutomaticallyLegalRule → ⊥
discriminatorDoesNotBecomeRuleByDiscovery ()

record DialecticalSearchBoundary : Set where
  constructor dialecticalSearchBoundary
  field
    supportAndDefeaterSearchBothFirstClass : Bool
    supportAndDefeaterSearchBothFirstClassIsTrue :
      supportAndDefeaterSearchBothFirstClass ≡ true
    antithesisMustBeLiteralTextualNegation : Bool
    antithesisMustBeLiteralTextualNegationIsFalse :
      antithesisMustBeLiteralTextualNegation ≡ false
    discoveredDiscriminatorEqualsDoctrine : Bool
    discoveredDiscriminatorEqualsDoctrineIsFalse :
      discoveredDiscriminatorEqualsDoctrine ≡ false

canonicalDialecticalSearchBoundary : DialecticalSearchBoundary
canonicalDialecticalSearchBoundary =
  dialecticalSearchBoundary true refl false refl false refl
