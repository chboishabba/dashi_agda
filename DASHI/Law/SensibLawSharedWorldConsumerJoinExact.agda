module DASHI.Law.SensibLawSharedWorldConsumerJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S19 SHARED WORLD / CONSUMER-RELATIVE JOIN
--
-- The same reviewed coordinate may serve several consumers only when it lies
-- in each consumer's dependency slice and an explicit review admits the join.
-- Citation, same-QID and ontology adjacency may propose a join; they are not
-- themselves dependency proofs.
------------------------------------------------------------------------

data JoinBasis : Set where
  citation treatment sameSource sameSemanticRef sameQid ontologyAdjacency
  conceptAdjacency explicitDependency : JoinBasis

record SharedCoordinate : Set where
  constructor sharedCoordinate
  field
    coordinateRef : String
    semanticRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open SharedCoordinate public

record ConsumerDependencySlice : Set₁ where
  constructor consumerDependencySlice
  field
    consumerRef : String
    coordinateRequired : String → Set
    sliceRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false

open ConsumerDependencySlice public

record JoinProposal : Set where
  constructor joinProposal
  field
    proposalRef : String
    sourceConsumerRef : String
    targetConsumerRef : String
    coordinateRef : String
    basis : JoinBasis
    evidenceRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false

open JoinProposal public

record ReviewedJoinWitness
    (coordinate : SharedCoordinate)
    (slice : ConsumerDependencySlice) : Set₁ where
  constructor reviewedJoinWitness
  field
    dependencyMembership :
      coordinateRequired slice (SharedCoordinate.coordinateRef coordinate)
    reviewRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsClaimTruth : Bool
    createsClaimTruthIsFalse : createsClaimTruth ≡ false

open ReviewedJoinWitness public

data ProposalAutomaticallyJoin : Set where
data SameQidAutomaticallyJoin : Set where
data CitationAutomaticallyJoin : Set where
data JoinCollapsesConsumerOntologies : Set where
data ReuseCreatesClaimTruth : Set where

proposalCannotEstablishJoin : ProposalAutomaticallyJoin → ⊥
proposalCannotEstablishJoin ()

sameQidCannotEstablishJoin : SameQidAutomaticallyJoin → ⊥
sameQidCannotEstablishJoin ()

citationCannotEstablishJoin : CitationAutomaticallyJoin → ⊥
citationCannotEstablishJoin ()

joinDoesNotCollapseConsumers : JoinCollapsesConsumerOntologies → ⊥
joinDoesNotCollapseConsumers ()

reuseDoesNotCreateTruth : ReuseCreatesClaimTruth → ⊥
reuseDoesNotCreateTruth ()

------------------------------------------------------------------------
-- Concrete cross-matter specimen: one native-title authority coordinate is
-- required by Mabo and Yindjibarndi slices, but not by the Pabai climate-duty
-- slice.  The strings are identifiers only; the membership proofs carry the
-- join semantics.
------------------------------------------------------------------------

nativeTitleAuthority : SharedCoordinate
nativeTitleAuthority =
  sharedCoordinate
    "coordinate:native-title-authority"
    "semantic:native-title-authority"
    true refl false refl false refl

data YindjibarndiNeed : String → Set where
  needsNativeTitleAuthority :
    YindjibarndiNeed "coordinate:native-title-authority"

data PabaiNeed : String → Set where
  needsClimateDutyAuthority :
    PabaiNeed "coordinate:climate-duty-authority"

yindjibarndiSlice : ConsumerDependencySlice
yindjibarndiSlice =
  consumerDependencySlice
    "consumer:yindjibarndi"
    YindjibarndiNeed
    "slice:yindjibarndi"
    true refl false refl

pabaiSlice : ConsumerDependencySlice
pabaiSlice =
  consumerDependencySlice
    "consumer:pabai"
    PabaiNeed
    "slice:pabai"
    true refl false refl

yindjibarndiReviewedReuse :
  ReviewedJoinWitness nativeTitleAuthority yindjibarndiSlice
yindjibarndiReviewedReuse =
  reviewedJoinWitness
    needsNativeTitleAuthority
    "review:yindjibarndi-native-title-join"
    true refl false refl false refl

data PabaiNativeTitleDependency : Set where

nativeTitleCoordinateDoesNotPayPabaiDuty :
  PabaiNativeTitleDependency → ⊥
nativeTitleCoordinateDoesNotPayPabaiDuty ()

record SharedWorldConsumerJoinBoundary : Set where
  constructor sharedWorldConsumerJoinBoundary
  field
    joinIsConsumerRelativeDependency : Bool
    joinIsConsumerRelativeDependencyIsTrue :
      joinIsConsumerRelativeDependency ≡ true

    proposalBasisAloneEstablishesJoin : Bool
    proposalBasisAloneEstablishesJoinIsFalse :
      proposalBasisAloneEstablishesJoin ≡ false

    reviewedCoordinateMayBeReusedAcrossConsumers : Bool
    reviewedCoordinateMayBeReusedAcrossConsumersIsTrue :
      reviewedCoordinateMayBeReusedAcrossConsumers ≡ true

    reuseCollapsesDistinctLegalConsumers : Bool
    reuseCollapsesDistinctLegalConsumersIsFalse :
      reuseCollapsesDistinctLegalConsumers ≡ false

    alreadyPaidCoordinateMayQuotientResearch : Bool
    alreadyPaidCoordinateMayQuotientResearchIsTrue :
      alreadyPaidCoordinateMayQuotientResearch ≡ true

    sharedReuseCreatesClaimTruth : Bool
    sharedReuseCreatesClaimTruthIsFalse :
      sharedReuseCreatesClaimTruth ≡ false

open SharedWorldConsumerJoinBoundary public

canonicalSharedWorldConsumerJoinBoundary :
  SharedWorldConsumerJoinBoundary
canonicalSharedWorldConsumerJoinBoundary =
  sharedWorldConsumerJoinBoundary
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
