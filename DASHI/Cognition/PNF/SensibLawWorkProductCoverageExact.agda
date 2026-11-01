module DASHI.Cognition.PNF.SensibLawWorkProductCoverageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMatterWorkspaceProjectionExact as Matter

------------------------------------------------------------------------
-- M14.A Matter-native Work Product Coverage boundary.
--
-- This is a projection over the already-landed Matter workspace.  It does
-- not introduce a second world, a new truth carrier, or a work-product-owned
-- semantic ontology.
------------------------------------------------------------------------

data WorkProductMatterRelation : Set where
  exactSupport equivalentSupport explicitDispute implicitDispute :
    WorkProductMatterRelation
  partialOverlap adjacentEvent substitution proceduralNonanswer unrelated :
    WorkProductMatterRelation

data WorkProductRelationRoot : Set where
  supports invalidates nonResolving unanswered : WorkProductRelationRoot

relationRoot : WorkProductMatterRelation → WorkProductRelationRoot
relationRoot exactSupport = supports
relationRoot equivalentSupport = supports
relationRoot explicitDispute = invalidates
relationRoot implicitDispute = invalidates
relationRoot partialOverlap = supports
relationRoot adjacentEvent = nonResolving
relationRoot substitution = nonResolving
relationRoot proceduralNonanswer = nonResolving
relationRoot unrelated = unanswered

data ForwardCoverageStatus : Set where
  supported qualified contradicted unreviewed unsupported :
    ForwardCoverageStatus

data ReverseCoverageStatus : Set where
  represented possiblyOmitted excludedByScope notExpectedForProduct
    unreviewedForOmission : ReverseCoverageStatus

record WorkProductPropositionOccurrence : Set where
  constructor work-product-proposition-occurrence
  field
    occurrenceRef : String
    workProductRef : String
    statementRef : String
    sourceRevisionRef : String
    exactSpanRef : String
    candidatePNFRef : String
    productPropositionRef : String
    candidateSearchReceiptRef : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open WorkProductPropositionOccurrence public

record WorkProductCoverageJudgment : Set where
  constructor work-product-coverage-judgment
  field
    occurrenceRef : String
    workProductSpanRef : String
    productPropositionRef : String
    matterPropositionRef : String
    relation : WorkProductMatterRelation
    status : ForwardCoverageStatus
    workProductSourceRefs : List String
    matterAncestryRefs : List String
    comparisonReceiptRefs : List String
    reviewRef : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open WorkProductCoverageJudgment public

record MatterOmissionJudgment : Set where
  constructor matter-omission-judgment
  field
    matterPropositionRef : String
    status : ReverseCoverageStatus
    expectationBasisRef : String
    resolvingOccurrenceRefs : List String
    matterAncestryRefs : List String
    reviewRef : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse :
      applicabilityPromoted ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open MatterOmissionJudgment public

record WorkProductCoverageBoundary : Set where
  constructor work-product-coverage-boundary
  field
    reusesMatterWorkspace : Bool
    reusesMatterWorkspaceIsTrue : reusesMatterWorkspace ≡ true

    workProductUsesOrdinarySourceTrace : Bool
    workProductUsesOrdinarySourceTraceIsTrue :
      workProductUsesOrdinarySourceTrace ≡ true

    forwardCoverageDistinctFromReverseOmission : Bool
    forwardCoverageDistinctFromReverseOmissionIsTrue :
      forwardCoverageDistinctFromReverseOmission ≡ true

    exactWorkProductSpanReopenable : Bool
    exactWorkProductSpanReopenableIsTrue :
      exactWorkProductSpanReopenable ≡ true

    matterAncestryReopenable : Bool
    matterAncestryReopenableIsTrue :
      matterAncestryReopenable ≡ true

    unsupportedKeepsCandidateSearchReceipt : Bool
    unsupportedKeepsCandidateSearchReceiptIsTrue :
      unsupportedKeepsCandidateSearchReceipt ≡ true

    workProductWordingCreatesSemanticAuthority : Bool
    workProductWordingCreatesSemanticAuthorityIsFalse :
      workProductWordingCreatesSemanticAuthority ≡ false

    supportedMeansLegalSufficiency : Bool
    supportedMeansLegalSufficiencyIsFalse :
      supportedMeansLegalSufficiency ≡ false

    contradictedMeansFalse : Bool
    contradictedMeansFalseIsFalse :
      contradictedMeansFalse ≡ false

    unsupportedMeansFalse : Bool
    unsupportedMeansFalseIsFalse :
      unsupportedMeansFalse ≡ false

    noMatterMatchMeansFalse : Bool
    noMatterMatchMeansFalseIsFalse :
      noMatterMatchMeansFalse ≡ false

    omissionMeansShouldInclude : Bool
    omissionMeansShouldIncludeIsFalse :
      omissionMeansShouldInclude ≡ false

    productRedactionDeletesCanonicalSource : Bool
    productRedactionDeletesCanonicalSourceIsFalse :
      productRedactionDeletesCanonicalSource ≡ false

    coverageJudgmentMutatesMatter : Bool
    coverageJudgmentMutatesMatterIsFalse :
      coverageJudgmentMutatesMatter ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse :
      claimTruthPromoted ≡ false

open WorkProductCoverageBoundary public

canonicalWorkProductCoverageBoundary : WorkProductCoverageBoundary
canonicalWorkProductCoverageBoundary =
  work-product-coverage-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data WorkProductWordingIsSemanticAuthority : Set where
data SupportedCoverageIsLegalSufficiency : Set where
data ContradictedCoverageMeansFalse : Set where
data UnsupportedCoverageMeansFalse : Set where
data NoMatterMatchMeansFalse : Set where
data PossiblyOmittedMeansShouldInclude : Set where
data ForwardCoverageIsReverseOmission : Set where
data ProductRedactionDeletesCanonicalSource : Set where
data CoverageJudgmentMutatesMatter : Set where

workProductWordingDoesNotCreateSemanticAuthority :
  WorkProductWordingIsSemanticAuthority → ⊥
workProductWordingDoesNotCreateSemanticAuthority ()

supportedCoverageDoesNotEstablishLegalSufficiency :
  SupportedCoverageIsLegalSufficiency → ⊥
supportedCoverageDoesNotEstablishLegalSufficiency ()

contradictedCoverageDoesNotMeanFalse :
  ContradictedCoverageMeansFalse → ⊥
contradictedCoverageDoesNotMeanFalse ()

unsupportedCoverageDoesNotMeanFalse :
  UnsupportedCoverageMeansFalse → ⊥
unsupportedCoverageDoesNotMeanFalse ()

noMatterMatchDoesNotMeanFalse :
  NoMatterMatchMeansFalse → ⊥
noMatterMatchDoesNotMeanFalse ()

possiblyOmittedDoesNotMeanShouldInclude :
  PossiblyOmittedMeansShouldInclude → ⊥
possiblyOmittedDoesNotMeanShouldInclude ()

forwardCoverageIsNotReverseOmission :
  ForwardCoverageIsReverseOmission → ⊥
forwardCoverageIsNotReverseOmission ()

productRedactionDoesNotDeleteCanonicalSource :
  ProductRedactionDeletesCanonicalSource → ⊥
productRedactionDoesNotDeleteCanonicalSource ()

coverageJudgmentDoesNotMutateMatter :
  CoverageJudgmentMutatesMatter → ⊥
coverageJudgmentDoesNotMutateMatter ()
