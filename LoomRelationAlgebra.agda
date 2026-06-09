module LoomRelationAlgebra where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Primitive using (Setω)

------------------------------------------------------------------------
-- Affidavit-style finite relation algebra for loom reconciliation.
--
-- This imports the shape of the SensibLaw affidavit lane formalism: finite
-- relation labels, coarse relation roots, bucket projection, evidence status,
-- and a separate promotion state. It does not import legal sufficiency or
-- workflow authority into DASHI.

data LoomRelationType : Set where
  exactSupport : LoomRelationType
  equivalentSupport : LoomRelationType
  explicitDispute : LoomRelationType
  implicitDispute : LoomRelationType
  partialOverlap : LoomRelationType
  adjacentEvent : LoomRelationType
  substitution : LoomRelationType
  proceduralNonanswer : LoomRelationType
  unrelated : LoomRelationType

canonicalRelationPrecedence : List LoomRelationType
canonicalRelationPrecedence =
  exactSupport
  ∷ explicitDispute
  ∷ equivalentSupport
  ∷ implicitDispute
  ∷ partialOverlap
  ∷ adjacentEvent
  ∷ substitution
  ∷ proceduralNonanswer
  ∷ unrelated
  ∷ []

data LoomRelationRoot : Set where
  supports : LoomRelationRoot
  invalidates : LoomRelationRoot
  nonResolving : LoomRelationRoot
  unanswered : LoomRelationRoot

relationRootFor : LoomRelationType → LoomRelationRoot
relationRootFor exactSupport = supports
relationRootFor equivalentSupport = supports
relationRootFor explicitDispute = invalidates
relationRootFor implicitDispute = invalidates
relationRootFor partialOverlap = supports
relationRootFor adjacentEvent = nonResolving
relationRootFor substitution = nonResolving
relationRootFor proceduralNonanswer = nonResolving
relationRootFor unrelated = unanswered

data LoomBucket : Set where
  supportedBucket : LoomBucket
  disputedBucket : LoomBucket
  partialSupportBucket : LoomBucket
  adjacentEventBucket : LoomBucket
  substitutionBucket : LoomBucket
  nonSubstantiveResponseBucket : LoomBucket
  missingBucket : LoomBucket

bucketFor : LoomRelationType → LoomBucket
bucketFor exactSupport = supportedBucket
bucketFor equivalentSupport = supportedBucket
bucketFor explicitDispute = disputedBucket
bucketFor implicitDispute = disputedBucket
bucketFor partialOverlap = partialSupportBucket
bucketFor adjacentEvent = adjacentEventBucket
bucketFor substitution = substitutionBucket
bucketFor proceduralNonanswer = nonSubstantiveResponseBucket
bucketFor unrelated = missingBucket

data LoomEvidenceStatus : Set where
  reviewOnly : LoomEvidenceStatus
  witnessed : LoomEvidenceStatus
  blocked : LoomEvidenceStatus
  boundaryOnly : LoomEvidenceStatus
  unresolved : LoomEvidenceStatus

data LoomPromotionState : Set where
  promotionFalse : LoomPromotionState
  promotionPending : LoomPromotionState
  promotionBlocked : LoomPromotionState
  promotedBySeparateContract : LoomPromotionState

record LoomTypedRelation : Set where
  constructor loomTypedRelation
  field
    relationType :
      LoomRelationType

    relationRoot :
      LoomRelationRoot

    relationRootIsDerived :
      relationRoot ≡ relationRootFor relationType

    bucket :
      LoomBucket

    bucketIsDerived :
      bucket ≡ bucketFor relationType

    evidenceStatus :
      LoomEvidenceStatus

    promotionState :
      LoomPromotionState

    relationNote :
      String

record LoomRelationAlgebra : Setω where
  field
    relationTypes :
      List LoomRelationType

    relationTypesAreAffidavitStyle :
      relationTypes
      ≡
      exactSupport
      ∷ equivalentSupport
      ∷ explicitDispute
      ∷ implicitDispute
      ∷ partialOverlap
      ∷ adjacentEvent
      ∷ substitution
      ∷ proceduralNonanswer
      ∷ unrelated
      ∷ []

    relationPrecedence :
      List LoomRelationType

    relationPrecedenceIsCanonical :
      relationPrecedence ≡ canonicalRelationPrecedence

    relationRoots :
      List LoomRelationRoot

    relationRootsAreCanonical :
      relationRoots
      ≡
      supports
      ∷ invalidates
      ∷ nonResolving
      ∷ unanswered
      ∷ []

    evidenceStatuses :
      List LoomEvidenceStatus

    evidenceStatusesAreCanonical :
      evidenceStatuses
      ≡
      reviewOnly
      ∷ witnessed
      ∷ blocked
      ∷ boundaryOnly
      ∷ unresolved
      ∷ []

    promotionStates :
      List LoomPromotionState

    promotionStatesAreCanonical :
      promotionStates
      ≡
      promotionFalse
      ∷ promotionPending
      ∷ promotionBlocked
      ∷ promotedBySeparateContract
      ∷ []

    supportDoesNotPromote :
      LoomTypedRelation

    boundaryDoesNotPromote :
      LoomTypedRelation

    separatesRelationFromPromotion :
      Bool

    separatesRelationFromPromotionIsTrue :
      separatesRelationFromPromotion ≡ true

    formalismBoundary :
      List String

open LoomTypedRelation public
open LoomRelationAlgebra public
open LoomRelationType public
open LoomRelationRoot public
open LoomBucket public
open LoomEvidenceStatus public
open LoomPromotionState public

canonicalSupportRelation : LoomTypedRelation
canonicalSupportRelation =
  loomTypedRelation
    equivalentSupport
    supports
    refl
    supportedBucket
    refl
    witnessed
    promotionFalse
    "Support is a comparison relation only; it is not theorem promotion."

canonicalBoundaryRelation : LoomTypedRelation
canonicalBoundaryRelation =
  loomTypedRelation
    proceduralNonanswer
    nonResolving
    refl
    nonSubstantiveResponseBucket
    refl
    boundaryOnly
    promotionFalse
    "Boundary-only material may be relation-bearing while promotion remains blocked."

canonicalLoomRelationAlgebra : LoomRelationAlgebra
canonicalLoomRelationAlgebra =
  record
    { relationTypes =
        exactSupport
        ∷ equivalentSupport
        ∷ explicitDispute
        ∷ implicitDispute
        ∷ partialOverlap
        ∷ adjacentEvent
        ∷ substitution
        ∷ proceduralNonanswer
        ∷ unrelated
        ∷ []
    ; relationTypesAreAffidavitStyle =
        refl
    ; relationPrecedence =
        canonicalRelationPrecedence
    ; relationPrecedenceIsCanonical =
        refl
    ; relationRoots =
        supports
        ∷ invalidates
        ∷ nonResolving
        ∷ unanswered
        ∷ []
    ; relationRootsAreCanonical =
        refl
    ; evidenceStatuses =
        reviewOnly
        ∷ witnessed
        ∷ blocked
        ∷ boundaryOnly
        ∷ unresolved
        ∷ []
    ; evidenceStatusesAreCanonical =
        refl
    ; promotionStates =
        promotionFalse
        ∷ promotionPending
        ∷ promotionBlocked
        ∷ promotedBySeparateContract
        ∷ []
    ; promotionStatesAreCanonical =
        refl
    ; supportDoesNotPromote =
        canonicalSupportRelation
    ; boundaryDoesNotPromote =
        canonicalBoundaryRelation
    ; separatesRelationFromPromotion =
        true
    ; separatesRelationFromPromotionIsTrue =
        refl
    ; formalismBoundary =
        "This relation algebra mirrors the affidavit-lane classifier shape, not legal sufficiency."
        ∷ "A support relation can remain review-only and non-promoting."
        ∷ "Promotion requires a separate guarded contract and is not implied by bucket assignment."
        ∷ []
    }
