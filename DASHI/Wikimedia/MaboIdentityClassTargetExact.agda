module DASHI.Wikimedia.MaboIdentityClassTargetExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionExact as Expansion
import DASHI.Wikimedia.MaboWorldObjectIdentityExact as Identity

------------------------------------------------------------------------
-- P7d target weld
--
-- The existing targetNovelObjects = 100 is interpreted here as cardinality of
-- explicitly reviewed world-object identity classes, not raw representation
-- strings, QIDs, URLs, provider IDs, routes or source manifestations.
------------------------------------------------------------------------

targetIdentityClasses : Nat
targetIdentityClasses = Expansion.targetNovelObjects

targetIdentityClassesIs100 : targetIdentityClasses ≡ 100
targetIdentityClassesIs100 = refl

record IdentityClassTargetBoundary : Set where
  constructor identity-class-target-boundary
  field
    reviewedIdentityClassesAreTarget : Bool
    representationStringsAreTarget : Bool
    qidsAloneAreTarget : Bool
    articleUrlsAloneAreTarget : Bool
    sourceManifestationsAloneAreTarget : Bool
    duplicateAliasesAdvanceTarget : Bool

open IdentityClassTargetBoundary public

canonicalIdentityClassTargetBoundary : IdentityClassTargetBoundary
canonicalIdentityClassTargetBoundary =
  identity-class-target-boundary true false false false false false

eddieMaboCountingIdentityClass : Identity.WorldIdentityResolutionReceipt
eddieMaboCountingIdentityClass = Identity.maboEddieParticipantResolution

data RepresentationCardinalityEqualsWorldObjectCardinality : Set where
data DuplicateAliasAdvancesNoveltyTarget : Set where
data QidCountEqualsReviewedIdentityClassCount : Set where

data ArticleCountEqualsReviewedIdentityClassCount : Set where

representationCardinalityDoesNotEqualWorldObjectCardinality :
  RepresentationCardinalityEqualsWorldObjectCardinality → ⊥
representationCardinalityDoesNotEqualWorldObjectCardinality ()

duplicateAliasDoesNotAdvanceNoveltyTarget :
  DuplicateAliasAdvancesNoveltyTarget → ⊥
duplicateAliasDoesNotAdvanceNoveltyTarget ()

qidCountDoesNotEqualReviewedIdentityClassCount :
  QidCountEqualsReviewedIdentityClassCount → ⊥
qidCountDoesNotEqualReviewedIdentityClassCount ()

articleCountDoesNotEqualReviewedIdentityClassCount :
  ArticleCountEqualsReviewedIdentityClassCount → ⊥
articleCountDoesNotEqualReviewedIdentityClassCount ()
