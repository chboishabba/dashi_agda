module DASHI.Physics.Closure.LilaE8RootEnumerationReceiptR2 where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.LilaE8RootEnumeration as R2

------------------------------------------------------------------------
-- LILA-R2: scoped E8 root-count receipt.
--
-- This module records bounded count evidence only:
--
--   integer doubled-coordinate root class : 112
--   half doubled-coordinate root class    : 128
--   total expected E8 root count          : 240
--
-- It deliberately does not construct a root carrier, a decidable
-- enumeration, or any promoted E8 theorem.  Diagrams should add this as a
-- LILA-R2 count-support node, not as a W3/W4/W5/W8 unblocker.

data LilaR2CountReceiptStatus : Set where
  countSupportOnly :
    LilaR2CountReceiptStatus

data LilaR2RootCountClass : Set where
  integerDoubledCoordinateRootClass :
    LilaR2RootCountClass
  halfDoubledCoordinateRootClass :
    LilaR2RootCountClass
  totalDoubledCoordinateRootClass :
    LilaR2RootCountClass

integerRootClassCount : Nat
integerRootClassCount = 112

halfRootClassCount : Nat
halfRootClassCount = 128

totalRootClassCount : Nat
totalRootClassCount = 240

record LilaR2RootCountEvidence : Set where
  field
    integerClass :
      Nat

    integerClassIs112 :
      integerClass ≡ integerRootClassCount

    halfClass :
      Nat

    halfClassIs128 :
      halfClass ≡ halfRootClassCount

    totalClass :
      Nat

    totalClassIs240 :
      totalClass ≡ totalRootClassCount

canonicalLilaR2RootCountEvidence :
  LilaR2RootCountEvidence
canonicalLilaR2RootCountEvidence =
  record
    { integerClass =
        integerRootClassCount
    ; integerClassIs112 =
        refl
    ; halfClass =
        halfRootClassCount
    ; halfClassIs128 =
        refl
    ; totalClass =
        totalRootClassCount
    ; totalClassIs240 =
        refl
    }

data LilaR2MissingPromotionField : Set where
  missingDuplicateFreedom :
    LilaR2MissingPromotionField
  missingCompleteness :
    LilaR2MissingPromotionField
  missingSquaredNormLaw :
    LilaR2MissingPromotionField
  missingInnerProductLaw :
    LilaR2MissingPromotionField
  missingWeylClosure :
    LilaR2MissingPromotionField
  missingDashiProjectionCompatibility :
    LilaR2MissingPromotionField
  missingLilaProjectionCompatibility :
    LilaR2MissingPromotionField

canonicalLilaR2MissingPromotionFields :
  List LilaR2MissingPromotionField
canonicalLilaR2MissingPromotionFields =
  missingDuplicateFreedom
  ∷ missingCompleteness
  ∷ missingSquaredNormLaw
  ∷ missingInnerProductLaw
  ∷ missingWeylClosure
  ∷ missingDashiProjectionCompatibility
  ∷ missingLilaProjectionCompatibility
  ∷ []

data LilaR2NonPromotionBoundary : Set where
  noRootCarrierConstructedHere :
    LilaR2NonPromotionBoundary
  noDecidableEnumerationConstructedHere :
    LilaR2NonPromotionBoundary
  noDuplicateFreedomProofConstructedHere :
    LilaR2NonPromotionBoundary
  noCompletenessProofConstructedHere :
    LilaR2NonPromotionBoundary
  noNormOrInnerProductProofConstructedHere :
    LilaR2NonPromotionBoundary
  noWeylClosureProofConstructedHere :
    LilaR2NonPromotionBoundary
  noProjectionCompatibilityProofConstructedHere :
    LilaR2NonPromotionBoundary
  noW3W4W5W8UnblockerConstructedHere :
    LilaR2NonPromotionBoundary

canonicalLilaR2NonPromotionBoundaries :
  List LilaR2NonPromotionBoundary
canonicalLilaR2NonPromotionBoundaries =
  noRootCarrierConstructedHere
  ∷ noDecidableEnumerationConstructedHere
  ∷ noDuplicateFreedomProofConstructedHere
  ∷ noCompletenessProofConstructedHere
  ∷ noNormOrInnerProductProofConstructedHere
  ∷ noWeylClosureProofConstructedHere
  ∷ noProjectionCompatibilityProofConstructedHere
  ∷ noW3W4W5W8UnblockerConstructedHere
  ∷ []

data LilaR2PromotedE8CarrierTheorem : Set where

lilaR2PromotedE8CarrierTheoremImpossibleHere :
  LilaR2PromotedE8CarrierTheorem →
  ⊥
lilaR2PromotedE8CarrierTheoremImpossibleHere ()

record LilaE8RootEnumerationReceiptR2 : Setω where
  field
    status :
      LilaR2CountReceiptStatus

    priorRequest :
      R2.LilaE8RootEnumerationRequest

    priorRequestStillNonPromoting :
      R2.LilaE8RootEnumerationRequest.theoremCompletedHere priorRequest
      ≡
      false

    countEvidence :
      LilaR2RootCountEvidence

    countEvidenceIsCanonical :
      countEvidence ≡ canonicalLilaR2RootCountEvidence

    missingPromotionFields :
      List LilaR2MissingPromotionField

    missingPromotionFieldsAreCanonical :
      missingPromotionFields ≡ canonicalLilaR2MissingPromotionFields

    nonPromotionBoundary :
      List LilaR2NonPromotionBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ canonicalLilaR2NonPromotionBoundaries

    diagramIntegrationNotes :
      List String

    theoremCompletedHere :
      Bool

    theoremCompletedHereIsFalse :
      theoremCompletedHere ≡ false

    promotedCarrierTheoremBlocked :
      LilaR2PromotedE8CarrierTheorem →
      ⊥

canonicalLilaE8RootEnumerationReceiptR2 :
  LilaE8RootEnumerationReceiptR2
canonicalLilaE8RootEnumerationReceiptR2 =
  record
    { status =
        countSupportOnly
    ; priorRequest =
        R2.canonicalLilaE8RootEnumerationRequest
    ; priorRequestStillNonPromoting =
        refl
    ; countEvidence =
        canonicalLilaR2RootCountEvidence
    ; countEvidenceIsCanonical =
        refl
    ; missingPromotionFields =
        canonicalLilaR2MissingPromotionFields
    ; missingPromotionFieldsAreCanonical =
        refl
    ; nonPromotionBoundary =
        canonicalLilaR2NonPromotionBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; diagramIntegrationNotes =
        "Add a LILA-R2 count-support node for 112 + 128 = 240 when diagrams are next edited"
        ∷ "Do not connect this receipt as a W3/W4/W5/W8 promotion unblocker"
        ∷ "Promotion still requires duplicate freedom, completeness, norm/inner-product laws, Weyl closure, and DASHI/LILA projection compatibility"
        ∷ []
    ; theoremCompletedHere =
        false
    ; theoremCompletedHereIsFalse =
        refl
    ; promotedCarrierTheoremBlocked =
        lilaR2PromotedE8CarrierTheoremImpossibleHere
    }
