module DASHI.Physics.Closure.LilaE8RootEnumeration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.LilaE8RootSystemLatticeReceipt as R1
import DASHI.Physics.Closure.LilaE8RootSystemLocalSourceDiagnostic as Source

------------------------------------------------------------------------
-- LILA-R2: conservative E8 root-enumeration request surface.
--
-- This module deliberately does not enumerate E8 roots.  It records the
-- constructive obligations for a future provider using doubled coordinates:
--
--   integer roots      : permutations of (±2, ±2, 0, ..., 0), expected 112
--   half-integer roots : all coordinates ±1 with even sign parity, expected 128
--
-- Supplying these requests is not enough for promotion; a future provider must
-- also prove uniqueness, membership, cardinality, norm/inner-product laws, and
-- projection compatibility in DASHI algebra.

data LilaE8RootEnumerationStatus : Set where
  enumerationRequestedButNotConstructed :
    LilaE8RootEnumerationStatus

data E8DoubledCoordinateFamily : Set where
  doubledIntegerRootFamily :
    E8DoubledCoordinateFamily
  doubledHalfIntegerRootFamily :
    E8DoubledCoordinateFamily

canonicalE8DoubledCoordinateFamilies :
  List E8DoubledCoordinateFamily
canonicalE8DoubledCoordinateFamilies =
  doubledIntegerRootFamily
  ∷ doubledHalfIntegerRootFamily
  ∷ []

data E8RootFamilyRequirement : Set where
  integerRootsUseEightDoubledCoordinates :
    E8RootFamilyRequirement
  integerRootsHaveExactlyTwoNonzeroCoordinates :
    E8RootFamilyRequirement
  integerRootNonzeroCoordinatesArePlusOrMinusTwo :
    E8RootFamilyRequirement
  integerRootsRangeOverAllCoordinatePairsAndSigns :
    E8RootFamilyRequirement
  halfIntegerRootsUseEightDoubledCoordinates :
    E8RootFamilyRequirement
  halfIntegerRootsHaveEveryCoordinatePlusOrMinusOne :
    E8RootFamilyRequirement
  halfIntegerRootsHaveEvenMinusSignParity :
    E8RootFamilyRequirement
  familiesAreDisjointInDoubledCoordinates :
    E8RootFamilyRequirement

canonicalE8RootFamilyRequirements :
  List E8RootFamilyRequirement
canonicalE8RootFamilyRequirements =
  integerRootsUseEightDoubledCoordinates
  ∷ integerRootsHaveExactlyTwoNonzeroCoordinates
  ∷ integerRootNonzeroCoordinatesArePlusOrMinusTwo
  ∷ integerRootsRangeOverAllCoordinatePairsAndSigns
  ∷ halfIntegerRootsUseEightDoubledCoordinates
  ∷ halfIntegerRootsHaveEveryCoordinatePlusOrMinusOne
  ∷ halfIntegerRootsHaveEvenMinusSignParity
  ∷ familiesAreDisjointInDoubledCoordinates
  ∷ []

data E8RootCardinalityObligation : Set where
  integerRootFamilyHas112Elements :
    E8RootCardinalityObligation
  halfIntegerRootFamilyHas128Elements :
    E8RootCardinalityObligation
  combinedRootFamilyHas240Elements :
    E8RootCardinalityObligation
  noDuplicateRootsAcrossOrWithinFamilies :
    E8RootCardinalityObligation
  decidableRootEqualityRequired :
    E8RootCardinalityObligation

canonicalE8RootCardinalityObligations :
  List E8RootCardinalityObligation
canonicalE8RootCardinalityObligations =
  integerRootFamilyHas112Elements
  ∷ halfIntegerRootFamilyHas128Elements
  ∷ combinedRootFamilyHas240Elements
  ∷ noDuplicateRootsAcrossOrWithinFamilies
  ∷ decidableRootEqualityRequired
  ∷ []

expectedIntegerRootCount : Nat
expectedIntegerRootCount = 112

expectedHalfIntegerRootCount : Nat
expectedHalfIntegerRootCount = 128

expectedTotalE8RootCount : Nat
expectedTotalE8RootCount = 240

record E8RootEnumerationCountRequest : Set where
  field
    expectedIntegerRoots :
      Nat

    expectedIntegerRootsIs112 :
      expectedIntegerRoots ≡ expectedIntegerRootCount

    expectedHalfIntegerRoots :
      Nat

    expectedHalfIntegerRootsIs128 :
      expectedHalfIntegerRoots ≡ expectedHalfIntegerRootCount

    expectedTotalRoots :
      Nat

    expectedTotalRootsIs240 :
      expectedTotalRoots ≡ expectedTotalE8RootCount

canonicalE8RootEnumerationCountRequest :
  E8RootEnumerationCountRequest
canonicalE8RootEnumerationCountRequest =
  record
    { expectedIntegerRoots =
        expectedIntegerRootCount
    ; expectedIntegerRootsIs112 =
        refl
    ; expectedHalfIntegerRoots =
        expectedHalfIntegerRootCount
    ; expectedHalfIntegerRootsIs128 =
        refl
    ; expectedTotalRoots =
        expectedTotalE8RootCount
    ; expectedTotalRootsIs240 =
        refl
    }

data E8MissingFormalProofField : Set where
  missingEightDimensionalDoubledCoordinateCarrier :
    E8MissingFormalProofField
  missingIntegerRootEnumerator :
    E8MissingFormalProofField
  missingHalfIntegerRootEnumerator :
    E8MissingFormalProofField
  missingIntegerMembershipDecision :
    E8MissingFormalProofField
  missingHalfIntegerMembershipDecision :
    E8MissingFormalProofField
  missingDuplicateFreedomProof :
    E8MissingFormalProofField
  missingIntegerCardinalityProof112 :
    E8MissingFormalProofField
  missingHalfIntegerCardinalityProof128 :
    E8MissingFormalProofField
  missingTotalCardinalityProof240 :
    E8MissingFormalProofField
  missingSquaredNormFourInDoubledCoordinatesProof :
    E8MissingFormalProofField
  missingE8InnerProductClosureProof :
    E8MissingFormalProofField
  missingWeylActionClosureProof :
    E8MissingFormalProofField
  missingDashiAlgebraCarrierEmbedding :
    E8MissingFormalProofField
  missingLilaProjectionCompatibilityProof :
    E8MissingFormalProofField
  missingLamTungPhiStarAdapterProof :
    E8MissingFormalProofField
  missingAcceptedExecutionAndAuthorityReceipts :
    E8MissingFormalProofField

canonicalE8MissingFormalProofFields :
  List E8MissingFormalProofField
canonicalE8MissingFormalProofFields =
  missingEightDimensionalDoubledCoordinateCarrier
  ∷ missingIntegerRootEnumerator
  ∷ missingHalfIntegerRootEnumerator
  ∷ missingIntegerMembershipDecision
  ∷ missingHalfIntegerMembershipDecision
  ∷ missingDuplicateFreedomProof
  ∷ missingIntegerCardinalityProof112
  ∷ missingHalfIntegerCardinalityProof128
  ∷ missingTotalCardinalityProof240
  ∷ missingSquaredNormFourInDoubledCoordinatesProof
  ∷ missingE8InnerProductClosureProof
  ∷ missingWeylActionClosureProof
  ∷ missingDashiAlgebraCarrierEmbedding
  ∷ missingLilaProjectionCompatibilityProof
  ∷ missingLamTungPhiStarAdapterProof
  ∷ missingAcceptedExecutionAndAuthorityReceipts
  ∷ []

data E8EnumerationNonPromotionBoundary : Set where
  noRootListConstructedHere :
    E8EnumerationNonPromotionBoundary
  noMembershipDecisionConstructedHere :
    E8EnumerationNonPromotionBoundary
  noCardinalityProofConstructedHere :
    E8EnumerationNonPromotionBoundary
  noInnerProductOrWeylProofConstructedHere :
    E8EnumerationNonPromotionBoundary
  noDashiProjectionProofConstructedHere :
    E8EnumerationNonPromotionBoundary
  noLamTungOrPhiStarPromotionHere :
    E8EnumerationNonPromotionBoundary

canonicalE8EnumerationNonPromotionBoundaries :
  List E8EnumerationNonPromotionBoundary
canonicalE8EnumerationNonPromotionBoundaries =
  noRootListConstructedHere
  ∷ noMembershipDecisionConstructedHere
  ∷ noCardinalityProofConstructedHere
  ∷ noInnerProductOrWeylProofConstructedHere
  ∷ noDashiProjectionProofConstructedHere
  ∷ noLamTungOrPhiStarPromotionHere
  ∷ []

data E8RootEnumerationConstructiveReceipt : Set where

e8RootEnumerationConstructiveReceiptImpossibleHere :
  E8RootEnumerationConstructiveReceipt →
  ⊥
e8RootEnumerationConstructiveReceiptImpossibleHere ()

record LilaE8RootEnumerationRequest : Setω where
  field
    status :
      LilaE8RootEnumerationStatus

    priorDiagnostic :
      Source.LilaE8RootSystemLocalSourceDiagnostic

    priorDiagnosticIsNonPromoting :
      Source.LilaE8RootSystemLocalSourceDiagnostic.e8PhysicsTheoremCompletedHere
        priorDiagnostic
      ≡
      false

    priorLatticeReceipt :
      R1.LilaE8RootSystemLatticeReceipt

    priorLatticeReceiptIsNonPromoting :
      R1.LilaE8RootSystemLatticeReceipt.e8PhysicsTheoremCompletedHere
        priorLatticeReceipt
      ≡
      false

    doubledCoordinateFamilies :
      List E8DoubledCoordinateFamily

    doubledCoordinateFamiliesAreCanonical :
      doubledCoordinateFamilies ≡ canonicalE8DoubledCoordinateFamilies

    familyRequirements :
      List E8RootFamilyRequirement

    familyRequirementsAreCanonical :
      familyRequirements ≡ canonicalE8RootFamilyRequirements

    countRequest :
      E8RootEnumerationCountRequest

    cardinalityObligations :
      List E8RootCardinalityObligation

    cardinalityObligationsAreCanonical :
      cardinalityObligations ≡ canonicalE8RootCardinalityObligations

    missingFormalProofFields :
      List E8MissingFormalProofField

    missingFormalProofFieldsAreCanonical :
      missingFormalProofFields ≡ canonicalE8MissingFormalProofFields

    requestNotes :
      List String

    theoremCompletedHere :
      Bool

    theoremCompletedHereIsFalse :
      theoremCompletedHere ≡ false

    nonPromotionBoundary :
      List E8EnumerationNonPromotionBoundary

    nonPromotionBoundaryIsCanonical :
      nonPromotionBoundary ≡ canonicalE8EnumerationNonPromotionBoundaries

    constructiveReceiptBlocked :
      E8RootEnumerationConstructiveReceipt →
      ⊥

canonicalLilaE8RootEnumerationRequest :
  LilaE8RootEnumerationRequest
canonicalLilaE8RootEnumerationRequest =
  record
    { status =
        enumerationRequestedButNotConstructed
    ; priorDiagnostic =
        Source.canonicalLilaE8RootSystemLocalSourceDiagnostic
    ; priorDiagnosticIsNonPromoting =
        refl
    ; priorLatticeReceipt =
        R1.canonicalLilaE8RootSystemLatticeReceipt
    ; priorLatticeReceiptIsNonPromoting =
        refl
    ; doubledCoordinateFamilies =
        canonicalE8DoubledCoordinateFamilies
    ; doubledCoordinateFamiliesAreCanonical =
        refl
    ; familyRequirements =
        canonicalE8RootFamilyRequirements
    ; familyRequirementsAreCanonical =
        refl
    ; countRequest =
        canonicalE8RootEnumerationCountRequest
    ; cardinalityObligations =
        canonicalE8RootCardinalityObligations
    ; cardinalityObligationsAreCanonical =
        refl
    ; missingFormalProofFields =
        canonicalE8MissingFormalProofFields
    ; missingFormalProofFieldsAreCanonical =
        refl
    ; requestNotes =
        "LILA-R2 refines LILA-R1 by naming the constructive E8 root-enumeration receipt shape"
        ∷ "Use doubled coordinates so integer roots are +/-2 entries and half-integer roots are +/-1 entries"
        ∷ "The expected counts 112, 128, and 240 are obligations, not locally validated cardinality theorems"
        ∷ "A provider must return a real constructive receipt or the first missing typed proof field"
        ∷ []
    ; theoremCompletedHere =
        false
    ; theoremCompletedHereIsFalse =
        refl
    ; nonPromotionBoundary =
        canonicalE8EnumerationNonPromotionBoundaries
    ; nonPromotionBoundaryIsCanonical =
        refl
    ; constructiveReceiptBlocked =
        e8RootEnumerationConstructiveReceiptImpossibleHere
    }

canonicalLilaE8RootEnumerationStatus :
  LilaE8RootEnumerationStatus
canonicalLilaE8RootEnumerationStatus =
  enumerationRequestedButNotConstructed
