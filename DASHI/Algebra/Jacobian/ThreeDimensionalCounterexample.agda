module DASHI.Algebra.Jacobian.ThreeDimensionalCounterexample where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Jacobian.CollisionImpliesNonInjective as Collision

------------------------------------------------------------------------
-- Mathematical consequence and publication/provenance status are separated.
-- The sparse-polynomial determinant and rational evaluations are supplied by
-- an exact executable certificate.  Agda proves the collision implication.

record ExactPolynomialCertificate : Set where
  constructor exactPolynomialCertificate
  field
    ambientDimension : Nat
    formulaVersion : String
    determinantConstant : String
    determinantExpansionCheckedExactly : Bool
    distinctCollisionCheckedExactly : Bool
    witnessCount : Nat
    commonImage : String
    executableChecker : String
    checkerDigest : String

open ExactPolynomialCertificate public

record KernelPromotionStatus : Set where
  constructor kernelPromotionStatus
  field
    sparsePolynomialExpansionKernelChecked : Bool
    exactEvaluationKernelChecked : Bool
    collisionImpliesNoninjectiveKernelProved : Bool
    counterexampleImplicationKernelProved : Bool

open KernelPromotionStatus public

record PublicationStatus : Set where
  constructor publicationStatus
  field
    announcementSource : String
    attribution : String
    stableArchivalCitationPresent : Bool
    peerReviewedPublicationPresent : Bool
    historicalAttributionFinalised : Bool
    laterCorrectionReceipt : String

open PublicationStatus public

record JacobianCounterexampleReceipt : Set₁ where
  constructor jacobianCounterexampleReceipt
  field
    certificate : ExactPolynomialCertificate
    kernelStatus : KernelPromotionStatus
    publication : PublicationStatus
    nonzeroConstantJacobian : Bool
    noninjective : Bool
    counterexampleInDimensionThree : Bool
    dimensionTwoResolved : Bool

open JacobianCounterexampleReceipt public

canonicalExactCertificate : ExactPolynomialCertificate
canonicalExactCertificate =
  exactPolynomialCertificate
    3
    "three-coordinate formula checked by sparse exact arithmetic"
    "-2"
    true
    true
    3
    "(-1/4,0,0)"
    "scripts/check_jacobian_noninjective_example.py"
    "digest pending repository release receipt"

canonicalKernelStatus : KernelPromotionStatus
canonicalKernelStatus =
  kernelPromotionStatus
    false
    false
    true
    true

canonicalPublicationStatus : PublicationStatus
canonicalPublicationStatus =
  publicationStatus
    "recent public announcement; exact archival source must be maintained separately"
    "candidate attribution recorded outside the mathematical kernel"
    false
    false
    false
    "no correction recorded in this receipt"

canonicalCounterexampleReceipt : JacobianCounterexampleReceipt
canonicalCounterexampleReceipt =
  jacobianCounterexampleReceipt
    canonicalExactCertificate
    canonicalKernelStatus
    canonicalPublicationStatus
    true
    true
    true
    false

canonicalDimensionTwoRemainsOpen :
  dimensionTwoResolved canonicalCounterexampleReceipt ≡ false
canonicalDimensionTwoRemainsOpen = refl
