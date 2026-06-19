module DASHI.Physics.Closure.NSBoundaryHBCorrectPointwiseReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only BoundaryHB receipt for the corrected pointwise route.
--
-- The corrected dependency is:
--   BoundaryHB pointwise lower bound does not follow from integral Korn
--   plus continuity alone.
--   It follows from the pointwise route lambda2 = 0, lambda1 = -lambda3,
--   lambda3 >= lambda_min, and pointwise ||nabla^2 u|| >= eta, which
--   projects to max_k B_k >= b0 through pointwise kornBiaxialBound.
--
-- The explicit blocker is that layer-integral Korn control alone is not
-- enough to force an all-point lower bound.

data Void : Set where

data NSBoundaryHBCorrectPointwiseStatus : Set where
  candidateOnlyCorrectedPointwiseDependencyRecorded :
    NSBoundaryHBCorrectPointwiseStatus

data NSBoundaryHCBoundaryBlocker : Set where
  layerIntegralKornInsufficientForAllPointLowerBound :
    NSBoundaryHCBoundaryBlocker

  continuityDoesNotUpgradeIntegralToPointwise :
    NSBoundaryHCBoundaryBlocker

  missingPointwiseKornBiaxialBound :
    NSBoundaryHCBoundaryBlocker

  missingBiaxialBoundaryHypothesis :
    NSBoundaryHCBoundaryBlocker

  missingLambda3GapHypothesis :
    NSBoundaryHCBoundaryBlocker

  missingPointwiseNabla2ULowerBoundEta :
    NSBoundaryHCBoundaryBlocker

data NSBoundaryHCPointwiseRouteProjection : Set where
  lambda2EqualsZeroProjected :
    NSBoundaryHCPointwiseRouteProjection

  lambda1EqualsNegativeLambda3Projected :
    NSBoundaryHCPointwiseRouteProjection

  lambda3AtLeastLambdaMinProjected :
    NSBoundaryHCPointwiseRouteProjection

  pointwiseNabla2ULowerBoundEtaProjected :
    NSBoundaryHCPointwiseRouteProjection

  pointwiseMaxBKAtLeastB0Projected :
    NSBoundaryHCPointwiseRouteProjection

canonicalNSBoundaryHCPointwiseRouteProjection :
  List NSBoundaryHCPointwiseRouteProjection
canonicalNSBoundaryHCPointwiseRouteProjection =
  lambda2EqualsZeroProjected
  ∷ lambda1EqualsNegativeLambda3Projected
  ∷ lambda3AtLeastLambdaMinProjected
  ∷ pointwiseNabla2ULowerBoundEtaProjected
  ∷ pointwiseMaxBKAtLeastB0Projected
  ∷ []

nsBoundaryHCPointwiseRouteProjectionStatement : String
nsBoundaryHCPointwiseRouteProjectionStatement =
  "Pointwise closeability route recorded: lambda2 = 0, lambda1 = -lambda3, lambda3 >= lambda_min, and ||nabla^2 u|| >= eta project to max_k B_k >= b0."

canonicalNSBoundaryHCBoundaryBlockers :
  List NSBoundaryHCBoundaryBlocker
canonicalNSBoundaryHCBoundaryBlockers =
  layerIntegralKornInsufficientForAllPointLowerBound
  ∷ continuityDoesNotUpgradeIntegralToPointwise
  ∷ missingPointwiseKornBiaxialBound
  ∷ missingBiaxialBoundaryHypothesis
  ∷ missingLambda3GapHypothesis
  ∷ missingPointwiseNabla2ULowerBoundEta
  ∷ []

nsBoundaryHBPointwiseDependencyStatement : String
nsBoundaryHBPointwiseDependencyStatement =
  "BoundaryHB pointwise lower bound is not recovered from integral Korn plus continuity alone; the corrected route uses lambda2 = 0, lambda1 = -lambda3, lambda3 >= lambda_min, and pointwise ||nabla^2 u|| >= eta, which projects to max_k B_k >= b0 through pointwise kornBiaxialBound. Layer-integral Korn alone remains insufficient for an all-point lower bound."

record NSBoundaryHBCorrectPointwiseReceipt : Setω where
  field
    status :
      NSBoundaryHBCorrectPointwiseStatus

    statusIsCanonical :
      status ≡ candidateOnlyCorrectedPointwiseDependencyRecorded

    blockers :
      List NSBoundaryHCBoundaryBlocker

    blockersAreCanonical :
      blockers ≡ canonicalNSBoundaryHCBoundaryBlockers

    pointwiseDependencyRecorded :
      Bool

    pointwiseDependencyRecordedIsTrue :
      pointwiseDependencyRecorded ≡ true

    pointwiseDependencyPromoted :
      Bool

    pointwiseDependencyPromotedIsFalse :
      pointwiseDependencyPromoted ≡ false

    pointwiseRouteProjection :
      List NSBoundaryHCPointwiseRouteProjection

    pointwiseRouteProjectionIsCanonical :
      pointwiseRouteProjection ≡ canonicalNSBoundaryHCPointwiseRouteProjection

    pointwiseRouteProjectionStatement :
      String

    pointwiseRouteProjectionStatementIsCanonical :
      pointwiseRouteProjectionStatement
      ≡ nsBoundaryHCPointwiseRouteProjectionStatement

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    pointwiseKornBiaxialBound :
      Bool

    pointwiseKornBiaxialBoundIsTrue :
      pointwiseKornBiaxialBound ≡ true

    lambda2ZeroRequired :
      Bool

    lambda2ZeroRequiredIsTrue :
      lambda2ZeroRequired ≡ true

    lambda1EqualsNegativeLambda3Required :
      Bool

    lambda1EqualsNegativeLambda3RequiredIsTrue :
      lambda1EqualsNegativeLambda3Required ≡ true

    lambda3AtLeastLambdaMinRequired :
      Bool

    lambda3AtLeastLambdaMinRequiredIsTrue :
      lambda3AtLeastLambdaMinRequired ≡ true

    biaxialBoundary :
      Bool

    biaxialBoundaryIsTrue :
      biaxialBoundary ≡ true

    lambda3Gap :
      Bool

    lambda3GapIsTrue :
      lambda3Gap ≡ true

    nabla2ULowerBoundEta :
      Bool

    nabla2ULowerBoundEtaIsTrue :
      nabla2ULowerBoundEta ≡ true

    pointwiseMaxBKAtLeastB0Closed :
      Bool

    pointwiseMaxBKAtLeastB0ClosedIsTrue :
      pointwiseMaxBKAtLeastB0Closed ≡ true

    boundaryHBPointwiseDependencyStatement :
      String

    boundaryHBPointwiseDependencyStatementIsCanonical :
      boundaryHBPointwiseDependencyStatement
      ≡ nsBoundaryHBPointwiseDependencyStatement

    receiptBoundary :
      List String

open NSBoundaryHBCorrectPointwiseReceipt public

canonicalNSBoundaryHBCorrectPointwiseReceipt :
  NSBoundaryHBCorrectPointwiseReceipt
canonicalNSBoundaryHBCorrectPointwiseReceipt =
  record
    { status =
        candidateOnlyCorrectedPointwiseDependencyRecorded
    ; statusIsCanonical =
        refl
    ; blockers =
        canonicalNSBoundaryHCBoundaryBlockers
    ; blockersAreCanonical =
        refl
    ; pointwiseDependencyRecorded =
        true
    ; pointwiseDependencyRecordedIsTrue =
        refl
    ; pointwiseDependencyPromoted =
        false
    ; pointwiseDependencyPromotedIsFalse =
        refl
    ; pointwiseRouteProjection =
        canonicalNSBoundaryHCPointwiseRouteProjection
    ; pointwiseRouteProjectionIsCanonical =
        refl
    ; pointwiseRouteProjectionStatement =
        nsBoundaryHCPointwiseRouteProjectionStatement
    ; pointwiseRouteProjectionStatementIsCanonical =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; pointwiseKornBiaxialBound =
        true
    ; pointwiseKornBiaxialBoundIsTrue =
        refl
    ; lambda2ZeroRequired =
        true
    ; lambda2ZeroRequiredIsTrue =
        refl
    ; lambda1EqualsNegativeLambda3Required =
        true
    ; lambda1EqualsNegativeLambda3RequiredIsTrue =
        refl
    ; lambda3AtLeastLambdaMinRequired =
        true
    ; lambda3AtLeastLambdaMinRequiredIsTrue =
        refl
    ; biaxialBoundary =
        true
    ; biaxialBoundaryIsTrue =
        refl
    ; lambda3Gap =
        true
    ; lambda3GapIsTrue =
        refl
    ; nabla2ULowerBoundEta =
        true
    ; nabla2ULowerBoundEtaIsTrue =
        refl
    ; pointwiseMaxBKAtLeastB0Closed =
        true
    ; pointwiseMaxBKAtLeastB0ClosedIsTrue =
        refl
    ; boundaryHBPointwiseDependencyStatement =
        nsBoundaryHBPointwiseDependencyStatement
    ; boundaryHBPointwiseDependencyStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Corrected BoundaryHB dependency: pointwise lower bound follows from pointwise kornBiaxialBound, not from integral Korn plus continuity alone."
        ∷ "Explicit blocker: layer-integral Korn control is insufficient for an all-point lower bound."
        ∷ "The corrected route requires lambda2 = 0, lambda1 = -lambda3, lambda3 >= lambda_min, and pointwise ||nabla^2 u|| >= eta."
        ∷ "The pointwise consequence is max_k B_k >= b0."
        ∷ "Candidate-only receipt surface; Clay Navier-Stokes remains false."
        ∷ []
    }

nsBoundaryHBCorrectPointwiseReceiptKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSBoundaryHBCorrectPointwiseReceipt ≡ false
nsBoundaryHBCorrectPointwiseReceiptKeepsClayFalse =
  refl
