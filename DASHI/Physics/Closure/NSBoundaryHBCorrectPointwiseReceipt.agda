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
--   It follows from pointwise kornBiaxialBound under biaxial boundary,
--   a lambda3 gap, and a pointwise ||nabla^2 u|| >= eta hypothesis.
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
  "BoundaryHB pointwise lower bound is not recovered from integral Korn plus continuity alone; the corrected route uses pointwise kornBiaxialBound under biaxial boundary, a lambda3 gap, and a pointwise ||nabla^2 u|| >= eta hypothesis. Layer-integral Korn alone remains insufficient for an all-point lower bound."

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
    ; boundaryHBPointwiseDependencyStatement =
        nsBoundaryHBPointwiseDependencyStatement
    ; boundaryHBPointwiseDependencyStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Corrected BoundaryHB dependency: pointwise lower bound follows from pointwise kornBiaxialBound, not from integral Korn plus continuity alone."
        ∷ "Explicit blocker: layer-integral Korn control is insufficient for an all-point lower bound."
        ∷ "The corrected route requires biaxial boundary, lambda3 gap, and pointwise ||nabla^2 u|| >= eta."
        ∷ "Candidate-only receipt surface; Clay Navier-Stokes remains false."
        ∷ []
    }

nsBoundaryHBCorrectPointwiseReceiptKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSBoundaryHBCorrectPointwiseReceipt ≡ false
nsBoundaryHBCorrectPointwiseReceiptKeepsClayFalse =
  refl
