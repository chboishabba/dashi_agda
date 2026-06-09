module DASHI.Physics.Closure.RGOperatorNormReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.RGContractionReceipt as RGContraction

------------------------------------------------------------------------
-- RG operator norm frontier.
--
-- This receipt isolates the precise metric computation needed for the
-- Yang-Mills RG route: prove ||T_d^RG||_op = alpha1 from the carrier metric
-- eigensystem.  The finite alpha1<1 diagnostic is recorded; the equality and
-- the Clay promotion remain false.

data RGOperatorNormInput : Set where
  factorVecMetricEigensystem :
    RGOperatorNormInput

  primeLaneAdjacentNormRatio :
    RGOperatorNormInput

  selfAdjointCarrierHamiltonianNorm :
    RGOperatorNormInput

canonicalRGOperatorNormInputs :
  List RGOperatorNormInput
canonicalRGOperatorNormInputs =
  factorVecMetricEigensystem
  ∷ primeLaneAdjacentNormRatio
  ∷ selfAdjointCarrierHamiltonianNorm
  ∷ []

data RGOperatorNormTarget : Set where
  operatorNormEqualsAlphaOne :
    RGOperatorNormTarget

data RGOperatorNormBlocker : Set where
  missingMetricEigensystemComputation :
    RGOperatorNormBlocker

  missingOperatorNormEqualityProof :
    RGOperatorNormBlocker

canonicalRGOperatorNormBlockers :
  List RGOperatorNormBlocker
canonicalRGOperatorNormBlockers =
  missingMetricEigensystemComputation
  ∷ missingOperatorNormEqualityProof
  ∷ []

operatorNormTargetStatement : String
operatorNormTargetStatement =
  "Target: ||T_d^RG||_op = alpha1, where alpha1 is the carrier p2-to-p3 depth-separation norm ratio read from the FactorVec metric eigensystem."

record RGOperatorNormReceipt : Setω where
  field
    rgContractionReceipt :
      RGContraction.RGContractionReceipt

    operatorNormEqualityAlreadyTargeted :
      RGContraction.operatorNormEqualityTargetRecorded rgContractionReceipt
      ≡
      true

    rgMapContractionStillOpen :
      RGContraction.rgMapContractsProved rgContractionReceipt
      ≡
      false

    inputs :
      List RGOperatorNormInput

    inputsAreCanonical :
      inputs ≡ canonicalRGOperatorNormInputs

    target :
      RGOperatorNormTarget

    targetIsCanonical :
      target ≡ operatorNormEqualsAlphaOne

    alphaOnePartsPerMillion :
      Nat

    alphaOnePartsPerMillionIsDiagnostic :
      alphaOnePartsPerMillion ≡ 41240

    alphaOneLessThanOneRecorded :
      Bool

    alphaOneLessThanOneRecordedIsTrue :
      alphaOneLessThanOneRecorded ≡ true

    metricEigensystemComputedHere :
      Bool

    metricEigensystemComputedHereIsFalse :
      metricEigensystemComputedHere ≡ false

    operatorNormEqualityProved :
      Bool

    operatorNormEqualityProvedIsFalse :
      operatorNormEqualityProved ≡ false

    rgContractionPromoted :
      Bool

    rgContractionPromotedIsFalse :
      rgContractionPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    blockers :
      List RGOperatorNormBlocker

    blockersAreCanonical :
      blockers ≡ canonicalRGOperatorNormBlockers

    targetStatement :
      String

    targetStatementIsCanonical :
      targetStatement ≡ operatorNormTargetStatement

    receiptBoundary :
      List String

open RGOperatorNormReceipt public

canonicalRGOperatorNormReceipt :
  RGOperatorNormReceipt
canonicalRGOperatorNormReceipt =
  record
    { rgContractionReceipt =
        RGContraction.canonicalRGContractionReceipt
    ; operatorNormEqualityAlreadyTargeted =
        refl
    ; rgMapContractionStillOpen =
        refl
    ; inputs =
        canonicalRGOperatorNormInputs
    ; inputsAreCanonical =
        refl
    ; target =
        operatorNormEqualsAlphaOne
    ; targetIsCanonical =
        refl
    ; alphaOnePartsPerMillion =
        41240
    ; alphaOnePartsPerMillionIsDiagnostic =
        refl
    ; alphaOneLessThanOneRecorded =
        true
    ; alphaOneLessThanOneRecordedIsTrue =
        refl
    ; metricEigensystemComputedHere =
        false
    ; metricEigensystemComputedHereIsFalse =
        refl
    ; operatorNormEqualityProved =
        false
    ; operatorNormEqualityProvedIsFalse =
        refl
    ; rgContractionPromoted =
        false
    ; rgContractionPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; blockers =
        canonicalRGOperatorNormBlockers
    ; blockersAreCanonical =
        refl
    ; targetStatement =
        operatorNormTargetStatement
    ; targetStatementIsCanonical =
        refl
    ; receiptBoundary =
        "The alpha1<1 diagnostic is recorded at 41240 ppm"
        ∷ "The missing proof is the metric eigensystem computation giving ||T_d^RG||_op = alpha1"
        ∷ "Without that equality, Banach fixed-point and Clay Yang-Mills promotion remain false"
        ∷ []
    }

rgOperatorNormAlphaOneLessThanOneRecorded :
  alphaOneLessThanOneRecorded canonicalRGOperatorNormReceipt ≡ true
rgOperatorNormAlphaOneLessThanOneRecorded =
  refl

rgOperatorNormEqualityStillOpen :
  operatorNormEqualityProved canonicalRGOperatorNormReceipt ≡ false
rgOperatorNormEqualityStillOpen =
  refl

rgOperatorNormDoesNotPromoteClay :
  clayYangMillsPromoted canonicalRGOperatorNormReceipt ≡ false
rgOperatorNormDoesNotPromoteClay =
  refl

