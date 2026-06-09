module DASHI.Physics.Closure.YMGeometricGapClosingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yang-Mills geometric gap closing receipt.
--
-- This receipt records the scale separation between the geometric spectral
-- gap in the cusp-degeneration carrier and the physical Yang-Mills mass gap.
-- Near a cusp at level N, the geometric Laplacian scale is recorded as
-- lambda_geom ~ (2*pi/N)^2, so it closes as N -> infinity.  The dynamical
-- Yang-Mills gap is instead recorded as m_gap^2 ~ Lambda_QCD^2 and remains
-- fixed.  In the large-N flat regime N >> 2*pi/Lambda_QCD, approximated here
-- by the receipt flag NMuchGreaterThan31, lambda_geom is negligible compared
-- to m_gap^2.  Thus the geometric spectral gap does not contribute to the
-- physical mass gap at large N.

data YMGeometricGapClosingStatus : Set where
  geometricGapClosingScaleSeparationRecorded :
    YMGeometricGapClosingStatus

data YMGeometricGapAsymptotic : Set where
  oneOverNSquared :
    YMGeometricGapAsymptotic

data YMDynamicalGapScale : Set where
  LambdaQCDSquared :
    YMDynamicalGapScale

data YMFlatRegimeCondition : Set where
  NMuchGreaterThan31 :
    YMFlatRegimeCondition

data YMGeometricGapClosingFact : Set where
  cuspLaplacianEigenvaluesScaleAsTwoPiOverNSquared :
    YMGeometricGapClosingFact

  geometricSpectralGapClosesAsNToInfinity :
    YMGeometricGapClosingFact

  dynamicalYangMillsMassGapScaleFixed :
    YMGeometricGapClosingFact

  largeNThresholdApproximatelyThirtyOne :
    YMGeometricGapClosingFact

  geometricGapNegligibleComparedToDynamicalGap :
    YMGeometricGapClosingFact

  geometricGapDoesNotSupplyPhysicalMassGap :
    YMGeometricGapClosingFact

canonicalYMGeometricGapClosingFacts :
  List YMGeometricGapClosingFact
canonicalYMGeometricGapClosingFacts =
  cuspLaplacianEigenvaluesScaleAsTwoPiOverNSquared
  ∷ geometricSpectralGapClosesAsNToInfinity
  ∷ dynamicalYangMillsMassGapScaleFixed
  ∷ largeNThresholdApproximatelyThirtyOne
  ∷ geometricGapNegligibleComparedToDynamicalGap
  ∷ geometricGapDoesNotSupplyPhysicalMassGap
  ∷ []

ymGeometricGapClosingStatement : String
ymGeometricGapClosingStatement =
  "Geometric spectral gap closes as N -> infinity: near a cusp, Laplacian eigenvalues obey lambda_geom ~ (2*pi/N)^2, hence lambda_geom -> 0.  The dynamical Yang-Mills mass gap has m_gap^2 ~ Lambda_QCD^2 fixed.  For N >> 2*pi/Lambda_QCD, approximated by N >> 31, lambda_geom << m_gap^2, so the geometric spectral gap does not contribute to the physical mass gap at large N."

record YMGeometricGapClosingReceipt : Setω where
  field
    status :
      YMGeometricGapClosingStatus

    statusIsCanonical :
      status ≡ geometricGapClosingScaleSeparationRecorded

    geometricGapClosesAsN :
      YMGeometricGapAsymptotic

    geometricGapClosesAsNIsOneOverNSquared :
      geometricGapClosesAsN ≡ oneOverNSquared

    laplacianEigenvalueScale :
      String

    laplacianEigenvalueScaleIsCanonical :
      laplacianEigenvalueScale ≡ "lambda_geom ~ (2*pi/N)^2"

    geometricGapLimit :
      String

    geometricGapLimitIsZero :
      geometricGapLimit ≡ "lambda_geom -> 0 as N -> infinity"

    dynamicalGapFixed :
      YMDynamicalGapScale

    dynamicalGapFixedIsLambdaQCDSquared :
      dynamicalGapFixed ≡ LambdaQCDSquared

    dynamicalMassGapScale :
      String

    dynamicalMassGapScaleIsCanonical :
      dynamicalMassGapScale ≡ "m_gap^2 ~ Lambda_QCD^2"

    flatRegimeCondition :
      YMFlatRegimeCondition

    flatRegimeConditionIsNMuchGreaterThan31 :
      flatRegimeCondition ≡ NMuchGreaterThan31

    flatRegimeThreshold :
      String

    flatRegimeThresholdIsCanonical :
      flatRegimeThreshold ≡ "N >> 2*pi/Lambda_QCD approx 31"

    geometricGapNegligibleAtLargeN :
      Bool

    geometricGapNegligibleAtLargeNIsTrue :
      geometricGapNegligibleAtLargeN ≡ true

    geometricGapContributesToPhysicalMassGapAtLargeN :
      Bool

    geometricGapContributesToPhysicalMassGapAtLargeNIsFalse :
      geometricGapContributesToPhysicalMassGapAtLargeN ≡ false

    facts :
      List YMGeometricGapClosingFact

    factsAreCanonical :
      facts ≡ canonicalYMGeometricGapClosingFacts

    statement :
      String

    statementIsCanonical :
      statement ≡ ymGeometricGapClosingStatement

    receiptBoundary :
      List String

open YMGeometricGapClosingReceipt public

canonicalYMGeometricGapClosingReceipt :
  YMGeometricGapClosingReceipt
canonicalYMGeometricGapClosingReceipt =
  record
    { status =
        geometricGapClosingScaleSeparationRecorded
    ; statusIsCanonical =
        refl
    ; geometricGapClosesAsN =
        oneOverNSquared
    ; geometricGapClosesAsNIsOneOverNSquared =
        refl
    ; laplacianEigenvalueScale =
        "lambda_geom ~ (2*pi/N)^2"
    ; laplacianEigenvalueScaleIsCanonical =
        refl
    ; geometricGapLimit =
        "lambda_geom -> 0 as N -> infinity"
    ; geometricGapLimitIsZero =
        refl
    ; dynamicalGapFixed =
        LambdaQCDSquared
    ; dynamicalGapFixedIsLambdaQCDSquared =
        refl
    ; dynamicalMassGapScale =
        "m_gap^2 ~ Lambda_QCD^2"
    ; dynamicalMassGapScaleIsCanonical =
        refl
    ; flatRegimeCondition =
        NMuchGreaterThan31
    ; flatRegimeConditionIsNMuchGreaterThan31 =
        refl
    ; flatRegimeThreshold =
        "N >> 2*pi/Lambda_QCD approx 31"
    ; flatRegimeThresholdIsCanonical =
        refl
    ; geometricGapNegligibleAtLargeN =
        true
    ; geometricGapNegligibleAtLargeNIsTrue =
        refl
    ; geometricGapContributesToPhysicalMassGapAtLargeN =
        false
    ; geometricGapContributesToPhysicalMassGapAtLargeNIsFalse =
        refl
    ; facts =
        canonicalYMGeometricGapClosingFacts
    ; factsAreCanonical =
        refl
    ; statement =
        ymGeometricGapClosingStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "geometricGapClosesAsN = oneOverNSquared"
        ∷ "lambda_geom ~ (2*pi/N)^2, hence lambda_geom -> 0 as N -> infinity"
        ∷ "dynamicalGapFixed = LambdaQCDSquared"
        ∷ "flatRegimeCondition = NMuchGreaterThan31"
        ∷ "For N >> 2*pi/Lambda_QCD approx 31, lambda_geom << m_gap^2"
        ∷ "geometricGapNegligibleAtLargeN = true"
        ∷ "The geometric spectral gap does not contribute to the physical mass gap at large N"
        ∷ []
    }

geometricGapClosingFlag :
  geometricGapClosesAsN canonicalYMGeometricGapClosingReceipt
  ≡
  oneOverNSquared
geometricGapClosingFlag =
  refl

dynamicalGapFixedFlag :
  dynamicalGapFixed canonicalYMGeometricGapClosingReceipt
  ≡
  LambdaQCDSquared
dynamicalGapFixedFlag =
  refl

flatRegimeConditionFlag :
  flatRegimeCondition canonicalYMGeometricGapClosingReceipt
  ≡
  NMuchGreaterThan31
flatRegimeConditionFlag =
  refl

geometricGapNegligibleAtLargeNFlag :
  geometricGapNegligibleAtLargeN canonicalYMGeometricGapClosingReceipt
  ≡
  true
geometricGapNegligibleAtLargeNFlag =
  refl
