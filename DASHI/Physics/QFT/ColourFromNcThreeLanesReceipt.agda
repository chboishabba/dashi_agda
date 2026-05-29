module DASHI.Physics.QFT.ColourFromNcThreeLanesReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Colour from N_c = 3 prime-lane diagnostic receipt.
--
-- This receipt records the finite observation that the three quark lanes
-- give N_c = 3 and admit an S3 Weyl-symmetry candidate.  It also records the
-- obstruction: the carrier lane metric is not invariant under the full
-- continuous SU(3) action, so exact SU3_c is not promoted.  The chiral-limit
-- colour interpretation is recorded only as an approximate/candidate route.

data QuarkPrimeLane : Set where
  p2QuarkLane :
    QuarkPrimeLane

  p3QuarkLane :
    QuarkPrimeLane

  p5QuarkLane :
    QuarkPrimeLane

canonicalQuarkPrimeLanes :
  List QuarkPrimeLane
canonicalQuarkPrimeLanes =
  p2QuarkLane
  ∷ p3QuarkLane
  ∷ p5QuarkLane
  ∷ []

canonicalNc :
  Nat
canonicalNc =
  3

data ThreeLaneWeylSymmetry : Set where
  S3WeylSymmetryCandidate :
    ThreeLaneWeylSymmetry

data ContinuousSU3ExtensionStatus : Set where
  blockedByNonInvariantLaneMetric :
    ContinuousSU3ExtensionStatus

data ColourCandidateStatus : Set where
  approximateChiralLimitCandidate :
    ColourCandidateStatus

threeLaneSpaceLabel : String
threeLaneSpaceLabel =
  "The p2/p3/p5 quark-lane span is a three-dimensional carrier lane space"

s3WeylCandidateLabel : String
s3WeylCandidateLabel =
  "S3 is recorded as the discrete Weyl-symmetry candidate for the three quark lanes"

metricObstructionLabel : String
metricObstructionLabel =
  "The lane metric is not SU(3)-invariant because the p2, p3, and p5 lanes carry distinct carrier weights"

continuousExtensionBlockedLabel : String
continuousExtensionBlockedLabel =
  "Full SU(3) requires a continuous unitary determinant-one extension of S3 with invariant lane metric; this is blocked here"

chiralLimitCandidateLabel : String
chiralLimitCandidateLabel =
  "Approximate colour is recorded as a chiral-limit candidate in which lane-metric mass splittings become irrelevant"

exactSU3cFalseLabel : String
exactSU3cFalseLabel =
  "Exact SU3_c is false in this receipt"

exactGDHREqualsGSMFalseLabel : String
exactGDHREqualsGSMFalseLabel =
  "Exact G_DHR ~= G_SM is false in this receipt"

record ColourFromNcThreeLanesReceipt : Setω where
  field
    quarkPrimeLanes :
      List QuarkPrimeLane

    quarkPrimeLanesAreCanonical :
      quarkPrimeLanes ≡ canonicalQuarkPrimeLanes

    nc :
      Nat

    ncIsThree :
      nc ≡ canonicalNc

    ncFromThreeQuarkLanes :
      Bool

    ncFromThreeQuarkLanesIsTrue :
      ncFromThreeQuarkLanes ≡ true

    threeLaneSpace :
      String

    threeLaneSpaceIsCanonical :
      threeLaneSpace ≡ threeLaneSpaceLabel

    discreteWeylSymmetryCandidate :
      ThreeLaneWeylSymmetry

    discreteWeylSymmetryCandidateIsS3 :
      discreteWeylSymmetryCandidate ≡ S3WeylSymmetryCandidate

    s3WeylCandidate :
      Bool

    s3WeylCandidateIsTrue :
      s3WeylCandidate ≡ true

    s3WeylCandidateBoundary :
      String

    s3WeylCandidateBoundaryIsCanonical :
      s3WeylCandidateBoundary ≡ s3WeylCandidateLabel

    laneMetricSU3Invariant :
      Bool

    laneMetricSU3InvariantIsFalse :
      laneMetricSU3Invariant ≡ false

    laneMetricObstruction :
      String

    laneMetricObstructionIsCanonical :
      laneMetricObstruction ≡ metricObstructionLabel

    continuousSU3Extension :
      ContinuousSU3ExtensionStatus

    continuousSU3ExtensionIsBlockedByMetric :
      continuousSU3Extension ≡ blockedByNonInvariantLaneMetric

    continuousSU3ExtensionBoundary :
      String

    continuousSU3ExtensionBoundaryIsCanonical :
      continuousSU3ExtensionBoundary ≡ continuousExtensionBlockedLabel

    approximateColourCandidate :
      Bool

    approximateColourCandidateIsTrue :
      approximateColourCandidate ≡ true

    chiralLimitColourCandidate :
      ColourCandidateStatus

    chiralLimitColourCandidateIsApproximate :
      chiralLimitColourCandidate ≡ approximateChiralLimitCandidate

    chiralLimitColourBoundary :
      String

    chiralLimitColourBoundaryIsCanonical :
      chiralLimitColourBoundary ≡ chiralLimitCandidateLabel

    exactSU3c :
      Bool

    exactSU3cIsFalse :
      exactSU3c ≡ false

    exactSU3cBoundary :
      String

    exactSU3cBoundaryIsCanonical :
      exactSU3cBoundary ≡ exactSU3cFalseLabel

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    exactGDHREqualsGSMBoundary :
      String

    exactGDHREqualsGSMBoundaryIsCanonical :
      exactGDHREqualsGSMBoundary ≡ exactGDHREqualsGSMFalseLabel

    receiptBoundary :
      List String

open ColourFromNcThreeLanesReceipt public

canonicalColourFromNcThreeLanesReceipt :
  ColourFromNcThreeLanesReceipt
canonicalColourFromNcThreeLanesReceipt =
  record
    { quarkPrimeLanes =
        canonicalQuarkPrimeLanes
    ; quarkPrimeLanesAreCanonical =
        refl
    ; nc =
        canonicalNc
    ; ncIsThree =
        refl
    ; ncFromThreeQuarkLanes =
        true
    ; ncFromThreeQuarkLanesIsTrue =
        refl
    ; threeLaneSpace =
        threeLaneSpaceLabel
    ; threeLaneSpaceIsCanonical =
        refl
    ; discreteWeylSymmetryCandidate =
        S3WeylSymmetryCandidate
    ; discreteWeylSymmetryCandidateIsS3 =
        refl
    ; s3WeylCandidate =
        true
    ; s3WeylCandidateIsTrue =
        refl
    ; s3WeylCandidateBoundary =
        s3WeylCandidateLabel
    ; s3WeylCandidateBoundaryIsCanonical =
        refl
    ; laneMetricSU3Invariant =
        false
    ; laneMetricSU3InvariantIsFalse =
        refl
    ; laneMetricObstruction =
        metricObstructionLabel
    ; laneMetricObstructionIsCanonical =
        refl
    ; continuousSU3Extension =
        blockedByNonInvariantLaneMetric
    ; continuousSU3ExtensionIsBlockedByMetric =
        refl
    ; continuousSU3ExtensionBoundary =
        continuousExtensionBlockedLabel
    ; continuousSU3ExtensionBoundaryIsCanonical =
        refl
    ; approximateColourCandidate =
        true
    ; approximateColourCandidateIsTrue =
        refl
    ; chiralLimitColourCandidate =
        approximateChiralLimitCandidate
    ; chiralLimitColourCandidateIsApproximate =
        refl
    ; chiralLimitColourBoundary =
        chiralLimitCandidateLabel
    ; chiralLimitColourBoundaryIsCanonical =
        refl
    ; exactSU3c =
        false
    ; exactSU3cIsFalse =
        refl
    ; exactSU3cBoundary =
        exactSU3cFalseLabel
    ; exactSU3cBoundaryIsCanonical =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; exactGDHREqualsGSMBoundary =
        exactGDHREqualsGSMFalseLabel
    ; exactGDHREqualsGSMBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "N_c=3 is recorded from the three quark lanes p2, p3, and p5"
        ∷ "S3 is recorded as the finite Weyl-symmetry candidate for the three-lane space"
        ∷ "Full continuous SU(3) is blocked because the carrier lane metric is not SU(3)-invariant"
        ∷ "Approximate colour is recorded only as a chiral-limit candidate"
        ∷ "Exact SU3_c and exact G_DHR ~= G_SM remain false"
        ∷ []
    }

colourFromNcThreeLanesNcIsThree :
  nc canonicalColourFromNcThreeLanesReceipt
  ≡
  3
colourFromNcThreeLanesNcIsThree =
  refl

colourFromNcThreeLanesNcFromThreeQuarkLanesIsTrue :
  ncFromThreeQuarkLanes canonicalColourFromNcThreeLanesReceipt
  ≡
  true
colourFromNcThreeLanesNcFromThreeQuarkLanesIsTrue =
  refl

colourFromNcThreeLanesS3WeylCandidateIsTrue :
  s3WeylCandidate canonicalColourFromNcThreeLanesReceipt
  ≡
  true
colourFromNcThreeLanesS3WeylCandidateIsTrue =
  refl

colourFromNcThreeLanesMetricInvariantIsFalse :
  laneMetricSU3Invariant canonicalColourFromNcThreeLanesReceipt
  ≡
  false
colourFromNcThreeLanesMetricInvariantIsFalse =
  refl

colourFromNcThreeLanesContinuousSU3BlockedByMetric :
  continuousSU3Extension canonicalColourFromNcThreeLanesReceipt
  ≡
  blockedByNonInvariantLaneMetric
colourFromNcThreeLanesContinuousSU3BlockedByMetric =
  refl

colourFromNcThreeLanesChiralLimitCandidateIsApproximate :
  chiralLimitColourCandidate canonicalColourFromNcThreeLanesReceipt
  ≡
  approximateChiralLimitCandidate
colourFromNcThreeLanesChiralLimitCandidateIsApproximate =
  refl

colourFromNcThreeLanesExactSU3cIsFalse :
  exactSU3c canonicalColourFromNcThreeLanesReceipt
  ≡
  false
colourFromNcThreeLanesExactSU3cIsFalse =
  refl

colourFromNcThreeLanesExactGDHREqualsGSMIsFalse :
  exactGDHREqualsGSM canonicalColourFromNcThreeLanesReceipt
  ≡
  false
colourFromNcThreeLanesExactGDHREqualsGSMIsFalse =
  refl
