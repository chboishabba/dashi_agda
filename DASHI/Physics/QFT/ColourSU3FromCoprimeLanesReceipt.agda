module DASHI.Physics.QFT.ColourSU3FromCoprimeLanesReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU(3) colour from pairwise-coprime quark lanes receipt.
--
-- This receipt records a candidate route: three pairwise-coprime quark
-- lanes have a chiral-limit degeneracy with an S3/Weyl symmetry candidate.
-- The current mass metric breaks that degeneracy, so exact continuous
-- SU(3)_c, exact Standard Model, and G_DHR ~= G_SM promotion stay false.

data CoprimeQuarkLane : Set where
  p2QuarkLane :
    CoprimeQuarkLane

  p3QuarkLane :
    CoprimeQuarkLane

  p5QuarkLane :
    CoprimeQuarkLane

canonicalCoprimeQuarkLanes :
  List CoprimeQuarkLane
canonicalCoprimeQuarkLanes =
  p2QuarkLane
  ∷ p3QuarkLane
  ∷ p5QuarkLane
  ∷ []

data PairwiseCoprimeWitness : Set where
  p2p3Coprime :
    PairwiseCoprimeWitness

  p2p5Coprime :
    PairwiseCoprimeWitness

  p3p5Coprime :
    PairwiseCoprimeWitness

canonicalPairwiseCoprimeWitnesses :
  List PairwiseCoprimeWitness
canonicalPairwiseCoprimeWitnesses =
  p2p3Coprime
  ∷ p2p5Coprime
  ∷ p3p5Coprime
  ∷ []

data SU3CoprimeLaneStatus : Set where
  chiralLimitDegeneracyCandidateBrokenByMassMetric :
    SU3CoprimeLaneStatus

data SU3WeylCandidate : Set where
  s3AsSU3WeylCandidate :
    SU3WeylCandidate

data MassMetricStatus : Set where
  nonDegenerateMassMetricBreaksS3Weyl :
    MassMetricStatus

laneCount :
  Nat
laneCount =
  3

chiralLimitDegeneracyLabel :
  String
chiralLimitDegeneracyLabel =
  "in the chiral limit the three pairwise-coprime quark lanes are recorded as a degenerate colour-triplet candidate"

s3WeylCandidateLabel :
  String
s3WeylCandidateLabel =
  "the lane permutation S3 is recorded as the Weyl candidate for SU(3)"

massMetricBreakingLabel :
  String
massMetricBreakingLabel =
  "away from the chiral limit the nondegenerate quark-lane mass metric breaks the S3/Weyl degeneracy"

candidateOnlyBoundaryLabel :
  String
candidateOnlyBoundaryLabel =
  "SU3 colour is candidate-only here; exact gauge, Standard Model, and G_DHR ~= G_SM flags remain false"

canonicalColourSU3FromCoprimeLanesBoundary :
  List String
canonicalColourSU3FromCoprimeLanesBoundary =
  chiralLimitDegeneracyLabel
  ∷ s3WeylCandidateLabel
  ∷ massMetricBreakingLabel
  ∷ candidateOnlyBoundaryLabel
  ∷ []

record ColourSU3FromCoprimeLanesReceipt : Set where
  field
    status :
      SU3CoprimeLaneStatus

    statusIsChiralLimitCandidateBrokenByMassMetric :
      status ≡ chiralLimitDegeneracyCandidateBrokenByMassMetric

    quarkLanes :
      List CoprimeQuarkLane

    quarkLanesAreCanonical :
      quarkLanes ≡ canonicalCoprimeQuarkLanes

    quarkLaneCount :
      Nat

    quarkLaneCountIsThree :
      quarkLaneCount ≡ laneCount

    pairwiseCoprimeWitnesses :
      List PairwiseCoprimeWitness

    pairwiseCoprimeWitnessesAreCanonical :
      pairwiseCoprimeWitnesses ≡ canonicalPairwiseCoprimeWitnesses

    pairwiseCoprimeLanes :
      Bool

    pairwiseCoprimeLanesIsTrue :
      pairwiseCoprimeLanes ≡ true

    chiralLimitDegenerate :
      Bool

    chiralLimitDegenerateIsTrue :
      chiralLimitDegenerate ≡ true

    colourTripletCandidate :
      Bool

    colourTripletCandidateIsTrue :
      colourTripletCandidate ≡ true

    s3WeylCandidate :
      SU3WeylCandidate

    s3WeylCandidateIsCanonical :
      s3WeylCandidate ≡ s3AsSU3WeylCandidate

    lanePermutationS3Candidate :
      Bool

    lanePermutationS3CandidateIsTrue :
      lanePermutationS3Candidate ≡ true

    massMetricStatus :
      MassMetricStatus

    massMetricStatusIsBreaking :
      massMetricStatus ≡ nonDegenerateMassMetricBreaksS3Weyl

    massMetricDegenerate :
      Bool

    massMetricDegenerateIsFalse :
      massMetricDegenerate ≡ false

    massMetricBreaksCandidate :
      Bool

    massMetricBreaksCandidateIsTrue :
      massMetricBreaksCandidate ≡ true

    continuousSU3ColourDerived :
      Bool

    continuousSU3ColourDerivedIsFalse :
      continuousSU3ColourDerived ≡ false

    exactGaugePromotion :
      Bool

    exactGaugePromotionIsFalse :
      exactGaugePromotion ≡ false

    exactSU3cPromotion :
      Bool

    exactSU3cPromotionIsFalse :
      exactSU3cPromotion ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSMPromotion :
      Bool

    exactGDHREqualsGSMPromotionIsFalse :
      exactGDHREqualsGSMPromotion ≡ false

    chiralLimitDegeneracyBoundary :
      String

    chiralLimitDegeneracyBoundaryIsCanonical :
      chiralLimitDegeneracyBoundary ≡ chiralLimitDegeneracyLabel

    s3WeylCandidateBoundary :
      String

    s3WeylCandidateBoundaryIsCanonical :
      s3WeylCandidateBoundary ≡ s3WeylCandidateLabel

    massMetricBreakingBoundary :
      String

    massMetricBreakingBoundaryIsCanonical :
      massMetricBreakingBoundary ≡ massMetricBreakingLabel

    candidateOnlyBoundary :
      String

    candidateOnlyBoundaryIsCanonical :
      candidateOnlyBoundary ≡ candidateOnlyBoundaryLabel

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalColourSU3FromCoprimeLanesBoundary

open ColourSU3FromCoprimeLanesReceipt public

canonicalColourSU3FromCoprimeLanesReceipt :
  ColourSU3FromCoprimeLanesReceipt
canonicalColourSU3FromCoprimeLanesReceipt =
  record
    { status =
        chiralLimitDegeneracyCandidateBrokenByMassMetric
    ; statusIsChiralLimitCandidateBrokenByMassMetric =
        refl
    ; quarkLanes =
        canonicalCoprimeQuarkLanes
    ; quarkLanesAreCanonical =
        refl
    ; quarkLaneCount =
        laneCount
    ; quarkLaneCountIsThree =
        refl
    ; pairwiseCoprimeWitnesses =
        canonicalPairwiseCoprimeWitnesses
    ; pairwiseCoprimeWitnessesAreCanonical =
        refl
    ; pairwiseCoprimeLanes =
        true
    ; pairwiseCoprimeLanesIsTrue =
        refl
    ; chiralLimitDegenerate =
        true
    ; chiralLimitDegenerateIsTrue =
        refl
    ; colourTripletCandidate =
        true
    ; colourTripletCandidateIsTrue =
        refl
    ; s3WeylCandidate =
        s3AsSU3WeylCandidate
    ; s3WeylCandidateIsCanonical =
        refl
    ; lanePermutationS3Candidate =
        true
    ; lanePermutationS3CandidateIsTrue =
        refl
    ; massMetricStatus =
        nonDegenerateMassMetricBreaksS3Weyl
    ; massMetricStatusIsBreaking =
        refl
    ; massMetricDegenerate =
        false
    ; massMetricDegenerateIsFalse =
        refl
    ; massMetricBreaksCandidate =
        true
    ; massMetricBreaksCandidateIsTrue =
        refl
    ; continuousSU3ColourDerived =
        false
    ; continuousSU3ColourDerivedIsFalse =
        refl
    ; exactGaugePromotion =
        false
    ; exactGaugePromotionIsFalse =
        refl
    ; exactSU3cPromotion =
        false
    ; exactSU3cPromotionIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSMPromotion =
        false
    ; exactGDHREqualsGSMPromotionIsFalse =
        refl
    ; chiralLimitDegeneracyBoundary =
        chiralLimitDegeneracyLabel
    ; chiralLimitDegeneracyBoundaryIsCanonical =
        refl
    ; s3WeylCandidateBoundary =
        s3WeylCandidateLabel
    ; s3WeylCandidateBoundaryIsCanonical =
        refl
    ; massMetricBreakingBoundary =
        massMetricBreakingLabel
    ; massMetricBreakingBoundaryIsCanonical =
        refl
    ; candidateOnlyBoundary =
        candidateOnlyBoundaryLabel
    ; candidateOnlyBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        canonicalColourSU3FromCoprimeLanesBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

colourSU3CoprimeLaneCountIsThree :
  quarkLaneCount canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  3
colourSU3CoprimeLaneCountIsThree =
  refl

colourSU3CoprimeLanesArePairwiseCoprime :
  pairwiseCoprimeLanes canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  true
colourSU3CoprimeLanesArePairwiseCoprime =
  refl

colourSU3ChiralLimitDegeneracyCandidate :
  chiralLimitDegenerate canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  true
colourSU3ChiralLimitDegeneracyCandidate =
  refl

colourSU3MassMetricBreaksCandidate :
  massMetricBreaksCandidate canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  true
colourSU3MassMetricBreaksCandidate =
  refl

colourSU3ExactGaugePromotionFalse :
  exactGaugePromotion canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  false
colourSU3ExactGaugePromotionFalse =
  refl

colourSU3ExactSMFalse :
  exactStandardModelPromotion canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  false
colourSU3ExactSMFalse =
  refl

colourSU3ExactGDHRGSMFalse :
  exactGDHREqualsGSMPromotion canonicalColourSU3FromCoprimeLanesReceipt
  ≡
  false
colourSU3ExactGDHRGSMFalse =
  refl
