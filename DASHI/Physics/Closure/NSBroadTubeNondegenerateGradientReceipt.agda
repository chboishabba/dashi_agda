module DASHI.Physics.Closure.NSBroadTubeNondegenerateGradientReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Broad-tube nondegenerate gradient socket receipt.
--
-- This file records a conditional socket construction for the lambda2
-- gradient / tube-thickness foliation lane.  The record is explicit about
-- hypotheses, dependencies, steps, and the open boundary.  It does not claim
-- an unconditional lambda2-gradient theorem and it does not claim Clay
-- promotion.

data NSBroadTubeNondegenerateGradientStatus : Set where
  nondegenerateGradientSocketConstructedConditionally :
    NSBroadTubeNondegenerateGradientStatus

data NSBroadTubeNondegenerateGradientHypothesis : Set where
  smoothLambda2Field :
    NSBroadTubeNondegenerateGradientHypothesis

  gradientLowerBoundOnTube :
    NSBroadTubeNondegenerateGradientHypothesis

  boundedSecondFundamentalForm :
    NSBroadTubeNondegenerateGradientHypothesis

  finiteTubularRadius :
    NSBroadTubeNondegenerateGradientHypothesis

  levelSetFoliation :
    NSBroadTubeNondegenerateGradientHypothesis

canonicalNSBroadTubeNondegenerateGradientHypotheses :
  List NSBroadTubeNondegenerateGradientHypothesis
canonicalNSBroadTubeNondegenerateGradientHypotheses =
  smoothLambda2Field
  ∷ gradientLowerBoundOnTube
  ∷ boundedSecondFundamentalForm
  ∷ finiteTubularRadius
  ∷ levelSetFoliation
  ∷ []

canonicalNSBroadTubeNondegenerateGradientHypothesisLabels :
  List String
canonicalNSBroadTubeNondegenerateGradientHypothesisLabels =
  "smooth lambda2 field"
  ∷ "gradient lower bound on tube"
  ∷ "bounded second fundamental form"
  ∷ "finite tubular radius"
  ∷ "level set foliation"
  ∷ []

data NSBroadTubeNondegenerateGradientDependency : Set where
  hypothesisRecord :
    NSBroadTubeNondegenerateGradientDependency

  tubeGeometrySocket :
    NSBroadTubeNondegenerateGradientDependency

  foliationSocket :
    NSBroadTubeNondegenerateGradientDependency

  conditionalGradientSocket :
    NSBroadTubeNondegenerateGradientDependency

canonicalNSBroadTubeNondegenerateGradientDependencies :
  List NSBroadTubeNondegenerateGradientDependency
canonicalNSBroadTubeNondegenerateGradientDependencies =
  hypothesisRecord
  ∷ tubeGeometrySocket
  ∷ foliationSocket
  ∷ conditionalGradientSocket
  ∷ []

data NSBroadTubeNondegenerateGradientStep : Set where
  recordSmoothLambda2Field :
    NSBroadTubeNondegenerateGradientStep

  recordGradientLowerBoundOnTube :
    NSBroadTubeNondegenerateGradientStep

  recordBoundedSecondFundamentalForm :
    NSBroadTubeNondegenerateGradientStep

  recordFiniteTubularRadius :
    NSBroadTubeNondegenerateGradientStep

  recordLevelSetFoliation :
    NSBroadTubeNondegenerateGradientStep

  constructNondegenerateGradientSocket :
    NSBroadTubeNondegenerateGradientStep

canonicalNSBroadTubeNondegenerateGradientSteps :
  List NSBroadTubeNondegenerateGradientStep
canonicalNSBroadTubeNondegenerateGradientSteps =
  recordSmoothLambda2Field
  ∷ recordGradientLowerBoundOnTube
  ∷ recordBoundedSecondFundamentalForm
  ∷ recordFiniteTubularRadius
  ∷ recordLevelSetFoliation
  ∷ constructNondegenerateGradientSocket
  ∷ []

data NSBroadTubeNondegenerateGradientConclusion : Set where
  nondegenerateGradientSocketConstructed :
    NSBroadTubeNondegenerateGradientConclusion

nondegenerateGradientSocketBridge :
  List NSBroadTubeNondegenerateGradientHypothesis →
  List NSBroadTubeNondegenerateGradientStep →
  NSBroadTubeNondegenerateGradientConclusion
nondegenerateGradientSocketBridge _ _ =
  nondegenerateGradientSocketConstructed

data NSBroadTubeNondegenerateGradientNoPromotion : Set where

noNSBroadTubeNondegenerateGradientPromotion :
  NSBroadTubeNondegenerateGradientNoPromotion →
  ⊥
noNSBroadTubeNondegenerateGradientPromotion ()

nsBroadTubeNondegenerateGradientStatement : String
nsBroadTubeNondegenerateGradientStatement =
  "Conditional broad-tube nondegenerate gradient socket: with smooth lambda2 field, gradient lower bound on tube, bounded second fundamental form, finite tubular radius, and level set foliation, the nondegenerate gradient socket is constructed conditionally."

nsBroadTubeNondegenerateGradientBoundary : String
nsBroadTubeNondegenerateGradientBoundary =
  "no Clay promotion claimed; no unconditional lambda2-gradient theorem claimed; this receipt only records the conditional socket boundary"

record NSBroadTubeNondegenerateGradientORCSLPGF : Set where
  constructor mkNSBroadTubeNondegenerateGradientORCSLPGF
  field
    O : String
    R : String
    C : String
    S : String
    L : String
    P : String
    G : String
    F : String

canonicalNSBroadTubeNondegenerateGradientORCSLPGF :
  NSBroadTubeNondegenerateGradientORCSLPGF
canonicalNSBroadTubeNondegenerateGradientORCSLPGF =
  mkNSBroadTubeNondegenerateGradientORCSLPGF
    "Record a conditional broad-tube nondegenerate gradient socket with explicit hypotheses."
    "Construct the nondegenerate gradient socket under smooth lambda2 field, gradient lower bound on tube, bounded second fundamental form, finite tubular radius, and level set foliation."
    "Dependencies are the hypothesis record, tube geometry socket, foliation socket, and conditional gradient socket."
    "Hypothesis list is fixed as smooth-lambda2-field, gradient-lower-bound-on-tube, bounded-second-fundamental-form, finite-tubular-radius, and level-set-foliation."
    "Linking path: hypotheses -> conditional steps -> nondegenerate gradient socket constructed."
    "No unconditional lambda2-gradient theorem is established at this node."
    "Clay promotion is explicitly false."
    "Keep the receipt fail-closed at the conditional socket level."

record NSBroadTubeNondegenerateGradientReceipt : Setω where
  field
    status :
      NSBroadTubeNondegenerateGradientStatus

    statusIsCanonical :
      status ≡ nondegenerateGradientSocketConstructedConditionally

    hypotheses :
      List NSBroadTubeNondegenerateGradientHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalNSBroadTubeNondegenerateGradientHypotheses

    hypothesisLabels :
      List String

    hypothesisLabelsAreCanonical :
      hypothesisLabels ≡ canonicalNSBroadTubeNondegenerateGradientHypothesisLabels

    dependencies :
      List NSBroadTubeNondegenerateGradientDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalNSBroadTubeNondegenerateGradientDependencies

    steps :
      List NSBroadTubeNondegenerateGradientStep

    stepsAreCanonical :
      steps ≡ canonicalNSBroadTubeNondegenerateGradientSteps

    bridgeConclusion :
      NSBroadTubeNondegenerateGradientConclusion

    bridgeConclusionIsCanonical :
      bridgeConclusion ≡
      nondegenerateGradientSocketBridge hypotheses steps

    smoothLambda2FieldRecorded :
      Bool

    smoothLambda2FieldRecordedIsTrue :
      smoothLambda2FieldRecorded ≡ true

    gradientLowerBoundOnTubeRecorded :
      Bool

    gradientLowerBoundOnTubeRecordedIsTrue :
      gradientLowerBoundOnTubeRecorded ≡ true

    boundedSecondFundamentalFormRecorded :
      Bool

    boundedSecondFundamentalFormRecordedIsTrue :
      boundedSecondFundamentalFormRecorded ≡ true

    finiteTubularRadiusRecorded :
      Bool

    finiteTubularRadiusRecordedIsTrue :
      finiteTubularRadiusRecorded ≡ true

    levelSetFoliationRecorded :
      Bool

    levelSetFoliationRecordedIsTrue :
      levelSetFoliationRecorded ≡ true

    unconditionalLambda2GradientTheorem :
      Bool

    unconditionalLambda2GradientTheoremIsFalse :
      unconditionalLambda2GradientTheorem ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBroadTubeNondegenerateGradientStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsBroadTubeNondegenerateGradientBoundary

    promotionFlags :
      List NSBroadTubeNondegenerateGradientNoPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡
      "no Clay promotion claimed"
      ∷ "no unconditional lambda2-gradient theorem claimed"
      ∷ "conditional socket only"
      ∷ []

    orcslpgf :
      NSBroadTubeNondegenerateGradientORCSLPGF

    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSBroadTubeNondegenerateGradientORCSLPGF

open NSBroadTubeNondegenerateGradientReceipt public

canonicalNSBroadTubeNondegenerateGradientReceipt :
  NSBroadTubeNondegenerateGradientReceipt
canonicalNSBroadTubeNondegenerateGradientReceipt =
  record
    { status =
        nondegenerateGradientSocketConstructedConditionally
    ; statusIsCanonical =
        refl
    ; hypotheses =
        canonicalNSBroadTubeNondegenerateGradientHypotheses
    ; hypothesesAreCanonical =
        refl
    ; hypothesisLabels =
        canonicalNSBroadTubeNondegenerateGradientHypothesisLabels
    ; hypothesisLabelsAreCanonical =
        refl
    ; dependencies =
        canonicalNSBroadTubeNondegenerateGradientDependencies
    ; dependenciesAreCanonical =
        refl
    ; steps =
        canonicalNSBroadTubeNondegenerateGradientSteps
    ; stepsAreCanonical =
        refl
    ; bridgeConclusion =
        nondegenerateGradientSocketBridge
          canonicalNSBroadTubeNondegenerateGradientHypotheses
          canonicalNSBroadTubeNondegenerateGradientSteps
    ; bridgeConclusionIsCanonical =
        refl
    ; smoothLambda2FieldRecorded =
        true
    ; smoothLambda2FieldRecordedIsTrue =
        refl
    ; gradientLowerBoundOnTubeRecorded =
        true
    ; gradientLowerBoundOnTubeRecordedIsTrue =
        refl
    ; boundedSecondFundamentalFormRecorded =
        true
    ; boundedSecondFundamentalFormRecordedIsTrue =
        refl
    ; finiteTubularRadiusRecorded =
        true
    ; finiteTubularRadiusRecordedIsTrue =
        refl
    ; levelSetFoliationRecorded =
        true
    ; levelSetFoliationRecordedIsTrue =
        refl
    ; unconditionalLambda2GradientTheorem =
        false
    ; unconditionalLambda2GradientTheoremIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; statement =
        nsBroadTubeNondegenerateGradientStatement
    ; statementIsCanonical =
        refl
    ; boundary =
        nsBroadTubeNondegenerateGradientBoundary
    ; boundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "no Clay promotion claimed"
        ∷ "no unconditional lambda2-gradient theorem claimed"
        ∷ "conditional socket only"
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    ; orcslpgf =
        canonicalNSBroadTubeNondegenerateGradientORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    }
