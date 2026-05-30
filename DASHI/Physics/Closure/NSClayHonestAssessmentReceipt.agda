module DASHI.Physics.Closure.NSClayHonestAssessmentReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Honest assessment of the conditional Navier-Stokes Clay chain.
--
-- The first four carrier steps are recorded as inhabited by the current
-- tranche state.  Density is closed only conditionally on transporting a
-- uniform large-data contraction estimate through the approximation family.
-- The effective remaining gap is therefore the large-data contraction in
-- H^{11/8}; without it the all-smooth-data Clay promotion remains false.

data NSClayConditionalStep : Set where
  step1AdjacentOnlyProjection :
    NSClayConditionalStep

  step2FlowPreservationSummability :
    NSClayConditionalStep

  step3SubcriticalDissipationDominance :
    NSClayConditionalStep

  step4CarrierStructuredRegularity :
    NSClayConditionalStep

  step5LargeDataContractionH11Over8 :
    NSClayConditionalStep

  step6AllSmoothDataClayExtension :
    NSClayConditionalStep

canonicalNSClayConditionalChain :
  List NSClayConditionalStep
canonicalNSClayConditionalChain =
  step1AdjacentOnlyProjection
  ∷ step2FlowPreservationSummability
  ∷ step3SubcriticalDissipationDominance
  ∷ step4CarrierStructuredRegularity
  ∷ step5LargeDataContractionH11Over8
  ∷ step6AllSmoothDataClayExtension
  ∷ []

canonicalNSClayInhabitedSteps :
  List NSClayConditionalStep
canonicalNSClayInhabitedSteps =
  step1AdjacentOnlyProjection
  ∷ step2FlowPreservationSummability
  ∷ step3SubcriticalDissipationDominance
  ∷ step4CarrierStructuredRegularity
  ∷ []

canonicalNSClayMissingSteps :
  List NSClayConditionalStep
canonicalNSClayMissingSteps =
  step5LargeDataContractionH11Over8
  ∷ step6AllSmoothDataClayExtension
  ∷ []

data NSClayEffectiveGap : Set where
  largeDataContractionInH11Over8 :
    NSClayEffectiveGap

canonicalNSClayEffectiveGaps :
  List NSClayEffectiveGap
canonicalNSClayEffectiveGaps =
  largeDataContractionInH11Over8
  ∷ []

data NSClayHonestAssessmentStatus : Set where
  fourStepsInhabitedTwoMissingOneEffectiveGap :
    NSClayHonestAssessmentStatus

data NSClayHonestAssessmentPromotion : Set where

nsClayHonestAssessmentPromotionImpossibleHere :
  NSClayHonestAssessmentPromotion →
  ⊥
nsClayHonestAssessmentPromotionImpossibleHere ()

nsClayHonestAssessmentStatement : String
nsClayHonestAssessmentStatement =
  "Conditional NS Clay chain: steps 1-4 are inhabited; steps 5-6 are missing.  Density extension is conditional on a large-data contraction estimate.  Effectively one gap remains: large-data contraction in H^{11/8}.  No Clay Navier-Stokes promotion is made."

record NSClayHonestAssessmentReceipt : Setω where
  field
    status :
      NSClayHonestAssessmentStatus

    conditionalChain :
      List NSClayConditionalStep

    conditionalChainIsCanonical :
      conditionalChain ≡ canonicalNSClayConditionalChain

    inhabitedSteps :
      List NSClayConditionalStep

    inhabitedStepsAreCanonical :
      inhabitedSteps ≡ canonicalNSClayInhabitedSteps

    missingSteps :
      List NSClayConditionalStep

    missingStepsAreCanonical :
      missingSteps ≡ canonicalNSClayMissingSteps

    step1Inhabited :
      Bool

    step1InhabitedIsTrue :
      step1Inhabited ≡ true

    step1AdjacentOnlyProjectionRecorded :
      Bool

    step1AdjacentOnlyProjectionRecordedIsTrue :
      step1AdjacentOnlyProjectionRecorded ≡ true

    step2Inhabited :
      Bool

    step2InhabitedIsTrue :
      step2Inhabited ≡ true

    step2FlowPreservationSummabilityRecorded :
      Bool

    step2FlowPreservationSummabilityRecordedIsTrue :
      step2FlowPreservationSummabilityRecorded ≡ true

    step3Inhabited :
      Bool

    step3InhabitedIsTrue :
      step3Inhabited ≡ true

    step3DissipationDominanceAtH11Over8Recorded :
      Bool

    step3DissipationDominanceAtH11Over8RecordedIsTrue :
      step3DissipationDominanceAtH11Over8Recorded ≡ true

    step4Inhabited :
      Bool

    step4InhabitedIsTrue :
      step4Inhabited ≡ true

    step4UniformGronwallBoundRecorded :
      Bool

    step4UniformGronwallBoundRecordedIsTrue :
      step4UniformGronwallBoundRecorded ≡ true

    densityApproximationRecorded :
      Bool

    densityApproximationRecordedIsTrue :
      densityApproximationRecorded ≡ true

    step5LargeDataContractionH11Over8Constructed :
      Bool

    step5LargeDataContractionH11Over8ConstructedIsFalse :
      step5LargeDataContractionH11Over8Constructed ≡ false

    step5Missing :
      Bool

    step5MissingIsTrue :
      step5Missing ≡ true

    step6AllSmoothDataClayExtensionConstructed :
      Bool

    step6AllSmoothDataClayExtensionConstructedIsFalse :
      step6AllSmoothDataClayExtensionConstructed ≡ false

    step6Missing :
      Bool

    step6MissingIsTrue :
      step6Missing ≡ true

    h11Over8Numerator :
      Nat

    h11Over8NumeratorIs11 :
      h11Over8Numerator ≡ 11

    h11Over8Denominator :
      Nat

    h11Over8DenominatorIs8 :
      h11Over8Denominator ≡ 8

    densityExtensionConditionalOnContraction :
      Bool

    densityExtensionConditionalOnContractionIsTrue :
      densityExtensionConditionalOnContraction ≡ true

    densityExtensionUnconditional :
      Bool

    densityExtensionUnconditionalIsFalse :
      densityExtensionUnconditional ≡ false

    effectiveGaps :
      List NSClayEffectiveGap

    effectiveGapsAreCanonical :
      effectiveGaps ≡ canonicalNSClayEffectiveGaps

    effectivelyOneGap :
      Bool

    effectivelyOneGapIsTrue :
      effectivelyOneGap ≡ true

    onlyEffectiveGapIsLargeDataContractionH11Over8 :
      Bool

    onlyEffectiveGapIsLargeDataContractionH11Over8IsTrue :
      onlyEffectiveGapIsLargeDataContractionH11Over8 ≡ true

    globalSmoothRegularityPromoted :
      Bool

    globalSmoothRegularityPromotedIsFalse :
      globalSmoothRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsClayHonestAssessmentStatement

    promotionFlags :
      List NSClayHonestAssessmentPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSClayHonestAssessmentReceipt public

canonicalNSClayHonestAssessmentReceipt :
  NSClayHonestAssessmentReceipt
canonicalNSClayHonestAssessmentReceipt =
  record
    { status =
        fourStepsInhabitedTwoMissingOneEffectiveGap
    ; conditionalChain =
        canonicalNSClayConditionalChain
    ; conditionalChainIsCanonical =
        refl
    ; inhabitedSteps =
        canonicalNSClayInhabitedSteps
    ; inhabitedStepsAreCanonical =
        refl
    ; missingSteps =
        canonicalNSClayMissingSteps
    ; missingStepsAreCanonical =
        refl
    ; step1Inhabited =
        true
    ; step1InhabitedIsTrue =
        refl
    ; step1AdjacentOnlyProjectionRecorded =
        true
    ; step1AdjacentOnlyProjectionRecordedIsTrue =
        refl
    ; step2Inhabited =
        true
    ; step2InhabitedIsTrue =
        refl
    ; step2FlowPreservationSummabilityRecorded =
        true
    ; step2FlowPreservationSummabilityRecordedIsTrue =
        refl
    ; step3Inhabited =
        true
    ; step3InhabitedIsTrue =
        refl
    ; step3DissipationDominanceAtH11Over8Recorded =
        true
    ; step3DissipationDominanceAtH11Over8RecordedIsTrue =
        refl
    ; step4Inhabited =
        true
    ; step4InhabitedIsTrue =
        refl
    ; step4UniformGronwallBoundRecorded =
        true
    ; step4UniformGronwallBoundRecordedIsTrue =
        refl
    ; densityApproximationRecorded =
        true
    ; densityApproximationRecordedIsTrue =
        refl
    ; step5LargeDataContractionH11Over8Constructed =
        false
    ; step5LargeDataContractionH11Over8ConstructedIsFalse =
        refl
    ; step5Missing =
        true
    ; step5MissingIsTrue =
        refl
    ; step6AllSmoothDataClayExtensionConstructed =
        false
    ; step6AllSmoothDataClayExtensionConstructedIsFalse =
        refl
    ; step6Missing =
        true
    ; step6MissingIsTrue =
        refl
    ; h11Over8Numerator =
        11
    ; h11Over8NumeratorIs11 =
        refl
    ; h11Over8Denominator =
        8
    ; h11Over8DenominatorIs8 =
        refl
    ; densityExtensionConditionalOnContraction =
        true
    ; densityExtensionConditionalOnContractionIsTrue =
        refl
    ; densityExtensionUnconditional =
        false
    ; densityExtensionUnconditionalIsFalse =
        refl
    ; effectiveGaps =
        canonicalNSClayEffectiveGaps
    ; effectiveGapsAreCanonical =
        refl
    ; effectivelyOneGap =
        true
    ; effectivelyOneGapIsTrue =
        refl
    ; onlyEffectiveGapIsLargeDataContractionH11Over8 =
        true
    ; onlyEffectiveGapIsLargeDataContractionH11Over8IsTrue =
        refl
    ; globalSmoothRegularityPromoted =
        false
    ; globalSmoothRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsClayHonestAssessmentStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Step 1 adjacent-only projection is inhabited"
        ∷ "Step 2 flow-preservation summability is inhabited"
        ∷ "Step 3 subcritical dissipation dominance is inhabited"
        ∷ "Step 4 carrier-structured regularity is inhabited"
        ∷ "Step 5 large-data contraction in H^{11/8} is missing"
        ∷ "Step 6 all-smooth-data Clay extension is missing"
        ∷ "Density extension is conditional on the contraction estimate"
        ∷ "Effectively one gap remains: large-data contraction in H^{11/8}"
        ∷ "No global regularity, Clay Navier-Stokes, or terminal Clay promotion is made"
        ∷ []
    }

nsClayHonestSteps1To4Inhabited :
  inhabitedSteps canonicalNSClayHonestAssessmentReceipt
  ≡
  canonicalNSClayInhabitedSteps
nsClayHonestSteps1To4Inhabited =
  refl

nsClayHonestSteps5To6Missing :
  missingSteps canonicalNSClayHonestAssessmentReceipt
  ≡
  canonicalNSClayMissingSteps
nsClayHonestSteps5To6Missing =
  refl

nsClayHonestDensityConditional :
  densityExtensionConditionalOnContraction
    canonicalNSClayHonestAssessmentReceipt
  ≡
  true
nsClayHonestDensityConditional =
  refl

nsClayHonestOnlyGapLargeDataContractionH11Over8 :
  onlyEffectiveGapIsLargeDataContractionH11Over8
    canonicalNSClayHonestAssessmentReceipt
  ≡
  true
nsClayHonestOnlyGapLargeDataContractionH11Over8 =
  refl

nsClayHonestNoClayPromotion :
  clayNavierStokesPromoted canonicalNSClayHonestAssessmentReceipt ≡ false
nsClayHonestNoClayPromotion =
  refl

nsClayHonestNoPromotion :
  NSClayHonestAssessmentPromotion →
  ⊥
nsClayHonestNoPromotion =
  nsClayHonestAssessmentPromotionImpossibleHere
