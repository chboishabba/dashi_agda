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
-- exact analytic assumptions, the ODE/min-principle kernel route, the open
-- boundary, and the promotion blockers.  It does not claim an unconditional
-- lambda2-gradient theorem and it does not claim Clay promotion.

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

data NSBroadTubeNondegenerateGradientExactAssumption : Set where
  lambda2IsC1OnTube :
    NSBroadTubeNondegenerateGradientExactAssumption

  lambda2IsC2AlongFoliation :
    NSBroadTubeNondegenerateGradientExactAssumption

  strictGradientLowerBoundForNondegeneracy :
    NSBroadTubeNondegenerateGradientExactAssumption

  finiteTubularRadiusWitness :
    NSBroadTubeNondegenerateGradientExactAssumption

  regularLevelSetFoliationWitness :
    NSBroadTubeNondegenerateGradientExactAssumption

  boundedSecondFundamentalFormWitness :
    NSBroadTubeNondegenerateGradientExactAssumption

  admissibleBoundaryDataForMinimumPrinciple :
    NSBroadTubeNondegenerateGradientExactAssumption

  rellichFirstDerivativeFormula :
    NSBroadTubeNondegenerateGradientExactAssumption

  katoHessianLaplacianFormula :
    NSBroadTubeNondegenerateGradientExactAssumption

  simpleEigenvalueGapLowerBoundG12 :
    NSBroadTubeNondegenerateGradientExactAssumption

  simpleEigenvalueGapLowerBoundG23 :
    NSBroadTubeNondegenerateGradientExactAssumption

  h3SardCoareaEstimate :
    NSBroadTubeNondegenerateGradientExactAssumption

  coareaNondegeneracyAERecorded :
    NSBroadTubeNondegenerateGradientExactAssumption

  pointwiseLowerBoundNeedsNonFlatNoCriticalManifold :
    NSBroadTubeNondegenerateGradientExactAssumption

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

canonicalNSBroadTubeNondegenerateGradientExactAssumptions :
  List NSBroadTubeNondegenerateGradientExactAssumption
canonicalNSBroadTubeNondegenerateGradientExactAssumptions =
  lambda2IsC1OnTube
  ∷ lambda2IsC2AlongFoliation
  ∷ strictGradientLowerBoundForNondegeneracy
  ∷ finiteTubularRadiusWitness
  ∷ regularLevelSetFoliationWitness
  ∷ boundedSecondFundamentalFormWitness
  ∷ admissibleBoundaryDataForMinimumPrinciple
  ∷ rellichFirstDerivativeFormula
  ∷ katoHessianLaplacianFormula
  ∷ simpleEigenvalueGapLowerBoundG12
  ∷ simpleEigenvalueGapLowerBoundG23
  ∷ h3SardCoareaEstimate
  ∷ coareaNondegeneracyAERecorded
  ∷ pointwiseLowerBoundNeedsNonFlatNoCriticalManifold
  ∷ []

canonicalNSBroadTubeNondegenerateGradientExactAssumptionLabels :
  List String
canonicalNSBroadTubeNondegenerateGradientExactAssumptionLabels =
  "lambda2 is C1 on the tube"
  ∷ "lambda2 is C2 along the foliation"
  ∷ "strict gradient lower bound for nondegeneracy"
  ∷ "finite tubular radius witness"
  ∷ "regular level-set foliation witness"
  ∷ "bounded second fundamental form witness"
  ∷ "admissible boundary data for the minimum principle"
  ∷ "rellich first derivative formula for differentiated gap identities"
  ∷ "kato hessian/laplacian formula recorded"
  ∷ "simple eigenvalue gap hypothesis: g12 >= delta1"
  ∷ "simple eigenvalue gap hypothesis: g23 >= delta3"
  ∷ "H3 plus Sard coarea estimate as geometric input"
  ∷ "coarea nondegeneracy recorded a.e. / measure-theoretically"
  ∷ "pointwise lower-bound blocker: non-flat and no-critical-manifold hypothesis required"
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

data NSBroadTubeNondegenerateGradientKernelStep : Set where
  differentiateLambda2AlongTubeFlow :
    NSBroadTubeNondegenerateGradientKernelStep

  reduceToTubeODEAndBoundaryData :
    NSBroadTubeNondegenerateGradientKernelStep

  applyMinimumPrincipleOnTubeSlice :
    NSBroadTubeNondegenerateGradientKernelStep

  propagateNondegeneracyThroughFoliation :
    NSBroadTubeNondegenerateGradientKernelStep

  recordRellichFirstDerivative :
    NSBroadTubeNondegenerateGradientKernelStep

  recordKatoHessianLaplacian :
    NSBroadTubeNondegenerateGradientKernelStep

  splitSimpleEigenvalueGaps :
    NSBroadTubeNondegenerateGradientKernelStep

  recordGapDenominatorDelta1 :
    NSBroadTubeNondegenerateGradientKernelStep

  recordGapDenominatorDelta3 :
    NSBroadTubeNondegenerateGradientKernelStep

  recordH3SardCoareaStep :
    NSBroadTubeNondegenerateGradientKernelStep

  distinguishCoareaModes :
    NSBroadTubeNondegenerateGradientKernelStep

  recordPointwiseLowerBoundBlocker :
    NSBroadTubeNondegenerateGradientKernelStep

  keepKernelConditionalUntilAssumptionsDisappear :
    NSBroadTubeNondegenerateGradientKernelStep

data NSBroadTubeNondegenerateGradientPromotionBlocker : Set where
  residualAnalyticAssumptions :
    NSBroadTubeNondegenerateGradientPromotionBlocker

  oDEMinPrincipleKernelStillConditional :
    NSBroadTubeNondegenerateGradientPromotionBlocker

  noUnconditionalLambda2GradientTheorem :
    NSBroadTubeNondegenerateGradientPromotionBlocker

  pointwiseLowerBoundBlocker :
    NSBroadTubeNondegenerateGradientPromotionBlocker

  noClayPromotion :
    NSBroadTubeNondegenerateGradientPromotionBlocker

canonicalNSBroadTubeNondegenerateGradientKernelSteps :
  List NSBroadTubeNondegenerateGradientKernelStep
canonicalNSBroadTubeNondegenerateGradientKernelSteps =
  differentiateLambda2AlongTubeFlow
  ∷ reduceToTubeODEAndBoundaryData
  ∷ applyMinimumPrincipleOnTubeSlice
  ∷ propagateNondegeneracyThroughFoliation
  ∷ recordRellichFirstDerivative
  ∷ recordKatoHessianLaplacian
  ∷ splitSimpleEigenvalueGaps
  ∷ recordGapDenominatorDelta1
  ∷ recordGapDenominatorDelta3
  ∷ recordH3SardCoareaStep
  ∷ distinguishCoareaModes
  ∷ recordPointwiseLowerBoundBlocker
  ∷ keepKernelConditionalUntilAssumptionsDisappear
  ∷ []

canonicalNSBroadTubeNondegenerateGradientPromotionBlockers :
  List NSBroadTubeNondegenerateGradientPromotionBlocker
canonicalNSBroadTubeNondegenerateGradientPromotionBlockers =
  residualAnalyticAssumptions
  ∷ oDEMinPrincipleKernelStillConditional
  ∷ noUnconditionalLambda2GradientTheorem
  ∷ pointwiseLowerBoundBlocker
  ∷ noClayPromotion
  ∷ []

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

canonicalNSBroadTubeNondegenerateGradientKernelStepLabels :
  List String
canonicalNSBroadTubeNondegenerateGradientKernelStepLabels =
  "differentiate lambda2 along tube flow"
  ∷ "reduce to tube ODE and boundary data"
  ∷ "apply minimum principle on tube slice"
  ∷ "propagate nondegeneracy through foliation"
  ∷ "record Rellich first-derivative identity"
  ∷ "record Kato hessian and Laplacian formulas"
  ∷ "split and track simple eigenvalue gaps"
  ∷ "close g12 denominator by g12 >= delta1"
  ∷ "close g23 denominator by g23 >= delta3"
  ∷ "insert H3 + Sard + coarea estimate step"
  ∷ "distinguish a.e. coarea lower bound from pointwise lower bound"
  ∷ "record blocker: pointwise lower bound needs non-flat/no-critical-manifold"
  ∷ "keep kernel conditional until assumptions disappear"
  ∷ []

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
  "Conditional broad-tube nondegenerate gradient socket: with exact C1/C2 lambda2 regularity, strict gradient lower bound, finite tubular radius, regular level-set foliation, bounded second fundamental form, and admissible minimum-principle boundary data, the ODE/min-principle kernel constructs the nondegenerate gradient socket only conditionally after recording Rellich and Kato first-derivative structures."

nsBroadTubeNondegenerateGradientBoundary : String
nsBroadTubeNondegenerateGradientBoundary =
  "no Clay promotion claimed; no unconditional lambda2-gradient theorem claimed; the receipt remains fail-closed until every analytic assumption disappears and the ODE/min-principle kernel is discharged"

nsBroadTubeNondegenerateGradientKernelSummary : String
nsBroadTubeNondegenerateGradientKernelSummary =
  "ODE/min-principle kernel: differentiate lambda2 along the tube flow, apply Rellich first-derivative expansion, insert Kato hessian/Laplacian formulas, split simple-eigenvalue gaps, close denominators with g12 >= delta1 and g23 >= delta3, apply H3 + Sard + coarea estimates, distinguish a.e. coarea nondegeneracy from pointwise lower bound, and propagate nondegeneracy through the foliation without promoting the global theorem."

nsBroadTubeNondegenerateGradientPromotionBlockerSummary : String
nsBroadTubeNondegenerateGradientPromotionBlockerSummary =
  "Promotion stays blocked by residual analytic assumptions, the conditional ODE/min-principle kernel, the missing unconditional lambda2-gradient theorem, the pointwise non-flat/no-critical-manifold requirement for coarea lower bounds, and the explicit no-Clay gate."

record NSBroadTubeNondegenerateGradientKernelReceipt : Set where
  field
    exactAssumptions :
      List NSBroadTubeNondegenerateGradientExactAssumption

    exactAssumptionsAreCanonical :
      exactAssumptions ≡
      canonicalNSBroadTubeNondegenerateGradientExactAssumptions

    exactAssumptionLabels :
      List String

    exactAssumptionLabelsAreCanonical :
      exactAssumptionLabels ≡
      canonicalNSBroadTubeNondegenerateGradientExactAssumptionLabels

    kernelSteps :
      List NSBroadTubeNondegenerateGradientKernelStep

    kernelStepsAreCanonical :
      kernelSteps ≡
      canonicalNSBroadTubeNondegenerateGradientKernelSteps

    kernelStepLabels :
      List String

    kernelStepLabelsAreCanonical :
      kernelStepLabels ≡
      canonicalNSBroadTubeNondegenerateGradientKernelStepLabels

    kernelSummary :
      String

    kernelSummaryIsCanonical :
      kernelSummary ≡ nsBroadTubeNondegenerateGradientKernelSummary

    kernelStillConditional :
      Bool

    kernelStillConditionalIsTrue :
      kernelStillConditional ≡ true

    promotionBlockers :
      List NSBroadTubeNondegenerateGradientPromotionBlocker

    promotionBlockersAreCanonical :
      promotionBlockers ≡
      canonicalNSBroadTubeNondegenerateGradientPromotionBlockers

    promotionBlockerSummary :
      String

    promotionBlockerSummaryIsCanonical :
      promotionBlockerSummary ≡
      nsBroadTubeNondegenerateGradientPromotionBlockerSummary

    coareaTheoremRecordedOnAEverywhere :
      Bool

    coareaTheoremRecordedOnAEverywhereIsTrue :
      coareaTheoremRecordedOnAEverywhere ≡ true

    pointwiseLowerBoundBlockerRecorded :
      Bool

    pointwiseLowerBoundBlockerRecordedIsTrue :
      pointwiseLowerBoundBlockerRecorded ≡ true

canonicalNSBroadTubeNondegenerateGradientKernelReceipt :
  NSBroadTubeNondegenerateGradientKernelReceipt
canonicalNSBroadTubeNondegenerateGradientKernelReceipt =
  record
    { exactAssumptions =
        canonicalNSBroadTubeNondegenerateGradientExactAssumptions
    ; exactAssumptionsAreCanonical =
        refl
    ; exactAssumptionLabels =
        canonicalNSBroadTubeNondegenerateGradientExactAssumptionLabels
    ; exactAssumptionLabelsAreCanonical =
        refl
    ; kernelSteps =
        canonicalNSBroadTubeNondegenerateGradientKernelSteps
    ; kernelStepsAreCanonical =
        refl
    ; kernelStepLabels =
        canonicalNSBroadTubeNondegenerateGradientKernelStepLabels
    ; kernelStepLabelsAreCanonical =
        refl
    ; kernelSummary =
        nsBroadTubeNondegenerateGradientKernelSummary
    ; kernelSummaryIsCanonical =
        refl
    ; kernelStillConditional =
        true
    ; kernelStillConditionalIsTrue =
        refl
    ; promotionBlockers =
        canonicalNSBroadTubeNondegenerateGradientPromotionBlockers
    ; promotionBlockersAreCanonical =
        refl
    ; promotionBlockerSummary =
        nsBroadTubeNondegenerateGradientPromotionBlockerSummary
    ; promotionBlockerSummaryIsCanonical =
        refl
    ; coareaTheoremRecordedOnAEverywhere =
        true
    ; coareaTheoremRecordedOnAEverywhereIsTrue =
        refl
    ; pointwiseLowerBoundBlockerRecorded =
        true
    ; pointwiseLowerBoundBlockerRecordedIsTrue =
        refl
    }

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
    "Record a conditional broad-tube nondegenerate gradient socket with explicit analytic steps: Rellich first-derivative expansion, Kato hessian/laplacian formulas, and explicit eigen-gap control."
    "Construct the nondegenerate gradient socket under smooth lambda2 field, gradient lower bound on tube, bounded second fundamental form, finite tubular radius, and level set foliation, while also recording exact C1/C2 lambda2 regularity, explicit Rellich/Kato formulas, gap lower bounds g12 >= delta1 and g23 >= delta3, admissible boundary data, and H3/Sard/coarea geometric control."
    "Dependencies are the hypothesis record, exact assumption record (expanded with Rellich/Kato/gap/coarea data), tube geometry socket, foliation socket, ODE/min-principle kernel record, and conditional gradient socket."
    "Hypothesis list is fixed as smooth-lambda2-field, gradient-lower-bound-on-tube, bounded-second-fundamental-form, finite-tubular-radius, and level-set-foliation; exact assumptions add lambda2 C1/C2 regularity, strict nondegeneracy lower bound, finite radius witness, regular foliation witness, bounded curvature witness, admissible minimum-principle boundary data, Rellich first-derivative formula, Kato hessian/laplacian formula, gap hypotheses g12 >= delta1 and g23 >= delta3, H3/Sard/coarea estimate, a.e. coarea nondegeneracy, and the pointwise lower-bound blocker."
    "Linking path: hypotheses -> exact assumptions -> ODE/min-principle kernel -> explicit Rellich/Kato/spectrum coarea steps -> nondegenerate gradient socket constructed conditionally."
    "No unconditional lambda2-gradient theorem is established at this node."
    "Clay promotion is explicitly false and the kernel remains conditional."
    "Keep the receipt fail-closed until the exact analytic assumptions disappear and the pointwise blocker is discharged."

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

    exactAssumptions :
      List NSBroadTubeNondegenerateGradientExactAssumption

    exactAssumptionsAreCanonical :
      exactAssumptions ≡
      canonicalNSBroadTubeNondegenerateGradientExactAssumptions

    exactAssumptionLabels :
      List String

    exactAssumptionLabelsAreCanonical :
      exactAssumptionLabels ≡
      canonicalNSBroadTubeNondegenerateGradientExactAssumptionLabels

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

    kernelReceipt :
      NSBroadTubeNondegenerateGradientKernelReceipt

    kernelReceiptIsCanonical :
      kernelReceipt ≡
      canonicalNSBroadTubeNondegenerateGradientKernelReceipt

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

    allAnalyticAssumptionsStillPresent :
      Bool

    allAnalyticAssumptionsStillPresentIsTrue :
      allAnalyticAssumptionsStillPresent ≡ true

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

    promotionBlockers :
      List NSBroadTubeNondegenerateGradientPromotionBlocker

    promotionBlockersAreCanonical :
      promotionBlockers ≡
      canonicalNSBroadTubeNondegenerateGradientPromotionBlockers

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡
      "no Clay promotion claimed"
      ∷ "no unconditional lambda2-gradient theorem claimed"
      ∷ "conditional socket only"
      ∷ "coarea nondegeneracy currently only a.e. recorded"
      ∷ "pointwise lower bound blocked by non-flat/no-critical-manifold condition"
      ∷ "exact analytic assumptions still present"
      ∷ []

    coareaAEMeasureTheoreticRecorded :
      Bool

    coareaAEMeasureTheoreticRecordedIsTrue :
      coareaAEMeasureTheoreticRecorded ≡ true

    pointwiseLowerBoundBlockerRecorded :
      Bool

    pointwiseLowerBoundBlockerRecordedIsTrue :
      pointwiseLowerBoundBlockerRecorded ≡ true

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
    ; exactAssumptions =
        canonicalNSBroadTubeNondegenerateGradientExactAssumptions
    ; exactAssumptionsAreCanonical =
        refl
    ; exactAssumptionLabels =
        canonicalNSBroadTubeNondegenerateGradientExactAssumptionLabels
    ; exactAssumptionLabelsAreCanonical =
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
    ; kernelReceipt =
        canonicalNSBroadTubeNondegenerateGradientKernelReceipt
    ; kernelReceiptIsCanonical =
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
    ; allAnalyticAssumptionsStillPresent =
        true
    ; allAnalyticAssumptionsStillPresentIsTrue =
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
    ; promotionBlockers =
        canonicalNSBroadTubeNondegenerateGradientPromotionBlockers
    ; promotionBlockersAreCanonical =
        refl
    ; receiptBoundary =
        "no Clay promotion claimed"
        ∷ "no unconditional lambda2-gradient theorem claimed"
        ∷ "conditional socket only"
        ∷ "coarea nondegeneracy currently only a.e. recorded"
        ∷ "pointwise lower bound blocked by non-flat/no-critical-manifold condition"
        ∷ "exact analytic assumptions still present"
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    ; coareaAEMeasureTheoreticRecorded =
        true
    ; coareaAEMeasureTheoreticRecordedIsTrue =
        refl
    ; pointwiseLowerBoundBlockerRecorded =
        true
    ; pointwiseLowerBoundBlockerRecordedIsTrue =
        refl
    ; orcslpgf =
        canonicalNSBroadTubeNondegenerateGradientORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    }
