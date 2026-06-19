module DASHI.Physics.Closure.LocalConcentrationPigeonConcentrationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only receipt for component-local concentration and the
-- pigeon_concentration proof-package shape.
--
-- The recorded surfaces are:
--   1. Calc 11 Leray tail plus ||f||_{L^{3,infty}} <= ||f||_{L^3};
--   2. local ball concentration;
--   3. finite component count h_fin with N_max empirically 20630;
--   4. pigeon bound K / N_max^(1/3);
--   5. no promotion;
--   6. package variables;
--   7. blockers.
--
-- No theorem promotion and no Clay promotion are claimed here.

data LocalConcentrationReceiptStatus : Set where
  candidateOnlySurfaceRecorded :
    LocalConcentrationReceiptStatus

data LocalConcentrationPackageShape : Set where
  localConcentrationShape :
    LocalConcentrationPackageShape

  pigeonConcentrationShape :
    LocalConcentrationPackageShape

canonicalLocalConcentrationPackageShapes :
  List LocalConcentrationPackageShape
canonicalLocalConcentrationPackageShapes =
  localConcentrationShape
  ∷ pigeonConcentrationShape
  ∷ []

data LocalConcentrationStage : Set where
  calc11LerayTailAndWeakL3Control :
    LocalConcentrationStage

  localBallConcentrationRecorded :
    LocalConcentrationStage

  finiteComponentCountHFinRecorded :
    LocalConcentrationStage

  pigeonBoundKOverNMaxOneThird :
    LocalConcentrationStage

  noPromotionClaimed :
    LocalConcentrationStage

  packageVariablesRecorded :
    LocalConcentrationStage

  blockerSetRecorded :
    LocalConcentrationStage

canonicalLocalConcentrationStages :
  List LocalConcentrationStage
canonicalLocalConcentrationStages =
  calc11LerayTailAndWeakL3Control
  ∷ localBallConcentrationRecorded
  ∷ finiteComponentCountHFinRecorded
  ∷ pigeonBoundKOverNMaxOneThird
  ∷ noPromotionClaimed
  ∷ packageVariablesRecorded
  ∷ blockerSetRecorded
  ∷ []

canonicalLocalConcentrationVariables :
  List String
canonicalLocalConcentrationVariables =
  "Calc 11"
  ∷ "Leray tail"
  ∷ "||f||_{L^{3,infty}} <= ||f||_{L^3}"
  ∷ "local ball concentration"
  ∷ "h_fin"
  ∷ "N_max"
  ∷ "N_max = 20630"
  ∷ "K"
  ∷ "K / N_max^(1/3)"
  ∷ "pigeon_concentration"
  ∷ []

data LocalConcentrationBlocker : Set where
  missingCalc11TailUpgrade :
    LocalConcentrationBlocker

  missingLocalBallConcentration :
    LocalConcentrationBlocker

  missingHFinHypothesisRecording :
    LocalConcentrationBlocker

  missingPigeonPackingInequality :
    LocalConcentrationBlocker

  missingVariableInstantiation :
    LocalConcentrationBlocker

  theoremPromotionForbidden :
    LocalConcentrationBlocker

  clayPromotionForbidden :
    LocalConcentrationBlocker

canonicalLocalConcentrationBlockers :
  List LocalConcentrationBlocker
canonicalLocalConcentrationBlockers =
  missingCalc11TailUpgrade
  ∷ missingLocalBallConcentration
  ∷ missingHFinHypothesisRecording
  ∷ missingPigeonPackingInequality
  ∷ missingVariableInstantiation
  ∷ theoremPromotionForbidden
  ∷ clayPromotionForbidden
  ∷ []

canonicalLocalConcentrationReceiptBoundary :
  List String
canonicalLocalConcentrationReceiptBoundary =
  "This receipt is candidate-only and records package shape only"
  ∷ "Calc 11 records Leray tail control together with ||f||_{L^{3,infty}} <= ||f||_{L^3}"
  ∷ "local ball concentration is recorded as a surface"
  ∷ "the finite component count h_fin is recorded with empirical N_max = 20630 and analytic hypothesis only"
  ∷ "the pigeon_concentration bound K / N_max^(1/3) is recorded as a surface, not a promoted theorem"
  ∷ "theorem promotion remains false"
  ∷ "Clay promotion remains false"
  ∷ []

data LocalConcentrationPromotion : Set where

localConcentrationPromotionImpossibleHere :
  LocalConcentrationPromotion →
  ⊥
localConcentrationPromotionImpossibleHere ()

localConcentrationPackageSummary : String
localConcentrationPackageSummary =
  "Candidate-only component-local concentration package after Calc 11: Leray tail control and ||f||_{L^{3,infty}} <= ||f||_{L^3} are recorded, local ball concentration is recorded, h_fin carries the empirical N_max = 20630 hypothesis, the pigeon_concentration bound K / N_max^(1/3) is recorded, and theorem/Clay promotion remains false."

record LocalConcentrationPigeonConcentrationReceipt : Setω where
  field
    status :
      LocalConcentrationReceiptStatus

    statusIsCanonical :
      status ≡ candidateOnlySurfaceRecorded

    proofPackageShapes :
      List LocalConcentrationPackageShape

    proofPackageShapesAreCanonical :
      proofPackageShapes ≡ canonicalLocalConcentrationPackageShapes

    packageStages :
      List LocalConcentrationStage

    packageStagesAreCanonical :
      packageStages ≡ canonicalLocalConcentrationStages

    variables :
      List String

    variablesAreCanonical :
      variables ≡ canonicalLocalConcentrationVariables

    calc11RouteSummary :
      String

    calc11RouteSummaryIsCanonical :
      calc11RouteSummary ≡ localConcentrationPackageSummary

    lerayTailSurface :
      String

    lerayTailSurfaceIsCanonical :
      lerayTailSurface ≡ "Leray tail"

    weakL3Surface :
      String

    weakL3SurfaceIsCanonical :
      weakL3Surface ≡ "||f||_{L^{3,infty}} <= ||f||_{L^3}"

    localL3Surface :
      String

    localL3SurfaceIsCanonical :
      localL3Surface ≡ "local ball concentration"

    localBallConcentrationSurface :
      String

    localBallConcentrationSurfaceIsCanonical :
      localBallConcentrationSurface ≡ "local ball concentration"

    tailControlSurface :
      String

    tailControlSurfaceIsCanonical :
      tailControlSurface ≡ "Leray tail"

    componentCountName :
      String

    componentCountNameIsCanonical :
      componentCountName ≡ "h_fin"

    componentCountSymbol :
      String

    componentCountSymbolIsCanonical :
      componentCountSymbol ≡ "N_max"

    empiricalNMax :
      Nat

    empiricalNMaxIsCanonical :
      empiricalNMax ≡ 20630

    componentCountAnalyticHypothesis :
      Bool

    componentCountAnalyticHypothesisIsTrue :
      componentCountAnalyticHypothesis ≡ true

    pigeonBoundFormula :
      String

    pigeonBoundFormulaIsCanonical :
      pigeonBoundFormula ≡ "K / N_max^(1/3)"

    pigeonConcentrationAlias :
      String

    pigeonConcentrationAliasIsCanonical :
      pigeonConcentrationAlias ≡ "pigeon_concentration"

    theoremPromoted :
      Bool

    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    blockers :
      List LocalConcentrationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalLocalConcentrationBlockers

    promotionFlags :
      List LocalConcentrationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    summary :
      String

    summaryIsCanonical :
      summary ≡ localConcentrationPackageSummary

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalLocalConcentrationReceiptBoundary

open LocalConcentrationPigeonConcentrationReceipt public

canonicalLocalConcentrationPigeonConcentrationReceipt :
  LocalConcentrationPigeonConcentrationReceipt
canonicalLocalConcentrationPigeonConcentrationReceipt =
  record
    { status =
        candidateOnlySurfaceRecorded
    ; statusIsCanonical =
        refl
    ; proofPackageShapes =
        canonicalLocalConcentrationPackageShapes
    ; proofPackageShapesAreCanonical =
        refl
    ; packageStages =
        canonicalLocalConcentrationStages
    ; packageStagesAreCanonical =
        refl
    ; variables =
        canonicalLocalConcentrationVariables
    ; variablesAreCanonical =
        refl
    ; calc11RouteSummary =
        localConcentrationPackageSummary
    ; calc11RouteSummaryIsCanonical =
        refl
    ; lerayTailSurface =
        "Leray tail"
    ; lerayTailSurfaceIsCanonical =
        refl
    ; weakL3Surface =
        "||f||_{L^{3,infty}} <= ||f||_{L^3}"
    ; weakL3SurfaceIsCanonical =
        refl
    ; localL3Surface =
        "local ball concentration"
    ; localL3SurfaceIsCanonical =
        refl
    ; localBallConcentrationSurface =
        "local ball concentration"
    ; localBallConcentrationSurfaceIsCanonical =
        refl
    ; tailControlSurface =
        "Leray tail"
    ; tailControlSurfaceIsCanonical =
        refl
    ; componentCountName =
        "h_fin"
    ; componentCountNameIsCanonical =
        refl
    ; componentCountSymbol =
        "N_max"
    ; componentCountSymbolIsCanonical =
        refl
    ; empiricalNMax =
        20630
    ; empiricalNMaxIsCanonical =
        refl
    ; componentCountAnalyticHypothesis =
        true
    ; componentCountAnalyticHypothesisIsTrue =
        refl
    ; pigeonBoundFormula =
        "K / N_max^(1/3)"
    ; pigeonBoundFormulaIsCanonical =
        refl
    ; pigeonConcentrationAlias =
        "pigeon_concentration"
    ; pigeonConcentrationAliasIsCanonical =
        refl
    ; theoremPromoted =
        false
    ; theoremPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; blockers =
        canonicalLocalConcentrationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; summary =
        localConcentrationPackageSummary
    ; summaryIsCanonical =
        refl
    ; receiptBoundary =
        canonicalLocalConcentrationReceiptBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

localConcentrationTheoremPromotedIsFalse :
  theoremPromoted canonicalLocalConcentrationPigeonConcentrationReceipt
  ≡
  false
localConcentrationTheoremPromotedIsFalse =
  refl

localConcentrationClayPromotedIsFalse :
  clayPromoted canonicalLocalConcentrationPigeonConcentrationReceipt
  ≡
  false
localConcentrationClayPromotedIsFalse =
  refl
