module DASHI.Physics.Closure.LocalConcentrationPigeonConcentrationReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only receipt for component-local concentration and the
-- pigeon_concentration proof-package shape.
--
-- The recorded surfaces are:
--   1. weak-L3 to local L3 with tail control;
--   2. finite component count N_max;
--   3. pigeon bound K / N_max^(1/3);
--   4. package variables;
--   5. blockers.
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
  weakL3ToLocalL3WithTailControl :
    LocalConcentrationStage

  finiteComponentCountNMax :
    LocalConcentrationStage

  pigeonBoundKOverNMaxOneThird :
    LocalConcentrationStage

  packageVariablesRecorded :
    LocalConcentrationStage

  blockerSetRecorded :
    LocalConcentrationStage

canonicalLocalConcentrationStages :
  List LocalConcentrationStage
canonicalLocalConcentrationStages =
  weakL3ToLocalL3WithTailControl
  ∷ finiteComponentCountNMax
  ∷ pigeonBoundKOverNMaxOneThird
  ∷ packageVariablesRecorded
  ∷ blockerSetRecorded
  ∷ []

canonicalLocalConcentrationVariables :
  List String
canonicalLocalConcentrationVariables =
  "weak-L3"
  ∷ "local L3"
  ∷ "tail control"
  ∷ "N_max"
  ∷ "K"
  ∷ "K / N_max^(1/3)"
  ∷ "pigeon_concentration"
  ∷ []

data LocalConcentrationBlocker : Set where
  missingTailControlUpgrade :
    LocalConcentrationBlocker

  missingFiniteComponentDischarge :
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
  missingTailControlUpgrade
  ∷ missingFiniteComponentDischarge
  ∷ missingPigeonPackingInequality
  ∷ missingVariableInstantiation
  ∷ theoremPromotionForbidden
  ∷ clayPromotionForbidden
  ∷ []

canonicalLocalConcentrationReceiptBoundary :
  List String
canonicalLocalConcentrationReceiptBoundary =
  "This receipt is candidate-only and records package shape only"
  ∷ "weak-L3 to local L3 is recorded with tail control"
  ∷ "the finite component count N_max is recorded as a surface, not a promoted theorem"
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
  "Candidate-only component-local concentration package: weak-L3 is routed to local L3 with tail control, the finite component count N_max is recorded, the pigeon_concentration bound K / N_max^(1/3) is recorded, and theorem/Clay promotion remains false."

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

    weakL3Surface :
      String

    weakL3SurfaceIsCanonical :
      weakL3Surface ≡ "weak-L3"

    localL3Surface :
      String

    localL3SurfaceIsCanonical :
      localL3Surface ≡ "local L3"

    tailControlSurface :
      String

    tailControlSurfaceIsCanonical :
      tailControlSurface ≡ "tail control"

    componentCountName :
      String

    componentCountNameIsCanonical :
      componentCountName ≡ "N_max"

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
    ; weakL3Surface =
        "weak-L3"
    ; weakL3SurfaceIsCanonical =
        refl
    ; localL3Surface =
        "local L3"
    ; localL3SurfaceIsCanonical =
        refl
    ; tailControlSurface =
        "tail control"
    ; tailControlSurfaceIsCanonical =
        refl
    ; componentCountName =
        "N_max"
    ; componentCountNameIsCanonical =
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
