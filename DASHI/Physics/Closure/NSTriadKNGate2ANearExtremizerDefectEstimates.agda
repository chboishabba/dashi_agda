module DASHI.Physics.Closure.NSTriadKNGate2ANearExtremizerDefectEstimates where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.NearExtremizerDefectEstimateBase
  using (NearExtremizerDefectEstimateModel)
open import DASHI.Physics.Closure.NSTriadKNGate2ASeamBudgetArithmetic
  using (canonicalNearExtremizerDefectEstimateModel)

------------------------------------------------------------------------
-- Gate 2-A near-extremizer defect estimates.
--
-- This module upgrades the symbolic eta_cross / eta_pure / eta_defect
-- placeholders into explicit cone-uniform inequalities on E_N(epsilon).
-- The point is to state the first uniform estimate package that can later
-- feed actual proofs of the cone-restricted defect ledger.

data DefectEstimateStatus : Set where
  crossEstimateStated :
    DefectEstimateStatus
  pureEstimateStated :
    DefectEstimateStatus
  combinedEstimateStated :
    DefectEstimateStatus
  coneUniformityTargetStated :
    DefectEstimateStatus
  quarterMarginCompatibilityStated :
    DefectEstimateStatus
  noNSOrClayPromotion :
    DefectEstimateStatus

canonicalStatuses : List DefectEstimateStatus
canonicalStatuses =
  crossEstimateStated
  ∷ pureEstimateStated
  ∷ combinedEstimateStated
  ∷ coneUniformityTargetStated
  ∷ quarterMarginCompatibilityStated
  ∷ noNSOrClayPromotion
  ∷ []

data DefectEstimateLine : Set where
  crossConeUniformBound :
    DefectEstimateLine
  pureConeUniformBound :
    DefectEstimateLine
  combinedConeUniformBound :
    DefectEstimateLine
  subcriticalMarginCompatibility :
    DefectEstimateLine

canonicalLines : List DefectEstimateLine
canonicalLines =
  crossConeUniformBound
  ∷ pureConeUniformBound
  ∷ combinedConeUniformBound
  ∷ subcriticalMarginCompatibility
  ∷ []

canonicalCrossEstimateText : String
canonicalCrossEstimateText =
  "Assert first cone-uniform cross estimate: for all x in E_N(epsilon), | 2 <DeltaJ x, L_neg J_abs x> | <= eta_cross * <J_abs x, L_abs J_abs x>, where eta_cross is independent of x and N within the transport regime."

canonicalPureEstimateText : String
canonicalPureEstimateText =
  "Assert first cone-uniform pure estimate: for all x in E_N(epsilon), | <DeltaJ x, L_neg DeltaJ x> | <= eta_pure * <J_abs x, L_abs J_abs x>, where eta_pure is independent of x and N within the transport regime."

canonicalCombinedEstimateText : String
canonicalCombinedEstimateText =
  "Assert combined cone-uniform defect estimate: eta_cross + eta_pure <= eta_defect and hence for all x in E_N(epsilon), | 2 <DeltaJ x, L_neg J_abs x> + <DeltaJ x, L_neg DeltaJ x> | <= eta_defect * <J_abs x, L_abs J_abs x>."

canonicalUniformityText : String
canonicalUniformityText =
  "Uniformity target: the defect constants eta_cross, eta_pure, eta_defect are allowed to depend on epsilon or the chosen near-extremizer regime, but not on the specific direction x and not on the sampled shell parameter N once inside that regime."

canonicalMarginCompatibilityText : String
canonicalMarginCompatibilityText =
  "Margin-compatibility target: principal directional transport plus eta_defect must stay below the conservative quarter threshold, so the defect package is useful only if it preserves theta_* <= 1/4 and therefore theta_* < 1."

open NearExtremizerDefectEstimateModel
  canonicalNearExtremizerDefectEstimateModel

record NSTriadKNGate2ANearExtremizerDefectEstimates : Setω where
  constructor mkNSTriadKNGate2ANearExtremizerDefectEstimates
  field
    defectEstimateModel : NearExtremizerDefectEstimateModel
    defectEstimateModelIsCanonical :
      defectEstimateModel ≡ canonicalNearExtremizerDefectEstimateModel

    crossEstimate :
      NearExtremizerDefectEstimateModel.cross≤η-cross
        defectEstimateModel

    pureEstimate :
      NearExtremizerDefectEstimateModel.pure≤η-pure
        defectEstimateModel

    combinedEstimate :
      NearExtremizerDefectEstimateModel.combined≤η-defect
        defectEstimateModel

    statuses : List DefectEstimateStatus
    statusesAreCanonical :
      statuses ≡ canonicalStatuses

    lines : List DefectEstimateLine
    linesAreCanonical :
      lines ≡ canonicalLines

    crossEstimateText : String
    crossEstimateTextIsCanonical :
      crossEstimateText ≡ canonicalCrossEstimateText

    pureEstimateText : String
    pureEstimateTextIsCanonical :
      pureEstimateText ≡ canonicalPureEstimateText

    combinedEstimateText : String
    combinedEstimateTextIsCanonical :
      combinedEstimateText ≡ canonicalCombinedEstimateText

    uniformityText : String
    uniformityTextIsCanonical :
      uniformityText ≡ canonicalUniformityText

    marginCompatibilityText : String
    marginCompatibilityTextIsCanonical :
      marginCompatibilityText ≡ canonicalMarginCompatibilityText

    crossEstimateInstalled : Bool
    crossEstimateInstalledIsTrue :
      crossEstimateInstalled ≡ true

    pureEstimateInstalled : Bool
    pureEstimateInstalledIsTrue :
      pureEstimateInstalled ≡ true

    combinedEstimateInstalled : Bool
    combinedEstimateInstalledIsTrue :
      combinedEstimateInstalled ≡ true

    coneUniformityInstalled : Bool
    coneUniformityInstalledIsTrue :
      coneUniformityInstalled ≡ true

    marginCompatibilityInstalled : Bool
    marginCompatibilityInstalledIsTrue :
      marginCompatibilityInstalled ≡ true

    crossEstimateProved : Bool
    crossEstimateProvedIsTrue :
      crossEstimateProved ≡ true

    pureEstimateProved : Bool
    pureEstimateProvedIsTrue :
      pureEstimateProved ≡ true

    combinedEstimateProved : Bool
    combinedEstimateProvedIsTrue :
      combinedEstimateProved ≡ true

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGate2ANearExtremizerDefectEstimates public

canonicalNSTriadKNGate2ANearExtremizerDefectEstimates :
  NSTriadKNGate2ANearExtremizerDefectEstimates
canonicalNSTriadKNGate2ANearExtremizerDefectEstimates =
  mkNSTriadKNGate2ANearExtremizerDefectEstimates
    canonicalNearExtremizerDefectEstimateModel
    refl
    (NearExtremizerDefectEstimateModel.cross≤η-cross
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.pure≤η-pure
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.combined≤η-defect
      canonicalNearExtremizerDefectEstimateModel)
    canonicalStatuses
    refl
    canonicalLines
    refl
    canonicalCrossEstimateText
    refl
    canonicalPureEstimateText
    refl
    canonicalCombinedEstimateText
    refl
    canonicalUniformityText
    refl
    canonicalMarginCompatibilityText
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
