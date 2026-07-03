module DASHI.Physics.Closure.NSTriadKNGate2ANearExtremizerDefectEstimates where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import DASHI.Physics.Closure.DefectBudgetBase
  using (DefectBudget)
open import DASHI.Physics.Closure.NearExtremizerDefectEstimateBase
  using ( NearExtremizerDefectEstimateModel
        ; mkNearExtremizerDefectEstimateModel
        )
open import DASHI.Physics.Closure.NSTriadKNGate2ASeamBudgetArithmetic
  using ( canonicalNearExtremizerDefectEstimateModel )

------------------------------------------------------------------------
-- Gate 2-A near-extremizer defect estimates.
--
-- This module now separates three layers explicitly:
--
--   1. seam-local analytic hypotheses on the lift defect ΔJ,
--   2. derived cone-uniform cross/pure/combined inequalities,
--   3. the still-open claim that the actual NS seam inhabits those
--      hypotheses on the true carrier.
--
-- The main analytic shape is:
--
--   cross-term    ≤ linear-envelope    ≤ η-cross
--   pure-term     ≤ quadratic-envelope ≤ η-pure
--   combined-term ≤ cross-term + pure-term
--
-- so the combined defect budget follows by transitivity and Lemma A.

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

canonicalLinearMechanismText : String
canonicalLinearMechanismText =
  "NS-seam analytic route for the cross term: first control a one-power lift-defect envelope for DeltaJ against the normalized seam energy, then dominate that envelope by eta_cross."

canonicalQuadraticMechanismText : String
canonicalQuadraticMechanismText =
  "NS-seam analytic route for the pure term: first control a two-power lift-defect envelope for DeltaJ against the normalized seam energy, then dominate that envelope by eta_pure."

canonicalCombinedMechanismText : String
canonicalCombinedMechanismText =
  "Combined route: use the triangle/splitting inequality for the lifted quadratic form, then feed the derived cross and pure estimates into the additive defect ledger."

------------------------------------------------------------------------
-- Analytic hypothesis package for the ΔJ seam estimates.
--
-- This is the first genuinely proof-shaped surface in the Gate 2-A
-- defect lane: it does not assume the final cross/pure inequalities
-- directly, but factors them through explicit one-power and two-power
-- envelopes for the lift defect.

record NSTriadKNGate2ASeamLiftDefectHypotheses : Setω where
  constructor mkNSTriadKNGate2ASeamLiftDefectHypotheses
  field
    defectBudget : DefectBudget

  open DefectBudget defectBudget public

  field
    cross-term pure-term combined-term : N
    linear-envelope quadratic-envelope : N

    combined≤splitWitness :
      combined-term ≤ (cross-term + pure-term)

    cross≤linearEnvelopeWitness :
      cross-term ≤ linear-envelope

    linearEnvelope≤η-crossWitness :
      linear-envelope ≤ η-cross

    pure≤quadraticEnvelopeWitness :
      pure-term ≤ quadratic-envelope

    quadraticEnvelope≤η-pureWitness :
      quadratic-envelope ≤ η-pure

  cross≤η-crossWitness : cross-term ≤ η-cross
  cross≤η-crossWitness =
    trans≤
      cross-term
      linear-envelope
      η-cross
      cross≤linearEnvelopeWitness
      linearEnvelope≤η-crossWitness

  pure≤η-pureWitness : pure-term ≤ η-pure
  pure≤η-pureWitness =
    trans≤
      pure-term
      quadratic-envelope
      η-pure
      pure≤quadraticEnvelopeWitness
      quadraticEnvelope≤η-pureWitness

open NSTriadKNGate2ASeamLiftDefectHypotheses public

mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses :
  NSTriadKNGate2ASeamLiftDefectHypotheses →
  NearExtremizerDefectEstimateModel
mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses h =
  mkNearExtremizerDefectEstimateModel
    (defectBudget h)
    (cross-term h)
    (pure-term h)
    (combined-term h)
    (combined≤splitWitness h)
    (cross≤η-crossWitness h)
    (pure≤η-pureWitness h)

mkCrossEstimateFromSeamLiftHypotheses :
  (h : NSTriadKNGate2ASeamLiftDefectHypotheses) →
  NearExtremizerDefectEstimateModel.cross≤η-cross
    (mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses h)
mkCrossEstimateFromSeamLiftHypotheses =
  cross≤η-crossWitness

mkPureEstimateFromSeamLiftHypotheses :
  (h : NSTriadKNGate2ASeamLiftDefectHypotheses) →
  NearExtremizerDefectEstimateModel.pure≤η-pure
    (mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses h)
mkPureEstimateFromSeamLiftHypotheses =
  pure≤η-pureWitness

mkCombinedEstimateFromSeamLiftHypotheses :
  (h : NSTriadKNGate2ASeamLiftDefectHypotheses) →
  NearExtremizerDefectEstimateModel.combined≤η-defect
    (mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses h)
mkCombinedEstimateFromSeamLiftHypotheses h =
  NearExtremizerDefectEstimateModel.combined≤η-defect
    (mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses h)

------------------------------------------------------------------------
-- Theorem-facing Gate 2-A package.
--
-- This consumes the seam-lift hypothesis package, exposes the derived
-- cone-uniform inequalities, and keeps the actual NS-seam realization
-- fail-closed until an inhabitant on the true carrier is constructed.

record NSTriadKNGate2ANearExtremizerDefectEstimates : Setω where
  constructor mkNSTriadKNGate2ANearExtremizerDefectEstimates
  field
    seamLiftDefectHypotheses :
      NSTriadKNGate2ASeamLiftDefectHypotheses

    defectEstimateModel : NearExtremizerDefectEstimateModel
    defectEstimateModelIsDerived :
      defectEstimateModel
        ≡ mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses
            seamLiftDefectHypotheses

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

    linearMechanismText : String
    linearMechanismTextIsCanonical :
      linearMechanismText ≡ canonicalLinearMechanismText

    quadraticMechanismText : String
    quadraticMechanismTextIsCanonical :
      quadraticMechanismText ≡ canonicalQuadraticMechanismText

    combinedMechanismText : String
    combinedMechanismTextIsCanonical :
      combinedMechanismText ≡ canonicalCombinedMechanismText

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

    crossEstimateAbstractModelProved : Bool
    crossEstimateAbstractModelProvedIsTrue :
      crossEstimateAbstractModelProved ≡ true

    pureEstimateAbstractModelProved : Bool
    pureEstimateAbstractModelProvedIsTrue :
      pureEstimateAbstractModelProved ≡ true

    combinedEstimateAbstractModelProved : Bool
    combinedEstimateAbstractModelProvedIsTrue :
      combinedEstimateAbstractModelProved ≡ true

    crossEstimateProved : Bool
    crossEstimateProvedIsFalse :
      crossEstimateProved ≡ false

    pureEstimateProved : Bool
    pureEstimateProvedIsFalse :
      pureEstimateProved ≡ false

    combinedEstimateProved : Bool
    combinedEstimateProvedIsFalse :
      combinedEstimateProved ≡ false

    fullNSPromoted : Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted : Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

open NSTriadKNGate2ANearExtremizerDefectEstimates public

open NearExtremizerDefectEstimateModel
  canonicalNearExtremizerDefectEstimateModel

canonicalSeamLiftDefectHypotheses :
  NSTriadKNGate2ASeamLiftDefectHypotheses
canonicalSeamLiftDefectHypotheses =
  mkNSTriadKNGate2ASeamLiftDefectHypotheses
    (NearExtremizerDefectEstimateModel.defectBudget
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.cross-term
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.pure-term
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.combined-term
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.η-cross
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.η-pure
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.combined≤split
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.cross≤η-cross
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.refl≤
      canonicalNearExtremizerDefectEstimateModel
      (NearExtremizerDefectEstimateModel.η-cross
        canonicalNearExtremizerDefectEstimateModel))
    (NearExtremizerDefectEstimateModel.pure≤η-pure
      canonicalNearExtremizerDefectEstimateModel)
    (NearExtremizerDefectEstimateModel.refl≤
      canonicalNearExtremizerDefectEstimateModel
      (NearExtremizerDefectEstimateModel.η-pure
        canonicalNearExtremizerDefectEstimateModel))

canonicalNSTriadKNGate2ANearExtremizerDefectEstimates :
  NSTriadKNGate2ANearExtremizerDefectEstimates
canonicalNSTriadKNGate2ANearExtremizerDefectEstimates =
  mkNSTriadKNGate2ANearExtremizerDefectEstimates
    canonicalSeamLiftDefectHypotheses
    (mkNearExtremizerDefectEstimateModelFromSeamLiftHypotheses
      canonicalSeamLiftDefectHypotheses)
    refl
    (mkCrossEstimateFromSeamLiftHypotheses
      canonicalSeamLiftDefectHypotheses)
    (mkPureEstimateFromSeamLiftHypotheses
      canonicalSeamLiftDefectHypotheses)
    (mkCombinedEstimateFromSeamLiftHypotheses
      canonicalSeamLiftDefectHypotheses)
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
    canonicalLinearMechanismText
    refl
    canonicalQuadraticMechanismText
    refl
    canonicalCombinedMechanismText
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
    false
    refl
    false
    refl
    false
    refl
