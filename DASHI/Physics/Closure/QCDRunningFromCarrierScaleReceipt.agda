module DASHI.Physics.Closure.QCDRunningFromCarrierScaleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierRGTrajectoryYMReceipt as RG
import DASHI.Physics.Closure.CarrierScaleFromHeegnerReceipt as Scale

data QCDRunningFromCarrierScaleStatus : Set where
  qcdRunningAuditedCarrierScaleNotEnough :
    QCDRunningFromCarrierScaleStatus

data QCDRunningRequirement : Set where
  independentGaugeCoupling :
    QCDRunningRequirement

  betaFunctionCoefficients :
    QCDRunningRequirement

  lambdaQCDAnchor :
    QCDRunningRequirement

  thresholdMatching :
    QCDRunningRequirement

canonicalQCDRunningRequirements :
  List QCDRunningRequirement
canonicalQCDRunningRequirements =
  independentGaugeCoupling
  ∷ betaFunctionCoefficients
  ∷ lambdaQCDAnchor
  ∷ thresholdMatching
  ∷ []

data QCDRunningPromotion : Set where

qcdRunningPromotionImpossibleHere :
  QCDRunningPromotion →
  ⊥
qcdRunningPromotionImpossibleHere ()

oneLoopQCDRunningLabel : String
oneLoopQCDRunningLabel =
  "alpha_s(mu) = 4 pi / (beta0 log(mu^2 / Lambda_QCD^2)) after choosing beta0 and Lambda_QCD"

carrierScaleRunningBoundaryLabel : String
carrierScaleRunningBoundaryLabel =
  "carrier a_d = alpha1^d gives only a dimensionless scale label; it does not construct alpha_s(mu)"

record QCDRunningFromCarrierScaleReceipt : Setω where
  field
    status :
      QCDRunningFromCarrierScaleStatus

    carrierScaleReceipt :
      Scale.CarrierScaleFromHeegnerReceipt

    carrierScaleDimensionlessOnly :
      Scale.dimensionfulCarrierScaleDerived carrierScaleReceipt ≡ false

    rgTrajectoryReceipt :
      RG.CarrierRGTrajectoryYMReceipt

    rgTrajectoryStillOpen :
      RG.carrierRGTrajectoryConstructed rgTrajectoryReceipt ≡ false

    runningFormula :
      String

    runningFormulaIsCanonical :
      runningFormula ≡ oneLoopQCDRunningLabel

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ carrierScaleRunningBoundaryLabel

    carrierScaleConsumed :
      Bool

    carrierScaleConsumedIsTrue :
      carrierScaleConsumed ≡ true

    qcdRunningRequirementsRecorded :
      Bool

    qcdRunningRequirementsRecordedIsTrue :
      qcdRunningRequirementsRecorded ≡ true

    alphaSRunningConstructed :
      Bool

    alphaSRunningConstructedIsFalse :
      alphaSRunningConstructed ≡ false

    lambdaQCDAnchorConstructed :
      Bool

    lambdaQCDAnchorConstructedIsFalse :
      lambdaQCDAnchorConstructed ≡ false

    continuumBetaRunningConstructed :
      Bool

    continuumBetaRunningConstructedIsFalse :
      continuumBetaRunningConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    requirements :
      List QCDRunningRequirement

    requirementsAreCanonical :
      requirements ≡ canonicalQCDRunningRequirements

    promotionFlags :
      List QCDRunningPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open QCDRunningFromCarrierScaleReceipt public

canonicalQCDRunningFromCarrierScaleReceipt :
  QCDRunningFromCarrierScaleReceipt
canonicalQCDRunningFromCarrierScaleReceipt =
  record
    { status =
        qcdRunningAuditedCarrierScaleNotEnough
    ; carrierScaleReceipt =
        Scale.canonicalCarrierScaleFromHeegnerReceipt
    ; carrierScaleDimensionlessOnly =
        refl
    ; rgTrajectoryReceipt =
        RG.canonicalCarrierRGTrajectoryYMReceipt
    ; rgTrajectoryStillOpen =
        refl
    ; runningFormula =
        oneLoopQCDRunningLabel
    ; runningFormulaIsCanonical =
        refl
    ; boundaryStatement =
        carrierScaleRunningBoundaryLabel
    ; boundaryStatementIsCanonical =
        refl
    ; carrierScaleConsumed =
        true
    ; carrierScaleConsumedIsTrue =
        refl
    ; qcdRunningRequirementsRecorded =
        true
    ; qcdRunningRequirementsRecordedIsTrue =
        refl
    ; alphaSRunningConstructed =
        false
    ; alphaSRunningConstructedIsFalse =
        refl
    ; lambdaQCDAnchorConstructed =
        false
    ; lambdaQCDAnchorConstructedIsFalse =
        refl
    ; continuumBetaRunningConstructed =
        false
    ; continuumBetaRunningConstructedIsFalse =
        refl
    ; continuumYangMillsConstructed =
        true
    ; continuumYangMillsConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; requirements =
        canonicalQCDRunningRequirements
    ; requirementsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

qcdRunningFromCarrierScaleKeepsRunningFalse :
  alphaSRunningConstructed canonicalQCDRunningFromCarrierScaleReceipt ≡ false
qcdRunningFromCarrierScaleKeepsRunningFalse =
  refl
