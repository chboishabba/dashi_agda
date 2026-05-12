module DASHI.Physics.Closure.W4MatterStressEnergyInterfaceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as W4External

------------------------------------------------------------------------
-- W4 matter/stress-energy interface receipt.
--
-- This is a pre-GR contract surface.  It records the minimum Candidate256
-- physical-calibration payload needed before W4 matter and stress-energy
-- can be named as typed consumers.  It does not construct matter, stress
-- energy, a discrete Einstein law, a GR law, a QFT law, or a GR/QFT
-- promotion.

record W4MatterStressEnergyPreflightSurface : Setω where
  field
    MatterField :
      Set

    T_mu_nu :
      MatterField →
      Set

    matterFieldFromW4 :
      W4External.Candidate256PhysicalCalibrationExternalReceipt →
      MatterField

    stressEnergyTensorFromW4 :
      (matter : MatterField) →
      T_mu_nu matter

    preflightBoundary :
      List String

record W4MatterStressEnergyPromotion : Setω where
  field
    candidate256PhysicalCalibrationReceipt :
      W4External.Candidate256PhysicalCalibrationExternalReceipt

    preflightSurface :
      W4MatterStressEnergyPreflightSurface

    matterField :
      W4MatterStressEnergyPreflightSurface.MatterField preflightSurface

    stressEnergyTensor :
      W4MatterStressEnergyPreflightSurface.T_mu_nu
        preflightSurface
        matterField

    promotionBoundary :
      List String

Candidate256PhysicalCalibrationExternalReceiptMissing : Setω
Candidate256PhysicalCalibrationExternalReceiptMissing =
  W4External.Candidate256PhysicalCalibrationExternalReceipt →
  ⊥

notCandidate256ToNoW4MatterStressEnergyPromotion :
  Candidate256PhysicalCalibrationExternalReceiptMissing →
  W4MatterStressEnergyPromotion →
  ⊥
notCandidate256ToNoW4MatterStressEnergyPromotion missingCandidate256 promotion =
  missingCandidate256
    (W4MatterStressEnergyPromotion.candidate256PhysicalCalibrationReceipt
      promotion)

candidate256MissingHere :
  Candidate256PhysicalCalibrationExternalReceiptMissing
candidate256MissingHere =
  W4External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere

w4MatterStressEnergyPromotionImpossibleHere :
  W4MatterStressEnergyPromotion →
  ⊥
w4MatterStressEnergyPromotionImpossibleHere =
  notCandidate256ToNoW4MatterStressEnergyPromotion candidate256MissingHere

record W4MatterStressEnergyInterfaceContractStatus : Setω where
  field
    requiredCalibrationReceiptName :
      String

    matterFieldFromW4TargetShape :
      String

    stressEnergyTensorFromW4TargetShape :
      String

    orderedContractPath :
      List String

    missingGap :
      String

    governanceBoundary :
      List String

    noPromotionWithoutCandidate256 :
      W4MatterStressEnergyPromotion →
      ⊥

canonicalW4MatterStressEnergyInterfaceContractStatus :
  W4MatterStressEnergyInterfaceContractStatus
canonicalW4MatterStressEnergyInterfaceContractStatus =
  record
    { requiredCalibrationReceiptName =
        "DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation.Candidate256PhysicalCalibrationExternalReceipt"
    ; matterFieldFromW4TargetShape =
        "matterFieldFromW4 : Candidate256PhysicalCalibrationExternalReceipt -> MatterField"
    ; stressEnergyTensorFromW4TargetShape =
        "stressEnergyTensorFromW4 : MatterField -> T_mu_nu"
    ; orderedContractPath =
        "Candidate256 calibration receipt"
        ∷ "MatterField"
        ∷ "T_mu_nu"
        ∷ "discrete Einstein law obligation"
        ∷ []
    ; missingGap =
        "Missing Candidate256 physical calibration receipt"
    ; governanceBoundary =
        "No W4 matter field can be consumed from Candidate256 without Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "No W4 stress-energy tensor can be promoted without a W4 matter field derived behind that receipt"
        ∷ "This module does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "This module does not construct W4MatterStressEnergyPromotion"
        ∷ "This module does not define grEquationLaw"
        ∷ "This module does not promote GR, QFT, GR/QFT, W4, or W5"
        ∷ []
    ; noPromotionWithoutCandidate256 =
        w4MatterStressEnergyPromotionImpossibleHere
    }
