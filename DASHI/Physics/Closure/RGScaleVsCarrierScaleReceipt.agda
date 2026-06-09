module DASHI.Physics.Closure.RGScaleVsCarrierScaleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierRenormalizationGroupScaleReceipt as RG

data CarrierScaleAnchor : Set where
  planckScaleAnchorCandidate : CarrierScaleAnchor

rgScaleBoundaryStatement : String
rgScaleBoundaryStatement =
  "A carrier RG fixed point supplies only a dimensionless scale until an external physical scale anchor and RG running map are constructed."

record RGScaleVsCarrierScaleReceipt : Setω where
  field
    carrierRGScaleReceipt :
      RG.CarrierRGScaleReceipt

    dimensionfulConvergenceStillOpen :
      RG.dimensionfulMassGapConvergesConstructedHere carrierRGScaleReceipt
      ≡
      false

    scaleAnchor :
      CarrierScaleAnchor

    carrierScaleAnchoredAtPlanck :
      Bool

    carrierScaleAnchoredAtPlanckIsCandidate :
      carrierScaleAnchoredAtPlanck ≡ true

    rgRunningFromPlanckToQCD :
      Bool

    rgRunningFromPlanckToQCDIsFalse :
      rgRunningFromPlanckToQCD ≡ false

    qcdScaleMatched :
      Bool

    qcdScaleMatchedIsFalse :
      qcdScaleMatched ≡ false

    dimensionfulMassGapFromRG :
      Bool

    dimensionfulMassGapFromRGIsFalse :
      dimensionfulMassGapFromRG ≡ false

    yangMillsMassGapClayPromoted :
      Bool

    yangMillsMassGapClayPromotedIsFalse :
      yangMillsMassGapClayPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ rgScaleBoundaryStatement

    receiptBoundary :
      List String

open RGScaleVsCarrierScaleReceipt public

canonicalRGScaleVsCarrierScaleReceipt :
  RGScaleVsCarrierScaleReceipt
canonicalRGScaleVsCarrierScaleReceipt =
  record
    { carrierRGScaleReceipt =
        RG.canonicalCarrierRGScaleReceipt
    ; dimensionfulConvergenceStillOpen =
        refl
    ; scaleAnchor =
        planckScaleAnchorCandidate
    ; carrierScaleAnchoredAtPlanck =
        true
    ; carrierScaleAnchoredAtPlanckIsCandidate =
        refl
    ; rgRunningFromPlanckToQCD =
        false
    ; rgRunningFromPlanckToQCDIsFalse =
        refl
    ; qcdScaleMatched =
        false
    ; qcdScaleMatchedIsFalse =
        refl
    ; dimensionfulMassGapFromRG =
        false
    ; dimensionfulMassGapFromRGIsFalse =
        refl
    ; yangMillsMassGapClayPromoted =
        false
    ; yangMillsMassGapClayPromotedIsFalse =
        refl
    ; boundaryStatement =
        rgScaleBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "The Planck anchor is a candidate scale-setting convention, not a constructed calibration"
        ∷ "Running from the carrier/Planck scale to QCD is open"
        ∷ "No dimensionful continuum Yang-Mills mass gap or Clay promotion is derived"
        ∷ []
    }

dimensionfulMassGapStillOpen :
  dimensionfulMassGapFromRG canonicalRGScaleVsCarrierScaleReceipt ≡ false
dimensionfulMassGapStillOpen =
  refl

