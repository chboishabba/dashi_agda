module DASHI.Physics.Closure.FieldStrengthTransportOnGaugeBundle where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YangMillsFieldEquationReceipt as YMRec
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as Gate3
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Field-strength transport on the selected gauge bundle.
--
-- This is a thin fail-closed consumer.  It does not construct the missing
-- transport action itself; it packages the exact blocker chain together with
-- the already-canonical route-B selected transport/current receipts.

record FieldStrengthTransportOnGaugeBundleReceipt : Set₁ where
  field
    gate3Receipt :
      Gate3.Gate3DiscreteGeometryReceipt

    gate3ReceiptIsCanonical :
      gate3Receipt ≡ Gate3.canonicalGate3DiscreteGeometryReceipt

    selectedDiscreteHodgeCovariantDerivativeSupply :
      YMObs.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply

    selectedDiscreteHodgeCovariantDerivativeSupplyIsCanonical :
      selectedDiscreteHodgeCovariantDerivativeSupply
      ≡
      YMRec.canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply

    lowerHodgeCurrentSurface :
      YMRec.YMSFGCRouteBLowerHodgeCurrentSurface

    lowerHodgeCurrentSurfaceIsCanonical :
      lowerHodgeCurrentSurface
      ≡
      YMRec.canonicalYMSFGCRouteBLowerHodgeCurrentSurface

    selectedDStarFEqualsJLaw :
      (A : SFGC.GaugeField) →
      YMRec.routeBSelectedCovariantDerivativeOnDualCurvature
        A
        (YMRec.routeBSelectedHodgeStar
          (SFGC.sfgcSite2DFieldStrengthFromCurvature
            (SFGC.sfgcSite2Dδ₁
              (SFGC.sfgcSite2DConnectionTo1Form A))))
      ≡
      YMRec.routeBSelectedCurrentSource A

    selectedDStarFEqualsJLawIsCanonical :
      selectedDStarFEqualsJLaw
      ≡
      YMRec.routeBSelectedDStarFEqualsJLaw

    selectedGaugeBundleTransportBlocker :
      YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive

    selectedGaugeBundleTransportBlockerIsExact :
      selectedGaugeBundleTransportBlocker
      ≡
      YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle

    transportActionPromoted :
      Bool

    transportActionPromotedIsFalse :
      transportActionPromoted ≡ false

    exactBlockerChain :
      List Gate3.Gate3DiscreteGeometryOpenObligation

    exactBlockerChainIsCanonical :
      exactBlockerChain
      ≡
      Gate3.canonicalGate3DiscreteGeometryOpenObligations

    exactBlockerBoundary :
      List String

    exactBlockerBoundaryIsCanonical :
      exactBlockerBoundary
      ≡
      Gate3.gate3Boundary Gate3.canonicalGate3DiscreteGeometryReceipt

open FieldStrengthTransportOnGaugeBundleReceipt public

canonicalFieldStrengthTransportOnGaugeBundleReceipt :
  FieldStrengthTransportOnGaugeBundleReceipt
canonicalFieldStrengthTransportOnGaugeBundleReceipt =
  record
    { gate3Receipt =
        Gate3.canonicalGate3DiscreteGeometryReceipt
    ; gate3ReceiptIsCanonical =
        refl
    ; selectedDiscreteHodgeCovariantDerivativeSupply =
        YMRec.canonicalRouteBSelectedDiscreteHodgeCovariantDerivativeSupply
    ; selectedDiscreteHodgeCovariantDerivativeSupplyIsCanonical =
        refl
    ; lowerHodgeCurrentSurface =
        YMRec.canonicalYMSFGCRouteBLowerHodgeCurrentSurface
    ; lowerHodgeCurrentSurfaceIsCanonical =
        refl
    ; selectedDStarFEqualsJLaw =
        YMRec.routeBSelectedDStarFEqualsJLaw
    ; selectedDStarFEqualsJLawIsCanonical =
        refl
    ; selectedGaugeBundleTransportBlocker =
        YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
    ; selectedGaugeBundleTransportBlockerIsExact =
        refl
    ; transportActionPromoted =
        false
    ; transportActionPromotedIsFalse =
        refl
    ; exactBlockerChain =
        Gate3.canonicalGate3DiscreteGeometryOpenObligations
    ; exactBlockerChainIsCanonical =
        refl
    ; exactBlockerBoundary =
        Gate3.gate3Boundary Gate3.canonicalGate3DiscreteGeometryReceipt
    ; exactBlockerBoundaryIsCanonical =
        refl
    }

fieldStrengthTransportBlocker :
  YMObs.YMSFGCSelectedCovariantDerivativeMissingPrimitive
fieldStrengthTransportBlocker =
  YMObs.missingFieldStrengthTransportActionOnSelectedGaugeBundle
