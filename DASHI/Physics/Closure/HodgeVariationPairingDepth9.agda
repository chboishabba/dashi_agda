module DASHI.Physics.Closure.HodgeVariationPairingDepth9 where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YangMillsFieldEquationReceipt as YMReceipt
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as Gate3
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Depth-9 Hodge variation pairing wrapper.
--
-- This module does not invent a selected variation pairing inhabitant.  It
-- packages the existing Gate 3 depth-9 geometry witness together with the
-- route-B Hodge/current and zero-IBP receipts, and it records the exact
-- blocker token that remains open: missingVariationPairingForSelectedHodgeStar.

data HodgeVariationPairingDepth9Status : Set where
  failClosedWithExactVariationBlocker :
    HodgeVariationPairingDepth9Status

record HodgeVariationPairingDepth9Receipt : Set₁ where
  field
    status :
      HodgeVariationPairingDepth9Status

    depth9Connection :
      Gate3.ConnectionOnDepth9

    depth9ConnectionIsCanonical :
      depth9Connection ≡ Gate3.canonicalConnectionOnDepth9

    selectedHodgeVariationPairing :
      Gate3.VariationPairing

    selectedHodgeVariationPairingIsCanonical :
      selectedHodgeVariationPairing
      ≡
      Gate3.canonicalVariationPairing

    routeBLowerHodgeCurrentSurface :
      YMReceipt.YMSFGCRouteBLowerHodgeCurrentSurface

    routeBLowerHodgeCurrentSurfaceIsCanonical :
      routeBLowerHodgeCurrentSurface
      ≡
      YMReceipt.canonicalYMSFGCRouteBLowerHodgeCurrentSurface

    routeBZeroDiscreteVariationIBPPrimitiveSupply :
      YMObs.YMSFGCDiscreteVariationIBPPrimitiveSupply

    routeBZeroDiscreteVariationIBPPrimitiveSupplyIsCanonical :
      routeBZeroDiscreteVariationIBPPrimitiveSupply
      ≡
      YMReceipt.canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply

    middle6DiscreteIBPVariationPairingProgress :
      YMObs.YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    middle6DiscreteIBPVariationPairingProgressIsCanonical :
      middle6DiscreteIBPVariationPairingProgress
      ≡
      YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt

    finiteDiscreteIBPLawIsZeroLaw :
      YMObs.YMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt.finiteDiscreteIBPLaw
        middle6DiscreteIBPVariationPairingProgress
      ≡
      YMObs.sfgcZeroDiscreteVariationIBPLaw

    selectedDStarFEqualsJLaw :
      (A : SFGC.GaugeField) →
      YMReceipt.routeBSelectedCovariantDerivativeOnDualCurvature
        A
        (YMReceipt.routeBSelectedHodgeStar
          (SFGC.sfgcSite2DFieldStrengthFromCurvature
            (SFGC.sfgcSite2Dδ₁
              (SFGC.sfgcSite2DConnectionTo1Form A))))
      ≡
      YMReceipt.routeBSelectedCurrentSource A

    selectedDStarFEqualsJLawIsCanonical :
      selectedDStarFEqualsJLaw
      ≡
      YMReceipt.routeBSelectedDStarFEqualsJLaw

    gate3DownstreamHodgeVariationIBP :
      YMObs.YMSFGCGate3DownstreamHodgeVariationIBPReceipt

    gate3DownstreamHodgeVariationIBPIsCanonical :
      gate3DownstreamHodgeVariationIBP
      ≡
      YMObs.canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt

    exactVariationPairingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactVariationPairingBlockerIsExact :
      exactVariationPairingBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    variationPairingPromoted :
      Bool

    variationPairingPromotedIsFalse :
      variationPairingPromoted ≡ false

    receiptBoundary :
      List String

open HodgeVariationPairingDepth9Receipt public

canonicalHodgeVariationPairingDepth9Receipt :
  HodgeVariationPairingDepth9Receipt
canonicalHodgeVariationPairingDepth9Receipt =
  record
    { status =
        failClosedWithExactVariationBlocker
    ; depth9Connection =
        Gate3.canonicalConnectionOnDepth9
    ; depth9ConnectionIsCanonical =
        refl
    ; selectedHodgeVariationPairing =
        Gate3.canonicalVariationPairing
    ; selectedHodgeVariationPairingIsCanonical =
        refl
    ; routeBLowerHodgeCurrentSurface =
        YMReceipt.canonicalYMSFGCRouteBLowerHodgeCurrentSurface
    ; routeBLowerHodgeCurrentSurfaceIsCanonical =
        refl
    ; routeBZeroDiscreteVariationIBPPrimitiveSupply =
        YMReceipt.canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply
    ; routeBZeroDiscreteVariationIBPPrimitiveSupplyIsCanonical =
        refl
    ; middle6DiscreteIBPVariationPairingProgress =
        YMObs.canonicalYMSFGCMiddle6DiscreteIBPVariationPairingProgressReceipt
    ; middle6DiscreteIBPVariationPairingProgressIsCanonical =
        refl
    ; finiteDiscreteIBPLawIsZeroLaw =
        refl
    ; selectedDStarFEqualsJLaw =
        YMReceipt.routeBSelectedDStarFEqualsJLaw
    ; selectedDStarFEqualsJLawIsCanonical =
        refl
    ; gate3DownstreamHodgeVariationIBP =
        YMObs.canonicalYMSFGCGate3DownstreamHodgeVariationIBPReceipt
    ; gate3DownstreamHodgeVariationIBPIsCanonical =
        refl
    ; exactVariationPairingBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; exactVariationPairingBlockerIsExact =
        refl
    ; variationPairingPromoted =
        false
    ; variationPairingPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Depth-9 geometry is carried by the canonical ConnectionOnDepth9 witness"
        ∷ "The selected Hodge-star surface is the canonical lower variation pairing candidate from Gate 3"
        ∷ "Route B Hodge/current is consumed from YangMillsFieldEquationReceipt as canonicalYMSFGCRouteBLowerHodgeCurrentSurface"
        ∷ "The zero discrete IBP supply is consumed from YangMillsFieldEquationReceipt as canonicalRouteBZeroDiscreteVariationIBPPrimitiveSupply"
        ∷ "The finite zero-variation IBP law and selected lower D * F = J source-current law are recorded as concrete definitional witnesses"
        ∷ "The exact variation blocker remains missingVariationPairingForSelectedHodgeStar"
        ∷ "No honest selected variation pairing inhabitant is introduced here; promotion stays false"
        ∷ []
    }

selectedHodgeVariationPairingDepth9 :
  HodgeVariationPairingDepth9Receipt
selectedHodgeVariationPairingDepth9 =
  canonicalHodgeVariationPairingDepth9Receipt
