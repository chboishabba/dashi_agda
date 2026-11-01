module DASHI.Physics.Closure.YMStrictSelectedHodgeAlgebraLaws where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.HodgeVariationPairingDepth9 as HV9
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as Gate3
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as StrictPairing
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Finite selected-Hodge algebra laws.
--
-- This module isolates the algebra that is already available for the
-- selected finite carrier.  The selected Hodge target is the lower finite
-- endomap on SFGCSite2DFieldStrengthBridge.  Because that endomap is
-- definitionally the identity, its square and stability laws are exact.
--
-- The dual/current laws below are wrapper/projection laws over the
-- user-supplied finite carriers.  They do not claim a metric Hodge star,
-- physical source coupling, continuum Yang-Mills, mass gap, or Clay theorem.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedHodgeAlgebraStatus : Set where
  finiteSelectedHodgeAlgebraCalculatedPhysicalHodgeBlocked :
    StrictSelectedHodgeAlgebraStatus

data StrictSelectedHodgeAlgebraRow : Set where
  selectedHodgeTargetRow :
    StrictSelectedHodgeAlgebraRow

  selectedHodgeIdentityLawRow :
    StrictSelectedHodgeAlgebraRow

  selectedHodgeSquareLawRow :
    StrictSelectedHodgeAlgebraRow

  selectedHodgeStabilityLawRow :
    StrictSelectedHodgeAlgebraRow

  selectedDualCarrierProjectionRow :
    StrictSelectedHodgeAlgebraRow

  selectedCurrentExtractionRow :
    StrictSelectedHodgeAlgebraRow

  selectedDStarFEqualsCurrentRow :
    StrictSelectedHodgeAlgebraRow

  physicalPromotionBlockedRow :
    StrictSelectedHodgeAlgebraRow

canonicalStrictSelectedHodgeAlgebraRows :
  List StrictSelectedHodgeAlgebraRow
canonicalStrictSelectedHodgeAlgebraRows =
  selectedHodgeTargetRow
  ∷ selectedHodgeIdentityLawRow
  ∷ selectedHodgeSquareLawRow
  ∷ selectedHodgeStabilityLawRow
  ∷ selectedDualCarrierProjectionRow
  ∷ selectedCurrentExtractionRow
  ∷ selectedDStarFEqualsCurrentRow
  ∷ physicalPromotionBlockedRow
  ∷ []

selectedFiniteHodgeTarget :
  SFGC.SFGCSite2DFieldStrengthBridge →
  SFGC.SFGCSite2DFieldStrengthBridge
selectedFiniteHodgeTarget =
  YMObs.sfgcSelectedHodgeStarLowerCandidate

selectedFiniteHodgeTargetIsGate3Canonical :
  Gate3.VariationPairing.selectedHodgeStar
    Gate3.canonicalVariationPairing
  ≡
  selectedFiniteHodgeTarget
selectedFiniteHodgeTargetIsGate3Canonical =
  refl

selectedFiniteHodgeIdentityLaw :
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  selectedFiniteHodgeTarget fieldStrength
  ≡
  fieldStrength
selectedFiniteHodgeIdentityLaw fieldStrength =
  refl

selectedFiniteHodgeSquareLaw :
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  selectedFiniteHodgeTarget (selectedFiniteHodgeTarget fieldStrength)
  ≡
  fieldStrength
selectedFiniteHodgeSquareLaw fieldStrength =
  refl

selectedFiniteHodgeStabilityLaw :
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  selectedFiniteHodgeTarget (selectedFiniteHodgeTarget fieldStrength)
  ≡
  selectedFiniteHodgeTarget fieldStrength
selectedFiniteHodgeStabilityLaw fieldStrength =
  refl

selectedFiniteDualCarrier :
  SFGC.SFGCSite2DFieldStrengthBridge →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
selectedFiniteDualCarrier =
  StrictPairing.strictSelectedHodgeStarToDual

selectedFiniteDualCarrierProjectionLaw :
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
    (selectedFiniteDualCarrier fieldStrength)
  ≡
  selectedFiniteHodgeTarget fieldStrength
selectedFiniteDualCarrierProjectionLaw =
  StrictPairing.strictSelectedHodgeStarToDualIsLowerCandidate

selectedFiniteDualCarrierStableProjectionLaw :
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
    (selectedFiniteDualCarrier (selectedFiniteHodgeTarget fieldStrength))
  ≡
  selectedFiniteHodgeTarget fieldStrength
selectedFiniteDualCarrierStableProjectionLaw fieldStrength =
  refl

selectedFiniteCurrentCarrier :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
selectedFiniteCurrentCarrier =
  StrictPairing.strictSelectedCurrentFromDerivative

selectedFiniteCurrentExtractedDual :
  YMObs.YMSFGCUserSuppliedCurrentCarrier →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
selectedFiniteCurrentExtractedDual
  (YMObs.ymSFGCUserSuppliedCurrentFromDualCurvature dualCurvature) =
  dualCurvature

selectedFiniteCurrentExtractionLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (dualCurvature : YMObs.YMSFGCUserSuppliedDualCurvatureCarrier) →
  selectedFiniteCurrentExtractedDual
    (selectedFiniteCurrentCarrier connection dualCurvature)
  ≡
  dualCurvature
selectedFiniteCurrentExtractionLaw connection dualCurvature =
  refl

selectedFiniteDStarFEqualsCurrentLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (dualCurvature : YMObs.YMSFGCUserSuppliedDualCurvatureCarrier) →
  StrictPairing.strictSelectedCovariantDerivativeOnDual
    connection
    dualCurvature
  ≡
  selectedFiniteCurrentCarrier connection dualCurvature
selectedFiniteDStarFEqualsCurrentLaw =
  StrictPairing.strictSelectedDStarFEqualsSelectedCurrentLaw

record StrictSelectedHodgeAlgebraLaws : Set₁ where
  field
    status :
      StrictSelectedHodgeAlgebraStatus

    consumedDepth9Receipt :
      HV9.HodgeVariationPairingDepth9Receipt

    consumedDepth9ReceiptIsCanonical :
      consumedDepth9Receipt
      ≡
      HV9.canonicalHodgeVariationPairingDepth9Receipt

    consumedGate3VariationPairing :
      Gate3.VariationPairing

    consumedGate3VariationPairingIsCanonical :
      consumedGate3VariationPairing
      ≡
      Gate3.canonicalVariationPairing

    consumedStrictPairingCalculation :
      StrictPairing.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictPairingCalculationIsCanonical :
      consumedStrictPairingCalculation
      ≡
      StrictPairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    selectedHodgeTarget :
      SFGC.SFGCSite2DFieldStrengthBridge →
      SFGC.SFGCSite2DFieldStrengthBridge

    selectedHodgeTargetIsCanonical :
      selectedHodgeTarget
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate

    selectedHodgeTargetIsGate3Canonical :
      selectedHodgeTarget
      ≡
      Gate3.VariationPairing.selectedHodgeStar
        consumedGate3VariationPairing

    selectedHodgeIdentity :
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      selectedHodgeTarget fieldStrength
      ≡
      fieldStrength

    selectedHodgeSquare :
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      selectedHodgeTarget (selectedHodgeTarget fieldStrength)
      ≡
      fieldStrength

    selectedHodgeStable :
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      selectedHodgeTarget (selectedHodgeTarget fieldStrength)
      ≡
      selectedHodgeTarget fieldStrength

    selectedDualCarrier :
      SFGC.SFGCSite2DFieldStrengthBridge →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    selectedDualCarrierIsStrictPairingTarget :
      selectedDualCarrier
      ≡
      StrictPairing.strictSelectedHodgeStarToDual

    selectedDualProjection :
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
        (selectedDualCarrier fieldStrength)
      ≡
      selectedHodgeTarget fieldStrength

    selectedDualStableProjection :
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
        (selectedDualCarrier (selectedHodgeTarget fieldStrength))
      ≡
      selectedHodgeTarget fieldStrength

    selectedCurrentCarrier :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    selectedCurrentCarrierIsStrictPairingCurrent :
      selectedCurrentCarrier
      ≡
      StrictPairing.strictSelectedCurrentFromDerivative

    selectedCurrentExtractedDual :
      YMObs.YMSFGCUserSuppliedCurrentCarrier →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    selectedCurrentExtraction :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (dualCurvature : YMObs.YMSFGCUserSuppliedDualCurvatureCarrier) →
      selectedCurrentExtractedDual
        (selectedCurrentCarrier connection dualCurvature)
      ≡
      dualCurvature

    selectedDStarFEqualsCurrent :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (dualCurvature : YMObs.YMSFGCUserSuppliedDualCurvatureCarrier) →
      StrictPairing.strictSelectedCovariantDerivativeOnDual
        connection
        dualCurvature
      ≡
      selectedCurrentCarrier connection dualCurvature

    selectedFiniteAlgebraCalculated :
      Bool

    selectedFiniteAlgebraCalculatedIsTrue :
      selectedFiniteAlgebraCalculated ≡ true

    metricHodgeStarPromoted :
      Bool

    metricHodgeStarPromotedIsFalse :
      metricHodgeStarPromoted ≡ false

    sourcedYMPromoted :
      Bool

    sourcedYMPromotedIsFalse :
      sourcedYMPromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    rowIndex :
      List StrictSelectedHodgeAlgebraRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedHodgeAlgebraRows

    rowCount :
      Nat

    rowCountIs8 :
      rowCount ≡ 8

    algebraBoundary :
      List String

open StrictSelectedHodgeAlgebraLaws public

canonicalStrictSelectedHodgeAlgebraLaws :
  StrictSelectedHodgeAlgebraLaws
canonicalStrictSelectedHodgeAlgebraLaws =
  record
    { status =
        finiteSelectedHodgeAlgebraCalculatedPhysicalHodgeBlocked
    ; consumedDepth9Receipt =
        HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; consumedDepth9ReceiptIsCanonical =
        refl
    ; consumedGate3VariationPairing =
        Gate3.canonicalVariationPairing
    ; consumedGate3VariationPairingIsCanonical =
        refl
    ; consumedStrictPairingCalculation =
        StrictPairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictPairingCalculationIsCanonical =
        refl
    ; selectedHodgeTarget =
        selectedFiniteHodgeTarget
    ; selectedHodgeTargetIsCanonical =
        refl
    ; selectedHodgeTargetIsGate3Canonical =
        refl
    ; selectedHodgeIdentity =
        selectedFiniteHodgeIdentityLaw
    ; selectedHodgeSquare =
        selectedFiniteHodgeSquareLaw
    ; selectedHodgeStable =
        selectedFiniteHodgeStabilityLaw
    ; selectedDualCarrier =
        selectedFiniteDualCarrier
    ; selectedDualCarrierIsStrictPairingTarget =
        refl
    ; selectedDualProjection =
        selectedFiniteDualCarrierProjectionLaw
    ; selectedDualStableProjection =
        selectedFiniteDualCarrierStableProjectionLaw
    ; selectedCurrentCarrier =
        selectedFiniteCurrentCarrier
    ; selectedCurrentCarrierIsStrictPairingCurrent =
        refl
    ; selectedCurrentExtractedDual =
        selectedFiniteCurrentExtractedDual
    ; selectedCurrentExtraction =
        selectedFiniteCurrentExtractionLaw
    ; selectedDStarFEqualsCurrent =
        selectedFiniteDStarFEqualsCurrentLaw
    ; selectedFiniteAlgebraCalculated =
        true
    ; selectedFiniteAlgebraCalculatedIsTrue =
        refl
    ; metricHodgeStarPromoted =
        false
    ; metricHodgeStarPromotedIsFalse =
        refl
    ; sourcedYMPromoted =
        false
    ; sourcedYMPromotedIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; rowIndex =
        canonicalStrictSelectedHodgeAlgebraRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        8
    ; rowCountIs8 =
        refl
    ; algebraBoundary =
        "The selected finite Hodge target is the canonical lower candidate on SFGCSite2DFieldStrengthBridge"
        ∷ "That selected lower candidate is definitionally the identity, so square and stability laws close by refl"
        ∷ "The user-supplied dual carrier is a finite wrapper around the selected Hodge target, with a projection law back to the bridge"
        ∷ "The user-supplied current carrier is a finite wrapper around selected dual curvature, with an extraction law back to that dual"
        ∷ "Selected D * F equals selected current is only the finite definitional current law from the strict selected pairing surface"
        ∷ "No metric Hodge star, physical source coupling, continuum Yang-Mills, mass gap, Clay, or terminal promotion is introduced"
        ∷ []
    }

canonicalStrictSelectedHodgeAlgebraRowCountIs8 :
  listCount canonicalStrictSelectedHodgeAlgebraRows ≡ 8
canonicalStrictSelectedHodgeAlgebraRowCountIs8 =
  refl

canonicalStrictSelectedHodgeAlgebraCalculated :
  StrictSelectedHodgeAlgebraLaws.selectedFiniteAlgebraCalculated
    canonicalStrictSelectedHodgeAlgebraLaws
  ≡
  true
canonicalStrictSelectedHodgeAlgebraCalculated =
  refl

canonicalStrictSelectedHodgeAlgebraMetricPromotionFalse :
  StrictSelectedHodgeAlgebraLaws.metricHodgeStarPromoted
    canonicalStrictSelectedHodgeAlgebraLaws
  ≡
  false
canonicalStrictSelectedHodgeAlgebraMetricPromotionFalse =
  refl

canonicalStrictSelectedHodgeAlgebraYMPromotionFalse :
  StrictSelectedHodgeAlgebraLaws.sourcedYMPromoted
    canonicalStrictSelectedHodgeAlgebraLaws
  ≡
  false
canonicalStrictSelectedHodgeAlgebraYMPromotionFalse =
  refl

canonicalStrictSelectedHodgeAlgebraClayPromotionFalse :
  StrictSelectedHodgeAlgebraLaws.clayYMPromoted
    canonicalStrictSelectedHodgeAlgebraLaws
  ≡
  false
canonicalStrictSelectedHodgeAlgebraClayPromotionFalse =
  refl
