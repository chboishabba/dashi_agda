module DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.HodgeVariationPairingDepth9 as HV9
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as Gate3
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Strict selected-Hodge variation pairing calculation.
--
-- The repo already has substantial Hodge-star/YM machinery: depth-9
-- selected geometry, Route-B selected D * F = J on the finite carrier, and
-- a zero finite IBP lower law.  This module records the next exact
-- calculation over the user-supplied variation/action carriers now exposed by
-- YangMillsFieldEquationObstruction: selected zero action variation equals
-- selected zero Euler-Lagrange pairing plus selected zero boundary term.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedHodgeVariationPairingStatus : Set where
  strictFiniteSelectedPairingCalculatedPhysicalYMBlocked :
    StrictSelectedHodgeVariationPairingStatus

data StrictSelectedHodgeVariationPairingRow : Set where
  selectedHodgeToDualCarrierRow :
    StrictSelectedHodgeVariationPairingRow

  selectedCovariantDerivativeToCurrentRow :
    StrictSelectedHodgeVariationPairingRow

  finiteVariationCarrierRow :
    StrictSelectedHodgeVariationPairingRow

  finiteActionScalarCarrierRow :
    StrictSelectedHodgeVariationPairingRow

  finiteSelectedVariationPairingRow :
    StrictSelectedHodgeVariationPairingRow

  finiteSelectedDiscreteIBPLawRow :
    StrictSelectedHodgeVariationPairingRow

  physicalPromotionBlockedRow :
    StrictSelectedHodgeVariationPairingRow

canonicalStrictSelectedHodgeVariationPairingRows :
  List StrictSelectedHodgeVariationPairingRow
canonicalStrictSelectedHodgeVariationPairingRows =
  selectedHodgeToDualCarrierRow
  ∷ selectedCovariantDerivativeToCurrentRow
  ∷ finiteVariationCarrierRow
  ∷ finiteActionScalarCarrierRow
  ∷ finiteSelectedVariationPairingRow
  ∷ finiteSelectedDiscreteIBPLawRow
  ∷ physicalPromotionBlockedRow
  ∷ []

strictSelectedHodgeStarToDual :
  SFGC.SFGCSite2DFieldStrengthBridge →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
strictSelectedHodgeStarToDual fieldStrength =
  YMObs.ymSFGCUserSuppliedDualCurvatureFromFieldStrength
    (YMObs.sfgcSelectedHodgeStarLowerCandidate fieldStrength)

strictSelectedHodgeStarToDualIsLowerCandidate :
  (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
  YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
    (strictSelectedHodgeStarToDual fieldStrength)
  ≡
  YMObs.sfgcSelectedHodgeStarLowerCandidate fieldStrength
strictSelectedHodgeStarToDualIsLowerCandidate fieldStrength =
  refl

strictSelectedCovariantDerivativeOnDual :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
strictSelectedCovariantDerivativeOnDual connection dualCurvature =
  YMObs.ymSFGCUserSuppliedCurrentFromDualCurvature dualCurvature

strictSelectedCurrentFromDerivative :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
strictSelectedCurrentFromDerivative connection dualCurvature =
  strictSelectedCovariantDerivativeOnDual connection dualCurvature

strictSelectedDStarFEqualsSelectedCurrentLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (dualCurvature : YMObs.YMSFGCUserSuppliedDualCurvatureCarrier) →
  strictSelectedCovariantDerivativeOnDual connection dualCurvature
  ≡
  strictSelectedCurrentFromDerivative connection dualCurvature
strictSelectedDStarFEqualsSelectedCurrentLaw connection dualCurvature =
  refl

strictReferenceDualCurvature :
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
strictReferenceDualCurvature =
  strictSelectedHodgeStarToDual
    (YMObs.ymSFGCUserSuppliedConnectionCurvature
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      YMObs.sfgcReferencePlaquette)

strictSelectedHodgeVariationPairing :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedHodgeVariationPairing =
  YMObs.ymSFGCUserSuppliedEulerLagrangePairing

strictSelectedActionVariation :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedActionVariation =
  YMObs.ymSFGCUserSuppliedVariationOfAction

strictSelectedBoundaryTerm :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedBoundaryTerm =
  YMObs.ymSFGCUserSuppliedBoundaryTerm

strictActionScalarCombine :
  YMObs.YMSFGCUserSuppliedActionScalarCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictActionScalarCombine =
  YMObs.ymSFGCUserSuppliedCombineActionScalar

strictSelectedDiscreteIBPLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  strictSelectedActionVariation connection δA
  ≡
  strictActionScalarCombine
    (strictSelectedHodgeVariationPairing connection δA)
    (strictSelectedBoundaryTerm connection δA)
strictSelectedDiscreteIBPLaw =
  YMObs.ymSFGCUserSuppliedSelectedVariationIBPLaw

record StrictSelectedHodgeVariationPairingCalculation : Set₁ where
  field
    status :
      StrictSelectedHodgeVariationPairingStatus

    consumedDepth9Pairing :
      HV9.HodgeVariationPairingDepth9Receipt

    consumedDepth9PairingIsCanonical :
      consumedDepth9Pairing
      ≡
      HV9.canonicalHodgeVariationPairingDepth9Receipt

    consumedGate3VariationPairing :
      Gate3.VariationPairing

    consumedGate3VariationPairingIsCanonical :
      consumedGate3VariationPairing
      ≡
      Gate3.canonicalVariationPairing

    selectedFiniteClosure :
      YMObs.YMSFGCStrictSelectedHodgeVariationPairingFiniteClosure

    selectedFiniteClosureIsCanonical :
      selectedFiniteClosure
      ≡
      YMObs.canonicalYMSFGCStrictSelectedHodgeVariationPairingFiniteClosure

    selectedHodgeStar :
      SFGC.SFGCSite2DFieldStrengthBridge →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    selectedHodgeStarIsLowerCandidate :
      (fieldStrength : SFGC.SFGCSite2DFieldStrengthBridge) →
      YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
        (selectedHodgeStar fieldStrength)
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate fieldStrength

    referenceDualCurvature :
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    covariantDerivativeOnDual :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    selectedCurrent :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    selectedDStarFEqualsSelectedCurrent :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (dualCurvature : YMObs.YMSFGCUserSuppliedDualCurvatureCarrier) →
      covariantDerivativeOnDual connection dualCurvature
      ≡
      selectedCurrent connection dualCurvature

    strictVariationPairing :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    strictVariationPairingIsSelected :
      strictVariationPairing
      ≡
      strictSelectedHodgeVariationPairing

    strictActionVariation :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    strictActionVariationIsSelected :
      strictActionVariation
      ≡
      strictSelectedActionVariation

    strictBoundaryTerm :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    strictBoundaryTermIsSelected :
      strictBoundaryTerm
      ≡
      strictSelectedBoundaryTerm

    selectedDiscreteIBPLawInReceipt :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      strictActionVariation connection δA
      ≡
      strictActionScalarCombine
        (strictVariationPairing connection δA)
        (strictBoundaryTerm connection δA)

    variationCarrierNonempty :
      Bool

    variationCarrierNonemptyIsTrue :
      variationCarrierNonempty ≡ true

    actionScalarCarrierNonempty :
      Bool

    actionScalarCarrierNonemptyIsTrue :
      actionScalarCarrierNonempty ≡ true

    strictPairingCalculated :
      Bool

    strictPairingCalculatedIsTrue :
      strictPairingCalculated ≡ true

    physicalVariationPairingPromoted :
      Bool

    physicalVariationPairingPromotedIsFalse :
      physicalVariationPairingPromoted ≡ false

    strictYMPromoted :
      Bool

    strictYMPromotedIsFalse :
      strictYMPromoted ≡ false

    rowIndex :
      List StrictSelectedHodgeVariationPairingRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedHodgeVariationPairingRows

    rowCount :
      Nat

    rowCountIs7 :
      rowCount ≡ 7

    calculationBoundary :
      List String

open StrictSelectedHodgeVariationPairingCalculation public

canonicalStrictSelectedHodgeVariationPairingCalculation :
  StrictSelectedHodgeVariationPairingCalculation
canonicalStrictSelectedHodgeVariationPairingCalculation =
  record
    { status =
        strictFiniteSelectedPairingCalculatedPhysicalYMBlocked
    ; consumedDepth9Pairing =
        HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; consumedDepth9PairingIsCanonical =
        refl
    ; consumedGate3VariationPairing =
        Gate3.canonicalVariationPairing
    ; consumedGate3VariationPairingIsCanonical =
        refl
    ; selectedFiniteClosure =
        YMObs.canonicalYMSFGCStrictSelectedHodgeVariationPairingFiniteClosure
    ; selectedFiniteClosureIsCanonical =
        refl
    ; selectedHodgeStar =
        strictSelectedHodgeStarToDual
    ; selectedHodgeStarIsLowerCandidate =
        strictSelectedHodgeStarToDualIsLowerCandidate
    ; referenceDualCurvature =
        strictReferenceDualCurvature
    ; covariantDerivativeOnDual =
        strictSelectedCovariantDerivativeOnDual
    ; selectedCurrent =
        strictSelectedCurrentFromDerivative
    ; selectedDStarFEqualsSelectedCurrent =
        strictSelectedDStarFEqualsSelectedCurrentLaw
    ; strictVariationPairing =
        strictSelectedHodgeVariationPairing
    ; strictVariationPairingIsSelected =
        refl
    ; strictActionVariation =
        strictSelectedActionVariation
    ; strictActionVariationIsSelected =
        refl
    ; strictBoundaryTerm =
        strictSelectedBoundaryTerm
    ; strictBoundaryTermIsSelected =
        refl
    ; selectedDiscreteIBPLawInReceipt =
        strictSelectedDiscreteIBPLaw
    ; variationCarrierNonempty =
        true
    ; variationCarrierNonemptyIsTrue =
        refl
    ; actionScalarCarrierNonempty =
        true
    ; actionScalarCarrierNonemptyIsTrue =
        refl
    ; strictPairingCalculated =
        true
    ; strictPairingCalculatedIsTrue =
        refl
    ; physicalVariationPairingPromoted =
        false
    ; physicalVariationPairingPromotedIsFalse =
        refl
    ; strictYMPromoted =
        false
    ; strictYMPromotedIsFalse =
        refl
    ; rowIndex =
        canonicalStrictSelectedHodgeVariationPairingRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        7
    ; rowCountIs7 =
        refl
    ; calculationBoundary =
        "Selected Hodge-to-dual carrier is computed by applying sfgcSelectedHodgeStarLowerCandidate and wrapping the result in YMSFGCUserSuppliedDualCurvatureCarrier"
        ∷ "A selected current carrier is computed from the selected dual-curvature carrier, giving a definitional selected D * F equals selected-current law"
        ∷ "YMSFGCUserSuppliedVariationCarrier is inhabited by a finite GaugeField wrapper"
        ∷ "YMSFGCUserSuppliedActionScalarCarrier is inhabited by an integer action-scalar wrapper"
        ∷ "The selected finite variation law closes as zero action variation equals zero Euler-Lagrange pairing plus zero boundary term"
        ∷ "This is the selected finite instance, not the generic quantified IBP request over arbitrary functions"
        ∷ "Sourced Euler-Lagrange D * F = J, physical Yang-Mills, Clay, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedHodgeVariationPairingRowCountIs7 :
  listCount canonicalStrictSelectedHodgeVariationPairingRows ≡ 7
canonicalStrictSelectedHodgeVariationPairingRowCountIs7 =
  refl

canonicalStrictSelectedHodgeVariationPairingCalculated :
  StrictSelectedHodgeVariationPairingCalculation.strictPairingCalculated
    canonicalStrictSelectedHodgeVariationPairingCalculation
  ≡
  true
canonicalStrictSelectedHodgeVariationPairingCalculated =
  refl

canonicalStrictSelectedHodgeVariationPairingPhysicalPromotionFalse :
  StrictSelectedHodgeVariationPairingCalculation.physicalVariationPairingPromoted
    canonicalStrictSelectedHodgeVariationPairingCalculation
  ≡
  false
canonicalStrictSelectedHodgeVariationPairingPhysicalPromotionFalse =
  refl

canonicalStrictSelectedHodgeVariationPairingYMPromotionFalse :
  StrictSelectedHodgeVariationPairingCalculation.strictYMPromoted
    canonicalStrictSelectedHodgeVariationPairingCalculation
  ≡
  false
canonicalStrictSelectedHodgeVariationPairingYMPromotionFalse =
  refl
