module DASHI.Physics.Closure.YMStrictSelectedNonzeroActionVariation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_) renaming (_+_ to _+ℤ_)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as Pairing
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Strict selected nonzero action variation.
--
-- The previous selected-Hodge calculation closes the zero finite IBP law
-- over the user-supplied variation/action-scalar carriers.  This module
-- takes the next finite step without changing the physical claim surface:
-- it constructs a selected nonzero action-scalar payload, a reference
-- non-vacuum variation, and a definitional local variation split
--
--   δS_selected = EL_selected + boundary_selected
--
-- where δS_selected has integer payload +1, EL_selected has payload +0, and
-- boundary_selected has payload +1.  This is still only a selected finite
-- arithmetic surface; it is not a physical sourced Yang-Mills equation, not a
-- continuum mass-gap theorem, and not a Clay promotion.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedNonzeroActionVariationStatus : Set where
  strictSelectedNonzeroFiniteActionVariationCalculatedPhysicalYMBlocked :
    StrictSelectedNonzeroActionVariationStatus

data StrictSelectedNonzeroActionVariationRow : Set where
  consumedStrictSelectedPairingRow :
    StrictSelectedNonzeroActionVariationRow

  referenceNonzeroVariationRow :
    StrictSelectedNonzeroActionVariationRow

  nonzeroActionScalarPayloadRow :
    StrictSelectedNonzeroActionVariationRow

  selectedNonzeroVariationSplitRow :
    StrictSelectedNonzeroActionVariationRow

  selectedNonzeroIBPLawRow :
    StrictSelectedNonzeroActionVariationRow

  physicalPromotionBlockedRow :
    StrictSelectedNonzeroActionVariationRow

canonicalStrictSelectedNonzeroActionVariationRows :
  List StrictSelectedNonzeroActionVariationRow
canonicalStrictSelectedNonzeroActionVariationRows =
  consumedStrictSelectedPairingRow
  ∷ referenceNonzeroVariationRow
  ∷ nonzeroActionScalarPayloadRow
  ∷ selectedNonzeroVariationSplitRow
  ∷ selectedNonzeroIBPLawRow
  ∷ physicalPromotionBlockedRow
  ∷ []

strictSelectedNonzeroGaugeField :
  SFGC.GaugeField
strictSelectedNonzeroGaugeField site =
  SPTI4.φ1

strictSelectedNonzeroGaugeFieldAtStart :
  strictSelectedNonzeroGaugeField SPTI.shiftStartPoint
  ≡
  SPTI4.φ1
strictSelectedNonzeroGaugeFieldAtStart =
  refl

strictSelectedNonzeroVariation :
  YMObs.YMSFGCUserSuppliedVariationCarrier
strictSelectedNonzeroVariation =
  YMObs.ymSFGCUserSuppliedVariationFromGaugeField
    strictSelectedNonzeroGaugeField

strictSelectedNonzeroVariationGaugeAtStart :
  YMObs.ymSFGCUserSuppliedVariationGaugeField
    strictSelectedNonzeroVariation
    SPTI.shiftStartPoint
  ≡
  SPTI4.φ1
strictSelectedNonzeroVariationGaugeAtStart =
  refl

strictSelectedZeroActionScalar :
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedZeroActionScalar =
  YMObs.ymSFGCUserSuppliedActionScalarFromInteger (+ 0)

strictSelectedNonzeroActionScalar :
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedNonzeroActionScalar =
  YMObs.ymSFGCUserSuppliedActionScalarFromInteger (+ 1)

strictSelectedNonzeroActionScalarPayloadIsOne :
  YMObs.ymSFGCUserSuppliedActionScalarInteger
    strictSelectedNonzeroActionScalar
  ≡
  + 1
strictSelectedNonzeroActionScalarPayloadIsOne =
  refl

strictSelectedNonzeroActionScalarCombine :
  YMObs.YMSFGCUserSuppliedActionScalarCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedNonzeroActionScalarCombine
  (YMObs.ymSFGCUserSuppliedActionScalarFromInteger left)
  (YMObs.ymSFGCUserSuppliedActionScalarFromInteger right) =
  YMObs.ymSFGCUserSuppliedActionScalarFromInteger (left +ℤ right)

strictSelectedNonzeroActionVariation :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedNonzeroActionVariation connection variation =
  strictSelectedNonzeroActionScalar

strictSelectedNonzeroEulerLagrangePairing :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedNonzeroEulerLagrangePairing connection variation =
  strictSelectedZeroActionScalar

strictSelectedNonzeroBoundaryTerm :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedNonzeroBoundaryTerm connection variation =
  strictSelectedNonzeroActionScalar

strictSelectedNonzeroIBPLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  strictSelectedNonzeroActionVariation connection δA
  ≡
  strictSelectedNonzeroActionScalarCombine
    (strictSelectedNonzeroEulerLagrangePairing connection δA)
    (strictSelectedNonzeroBoundaryTerm connection δA)
strictSelectedNonzeroIBPLaw connection δA =
  refl

strictSelectedReferenceNonzeroActionVariationPayload :
  YMObs.ymSFGCUserSuppliedActionScalarInteger
    (strictSelectedNonzeroActionVariation
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      strictSelectedNonzeroVariation)
  ≡
  + 1
strictSelectedReferenceNonzeroActionVariationPayload =
  refl

strictSelectedReferenceNonzeroBoundaryPayload :
  YMObs.ymSFGCUserSuppliedActionScalarInteger
    (strictSelectedNonzeroBoundaryTerm
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      strictSelectedNonzeroVariation)
  ≡
  + 1
strictSelectedReferenceNonzeroBoundaryPayload =
  refl

strictSelectedReferenceEulerLagrangePayloadZero :
  YMObs.ymSFGCUserSuppliedActionScalarInteger
    (strictSelectedNonzeroEulerLagrangePairing
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      strictSelectedNonzeroVariation)
  ≡
  + 0
strictSelectedReferenceEulerLagrangePayloadZero =
  refl

record StrictSelectedNonzeroActionVariationCalculation : Set₁ where
  field
    status :
      StrictSelectedNonzeroActionVariationStatus

    consumedStrictSelectedPairing :
      Pairing.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictSelectedPairingIsCanonical :
      consumedStrictSelectedPairing
      ≡
      Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    referenceConnection :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier

    referenceConnectionIsCanonical :
      referenceConnection
      ≡
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

    referenceVariation :
      YMObs.YMSFGCUserSuppliedVariationCarrier

    referenceVariationIsNonzeroGaugeWrapper :
      referenceVariation
      ≡
      strictSelectedNonzeroVariation

    referenceVariationGaugeAtStart :
      YMObs.ymSFGCUserSuppliedVariationGaugeField
        referenceVariation
        SPTI.shiftStartPoint
      ≡
      SPTI4.φ1

    nonzeroActionScalar :
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    nonzeroActionScalarPayloadIsOne :
      YMObs.ymSFGCUserSuppliedActionScalarInteger
        nonzeroActionScalar
      ≡
      + 1

    selectedActionVariation :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    selectedActionVariationIsNonzero :
      selectedActionVariation
      ≡
      strictSelectedNonzeroActionVariation

    selectedEulerLagrangePairing :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    selectedEulerLagrangePairingIsZero :
      selectedEulerLagrangePairing
      ≡
      strictSelectedNonzeroEulerLagrangePairing

    selectedBoundaryTerm :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    selectedBoundaryTermIsNonzero :
      selectedBoundaryTerm
      ≡
      strictSelectedNonzeroBoundaryTerm

    selectedActionScalarCombine :
      YMObs.YMSFGCUserSuppliedActionScalarCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier →
      YMObs.YMSFGCUserSuppliedActionScalarCarrier

    selectedActionScalarCombineIsIntegerSum :
      selectedActionScalarCombine
      ≡
      strictSelectedNonzeroActionScalarCombine

    selectedNonzeroIBPLawInReceipt :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      selectedActionVariation connection δA
      ≡
      selectedActionScalarCombine
        (selectedEulerLagrangePairing connection δA)
        (selectedBoundaryTerm connection δA)

    referenceActionVariationPayloadIsOne :
      YMObs.ymSFGCUserSuppliedActionScalarInteger
        (selectedActionVariation referenceConnection referenceVariation)
      ≡
      + 1

    referenceEulerLagrangePayloadIsZero :
      YMObs.ymSFGCUserSuppliedActionScalarInteger
        (selectedEulerLagrangePairing referenceConnection referenceVariation)
      ≡
      + 0

    referenceBoundaryPayloadIsOne :
      YMObs.ymSFGCUserSuppliedActionScalarInteger
        (selectedBoundaryTerm referenceConnection referenceVariation)
      ≡
      + 1

    nonzeroActionVariationCalculated :
      Bool

    nonzeroActionVariationCalculatedIsTrue :
      nonzeroActionVariationCalculated ≡ true

    physicalSourceYMPromoted :
      Bool

    physicalSourceYMPromotedIsFalse :
      physicalSourceYMPromoted ≡ false

    continuumMassGapPromoted :
      Bool

    continuumMassGapPromotedIsFalse :
      continuumMassGapPromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    rowIndex :
      List StrictSelectedNonzeroActionVariationRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedNonzeroActionVariationRows

    rowCount :
      Nat

    rowCountIs6 :
      rowCount ≡ 6

    calculationBoundary :
      List String

open StrictSelectedNonzeroActionVariationCalculation public

canonicalStrictSelectedNonzeroActionVariationCalculation :
  StrictSelectedNonzeroActionVariationCalculation
canonicalStrictSelectedNonzeroActionVariationCalculation =
  record
    { status =
        strictSelectedNonzeroFiniteActionVariationCalculatedPhysicalYMBlocked
    ; consumedStrictSelectedPairing =
        Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictSelectedPairingIsCanonical =
        refl
    ; referenceConnection =
        YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
    ; referenceConnectionIsCanonical =
        refl
    ; referenceVariation =
        strictSelectedNonzeroVariation
    ; referenceVariationIsNonzeroGaugeWrapper =
        refl
    ; referenceVariationGaugeAtStart =
        refl
    ; nonzeroActionScalar =
        strictSelectedNonzeroActionScalar
    ; nonzeroActionScalarPayloadIsOne =
        refl
    ; selectedActionVariation =
        strictSelectedNonzeroActionVariation
    ; selectedActionVariationIsNonzero =
        refl
    ; selectedEulerLagrangePairing =
        strictSelectedNonzeroEulerLagrangePairing
    ; selectedEulerLagrangePairingIsZero =
        refl
    ; selectedBoundaryTerm =
        strictSelectedNonzeroBoundaryTerm
    ; selectedBoundaryTermIsNonzero =
        refl
    ; selectedActionScalarCombine =
        strictSelectedNonzeroActionScalarCombine
    ; selectedActionScalarCombineIsIntegerSum =
        refl
    ; selectedNonzeroIBPLawInReceipt =
        strictSelectedNonzeroIBPLaw
    ; referenceActionVariationPayloadIsOne =
        refl
    ; referenceEulerLagrangePayloadIsZero =
        refl
    ; referenceBoundaryPayloadIsOne =
        refl
    ; nonzeroActionVariationCalculated =
        true
    ; nonzeroActionVariationCalculatedIsTrue =
        refl
    ; physicalSourceYMPromoted =
        false
    ; physicalSourceYMPromotedIsFalse =
        refl
    ; continuumMassGapPromoted =
        false
    ; continuumMassGapPromotedIsFalse =
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
        canonicalStrictSelectedNonzeroActionVariationRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        6
    ; rowCountIs6 =
        refl
    ; calculationBoundary =
        "Consumes the strict selected-Hodge variation pairing calculation as the zero-law predecessor"
        ∷ "Reference variation is a concrete GaugeField wrapper whose start-point phase is phi1"
        ∷ "Reference selected action variation has integer payload +1"
        ∷ "Selected split is finite arithmetic: delta S payload +1 equals EL payload +0 plus boundary payload +1"
        ∷ "The local combine operation is integer addition on the user-supplied action-scalar wrapper"
        ∷ "Physical/source Yang-Mills, continuum mass gap, Clay YM, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedNonzeroActionVariationRowCountIs6 :
  listCount canonicalStrictSelectedNonzeroActionVariationRows ≡ 6
canonicalStrictSelectedNonzeroActionVariationRowCountIs6 =
  refl

canonicalStrictSelectedNonzeroActionVariationCalculated :
  StrictSelectedNonzeroActionVariationCalculation.nonzeroActionVariationCalculated
    canonicalStrictSelectedNonzeroActionVariationCalculation
  ≡
  true
canonicalStrictSelectedNonzeroActionVariationCalculated =
  refl

canonicalStrictSelectedNonzeroActionVariationPayloadIsOne :
  StrictSelectedNonzeroActionVariationCalculation.referenceActionVariationPayloadIsOne
    canonicalStrictSelectedNonzeroActionVariationCalculation
  ≡
  refl
canonicalStrictSelectedNonzeroActionVariationPayloadIsOne =
  refl

canonicalStrictSelectedNonzeroActionVariationPhysicalSourceYMFalse :
  StrictSelectedNonzeroActionVariationCalculation.physicalSourceYMPromoted
    canonicalStrictSelectedNonzeroActionVariationCalculation
  ≡
  false
canonicalStrictSelectedNonzeroActionVariationPhysicalSourceYMFalse =
  refl

canonicalStrictSelectedNonzeroActionVariationClayYMFalse :
  StrictSelectedNonzeroActionVariationCalculation.clayYMPromoted
    canonicalStrictSelectedNonzeroActionVariationCalculation
  ≡
  false
canonicalStrictSelectedNonzeroActionVariationClayYMFalse =
  refl

canonicalStrictSelectedNonzeroActionVariationTerminalFalse :
  StrictSelectedNonzeroActionVariationCalculation.terminalPromotion
    canonicalStrictSelectedNonzeroActionVariationCalculation
  ≡
  false
canonicalStrictSelectedNonzeroActionVariationTerminalFalse =
  refl
