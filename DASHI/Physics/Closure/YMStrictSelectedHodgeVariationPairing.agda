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
-- The repo already has substantial Hodge-star/YM machinery.  The exact strict
-- requested variation type is also visible:
--
--   YMSFGCUserSuppliedNonFlatConnectionCarrier →
--   YMSFGCUserSuppliedVariationCarrier →
--   YMSFGCUserSuppliedActionScalarCarrier
--
-- At the current boundary, the variation and action-scalar carriers are empty
-- request carriers.  Therefore the strict function type and the requested
-- discrete IBP law are inhabited by empty elimination over the variation
-- argument.  This is a real type-theoretic calculation, but it is vacuous and
-- deliberately non-promoting.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedHodgeVariationPairingStatus : Set where
  vacuousStrictPairingCalculatedNonVacuousPhysicsBlocked :
    StrictSelectedHodgeVariationPairingStatus

data StrictSelectedHodgeVariationPairingRow : Set where
  selectedHodgeToDualCarrierRow :
    StrictSelectedHodgeVariationPairingRow

  selectedCovariantDerivativeToCurrentRow :
    StrictSelectedHodgeVariationPairingRow

  vacuousVariationPairingRow :
    StrictSelectedHodgeVariationPairingRow

  vacuousDiscreteIBPLawRow :
    StrictSelectedHodgeVariationPairingRow

  nonVacuousPromotionBlockedRow :
    StrictSelectedHodgeVariationPairingRow

canonicalStrictSelectedHodgeVariationPairingRows :
  List StrictSelectedHodgeVariationPairingRow
canonicalStrictSelectedHodgeVariationPairingRows =
  selectedHodgeToDualCarrierRow
  ∷ selectedCovariantDerivativeToCurrentRow
  ∷ vacuousVariationPairingRow
  ∷ vacuousDiscreteIBPLawRow
  ∷ nonVacuousPromotionBlockedRow
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
strictSelectedHodgeVariationPairing connection ()

strictSelectedActionVariation :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedActionVariation connection ()

strictSelectedBoundaryTerm :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictSelectedBoundaryTerm connection ()

strictActionScalarCombine :
  YMObs.YMSFGCUserSuppliedActionScalarCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier →
  YMObs.YMSFGCUserSuppliedActionScalarCarrier
strictActionScalarCombine ()

strictVacuousDiscreteIBPLaw :
  (variationOfAction :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMObs.YMSFGCUserSuppliedVariationCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (eulerLagrangePairing :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMObs.YMSFGCUserSuppliedVariationCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (boundaryTerm :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMObs.YMSFGCUserSuppliedVariationCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (combineActionScalar :
    YMObs.YMSFGCUserSuppliedActionScalarCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  variationOfAction connection δA
  ≡
  combineActionScalar
    (eulerLagrangePairing connection δA)
    (boundaryTerm connection δA)
strictVacuousDiscreteIBPLaw
  variationOfAction
  eulerLagrangePairing
  boundaryTerm
  combineActionScalar
  connection
  ()

strictVacuousDiscreteIBPLawIsRequestedType :
  (variationOfAction :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMObs.YMSFGCUserSuppliedVariationCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (eulerLagrangePairing :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMObs.YMSFGCUserSuppliedVariationCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (boundaryTerm :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMObs.YMSFGCUserSuppliedVariationCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (combineActionScalar :
    YMObs.YMSFGCUserSuppliedActionScalarCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier →
    YMObs.YMSFGCUserSuppliedActionScalarCarrier) →
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  variationOfAction connection δA
  ≡
  combineActionScalar
    (eulerLagrangePairing connection δA)
    (boundaryTerm connection δA)
strictVacuousDiscreteIBPLawIsRequestedType =
  strictVacuousDiscreteIBPLaw

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

    strictVariationPairingIsRequestedType :
      Set

    strictVariationPairingTypeMatchesRequest :
      strictVariationPairingIsRequestedType
      ≡
      (YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
       YMObs.YMSFGCUserSuppliedVariationCarrier →
       YMObs.YMSFGCUserSuppliedActionScalarCarrier)

    strictDiscreteIBPLaw :
      YMObs.YMSFGCUserSuppliedRealYMPrimitiveTypedRequest.requestedDiscreteIBPLawType
        YMObs.canonicalYMSFGCUserSuppliedRealYMPrimitiveTypedRequest

    strictDiscreteIBPLawIsVacuous :
      strictDiscreteIBPLaw ≡ strictVacuousDiscreteIBPLaw

    variationCarrierNonempty :
      Bool

    variationCarrierNonemptyIsFalse :
      variationCarrierNonempty ≡ false

    actionScalarCarrierNonempty :
      Bool

    actionScalarCarrierNonemptyIsFalse :
      actionScalarCarrierNonempty ≡ false

    strictPairingCalculated :
      Bool

    strictPairingCalculatedIsTrue :
      strictPairingCalculated ≡ true

    nonVacuousVariationPairingPromoted :
      Bool

    nonVacuousVariationPairingPromotedIsFalse :
      nonVacuousVariationPairingPromoted ≡ false

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

    rowCountIs5 :
      rowCount ≡ 5

    calculationBoundary :
      List String

open StrictSelectedHodgeVariationPairingCalculation public

canonicalStrictSelectedHodgeVariationPairingCalculation :
  StrictSelectedHodgeVariationPairingCalculation
canonicalStrictSelectedHodgeVariationPairingCalculation =
  record
    { status =
        vacuousStrictPairingCalculatedNonVacuousPhysicsBlocked
    ; consumedDepth9Pairing =
        HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; consumedDepth9PairingIsCanonical =
        refl
    ; consumedGate3VariationPairing =
        Gate3.canonicalVariationPairing
    ; consumedGate3VariationPairingIsCanonical =
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
    ; strictVariationPairingIsRequestedType =
        YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
        YMObs.YMSFGCUserSuppliedVariationCarrier →
        YMObs.YMSFGCUserSuppliedActionScalarCarrier
    ; strictVariationPairingTypeMatchesRequest =
        refl
    ; strictDiscreteIBPLaw =
        strictVacuousDiscreteIBPLaw
    ; strictDiscreteIBPLawIsVacuous =
        refl
    ; variationCarrierNonempty =
        false
    ; variationCarrierNonemptyIsFalse =
        refl
    ; actionScalarCarrierNonempty =
        false
    ; actionScalarCarrierNonemptyIsFalse =
        refl
    ; strictPairingCalculated =
        true
    ; strictPairingCalculatedIsTrue =
        refl
    ; nonVacuousVariationPairingPromoted =
        false
    ; nonVacuousVariationPairingPromotedIsFalse =
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
        5
    ; rowCountIs5 =
        refl
    ; calculationBoundary =
        "Selected Hodge-to-dual carrier is computed by applying sfgcSelectedHodgeStarLowerCandidate and wrapping the result in YMSFGCUserSuppliedDualCurvatureCarrier"
        ∷ "A selected current carrier is computed from the selected dual-curvature carrier, giving a definitional selected D * F equals selected-current law"
        ∷ "The strict requested variation pairing type is inhabited by empty elimination over YMSFGCUserSuppliedVariationCarrier"
        ∷ "The strict requested discrete IBP law is also inhabited by empty elimination over YMSFGCUserSuppliedVariationCarrier"
        ∷ "This calculation is vacuous because YMSFGCUserSuppliedVariationCarrier and YMSFGCUserSuppliedActionScalarCarrier still have no constructors"
        ∷ "Non-vacuous selected Hodge variation, sourced Euler-Lagrange D * F = J, strict Yang-Mills, Clay, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedHodgeVariationPairingRowCountIs5 :
  listCount canonicalStrictSelectedHodgeVariationPairingRows ≡ 5
canonicalStrictSelectedHodgeVariationPairingRowCountIs5 =
  refl

canonicalStrictSelectedHodgeVariationPairingCalculated :
  StrictSelectedHodgeVariationPairingCalculation.strictPairingCalculated
    canonicalStrictSelectedHodgeVariationPairingCalculation
  ≡
  true
canonicalStrictSelectedHodgeVariationPairingCalculated =
  refl

canonicalStrictSelectedHodgeVariationPairingNonVacuousPromotionFalse :
  StrictSelectedHodgeVariationPairingCalculation.nonVacuousVariationPairingPromoted
    canonicalStrictSelectedHodgeVariationPairingCalculation
  ≡
  false
canonicalStrictSelectedHodgeVariationPairingNonVacuousPromotionFalse =
  refl

canonicalStrictSelectedHodgeVariationPairingYMPromotionFalse :
  StrictSelectedHodgeVariationPairingCalculation.strictYMPromoted
    canonicalStrictSelectedHodgeVariationPairingCalculation
  ≡
  false
canonicalStrictSelectedHodgeVariationPairingYMPromotionFalse =
  refl
