module DASHI.Promotion.YMStrictHodgeVariationBlockerIndex where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YM
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as StrictPairing

------------------------------------------------------------------------
-- Strict Hodge/variation blocker index.
--
-- This receipt is intentionally disjoint from the large obstruction module.
-- It records the strongest currently inhabited finite Route-B evidence and
-- consumes the strict selected-Hodge variation calculation.  The strict
-- pairing function type is now inhabited vacuously; non-vacuous selected
-- action variation remains blocked.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YMStrictHodgeVariationRow : Set where
  pureZeroCurrentDStarFEqualsJFiniteRow :
    YMStrictHodgeVariationRow

  finiteDiscreteIBPLowerLawRow :
    YMStrictHodgeVariationRow

  strictSelectedHodgeVariationBlockerRow :
    YMStrictHodgeVariationRow

  vacuousStrictSelectedHodgeVariationCalculatedRow :
    YMStrictHodgeVariationRow

  nonPromotingBoundaryRow :
    YMStrictHodgeVariationRow

canonicalYMStrictHodgeVariationRows :
  List YMStrictHodgeVariationRow
canonicalYMStrictHodgeVariationRows =
  pureZeroCurrentDStarFEqualsJFiniteRow
  ∷ finiteDiscreteIBPLowerLawRow
  ∷ strictSelectedHodgeVariationBlockerRow
  ∷ vacuousStrictSelectedHodgeVariationCalculatedRow
  ∷ nonPromotingBoundaryRow
  ∷ []

record YMStrictHodgeVariationBlockerIndex : Set₁ where
  field
    pureZeroCurrentFiniteSurface :
      YM.YMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface

    pureZeroCurrentFiniteSurfaceIsCanonical :
      pureZeroCurrentFiniteSurface
      ≡
      YM.canonicalYMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface

    pureZeroCurrentSupply :
      YM.YMSFGCDiscreteHodgeCovariantDerivativePrimitiveSupply

    pureZeroCurrentSupplyIsCanonical :
      pureZeroCurrentSupply
      ≡
      YM.canonicalYMSFGCPureZeroCurrentDiscreteHodgeCovariantDerivativeSupply

    pureZeroCurrentDStarFEqualsJLawIsCanonical :
      YM.YMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface.pureDStarFEqualsZeroCurrentLaw
        YM.canonicalYMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface
      ≡
      YM.sfgcPureZeroDStarFEqualsJLaw

    finiteIBPLowerCandidate :
      YM.YMSFGCDiscreteVariationIBPLowerCandidate

    finiteIBPLowerCandidateIsCanonical :
      finiteIBPLowerCandidate
      ≡
      YM.canonicalYMSFGCDiscreteVariationIBPLowerCandidate

    finiteIBPLowerLawIsCanonical :
      YM.YMSFGCDiscreteVariationIBPLowerCandidate.zeroIBPLaw
        YM.canonicalYMSFGCDiscreteVariationIBPLowerCandidate
      ≡
      YM.sfgcZeroDiscreteVariationIBPLaw

    strictSelectedHodgeVariationPairingCalculation :
      StrictPairing.StrictSelectedHodgeVariationPairingCalculation

    strictSelectedHodgeVariationPairingCalculationIsCanonical :
      strictSelectedHodgeVariationPairingCalculation
      ≡
      StrictPairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    vacuousStrictPairingCalculated :
      Bool

    vacuousStrictPairingCalculatedIsTrue :
      vacuousStrictPairingCalculated ≡ true

    exactStrictVariationBlocker :
      YM.YangMillsVariationalEquationMissingPrimitive

    exactStrictVariationBlockerIsMissingSelectedHodgePairing :
      exactStrictVariationBlocker
      ≡
      YM.missingVariationPairingForSelectedHodgeStar

    pureZeroCurrentDStarFEqualsJInhabited :
      Bool

    pureZeroCurrentDStarFEqualsJInhabitedIsTrue :
      pureZeroCurrentDStarFEqualsJInhabited ≡ true

    finiteIBPLowerLawInhabited :
      Bool

    finiteIBPLowerLawInhabitedIsTrue :
      finiteIBPLowerLawInhabited ≡ true

    strictVariationPairingPromoted :
      Bool

    strictVariationPairingPromotedIsFalse :
      strictVariationPairingPromoted ≡ false

    strictYMPromoted :
      Bool

    strictYMPromotedIsFalse :
      strictYMPromoted ≡ false

    rowIndex :
      List YMStrictHodgeVariationRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalYMStrictHodgeVariationRows

    rowCount :
      Nat

    rowCountIs5 :
      rowCount ≡ 5

    receiptBoundary :
      List String

open YMStrictHodgeVariationBlockerIndex public

canonicalYMStrictHodgeVariationBlockerIndex :
  YMStrictHodgeVariationBlockerIndex
canonicalYMStrictHodgeVariationBlockerIndex =
  record
    { pureZeroCurrentFiniteSurface =
        YM.canonicalYMSFGCPureZeroCurrentDStarFEqualsJFiniteSurface
    ; pureZeroCurrentFiniteSurfaceIsCanonical =
        refl
    ; pureZeroCurrentSupply =
        YM.canonicalYMSFGCPureZeroCurrentDiscreteHodgeCovariantDerivativeSupply
    ; pureZeroCurrentSupplyIsCanonical =
        refl
    ; pureZeroCurrentDStarFEqualsJLawIsCanonical =
        refl
    ; finiteIBPLowerCandidate =
        YM.canonicalYMSFGCDiscreteVariationIBPLowerCandidate
    ; finiteIBPLowerCandidateIsCanonical =
        refl
    ; finiteIBPLowerLawIsCanonical =
        refl
    ; strictSelectedHodgeVariationPairingCalculation =
        StrictPairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; strictSelectedHodgeVariationPairingCalculationIsCanonical =
        refl
    ; vacuousStrictPairingCalculated =
        true
    ; vacuousStrictPairingCalculatedIsTrue =
        refl
    ; exactStrictVariationBlocker =
        YM.missingVariationPairingForSelectedHodgeStar
    ; exactStrictVariationBlockerIsMissingSelectedHodgePairing =
        refl
    ; pureZeroCurrentDStarFEqualsJInhabited =
        true
    ; pureZeroCurrentDStarFEqualsJInhabitedIsTrue =
        refl
    ; finiteIBPLowerLawInhabited =
        true
    ; finiteIBPLowerLawInhabitedIsTrue =
        refl
    ; strictVariationPairingPromoted =
        false
    ; strictVariationPairingPromotedIsFalse =
        refl
    ; strictYMPromoted =
        false
    ; strictYMPromotedIsFalse =
        refl
    ; rowIndex =
        canonicalYMStrictHodgeVariationRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        5
    ; rowCountIs5 =
        refl
    ; receiptBoundary =
        "Inhabited: Gate 3 pure-YM finite carrier-level D * F = J with J = 0, via the canonical zero-current supply"
        ∷ "Inhabited: finite discrete IBP lower law, where zero variation splits as zero Euler-Lagrange pairing plus zero boundary term"
        ∷ "Calculated: the strict selected-Hodge variation pairing function type is inhabited by empty elimination over YMSFGCUserSuppliedVariationCarrier"
        ∷ "Still blocked: non-vacuous selected action variation and non-empty user variation/action-scalar carriers are not supplied"
        ∷ "Non-promoting: this receipt does not assert strict D * F = J, physical Yang-Mills, continuum mass gap, Clay, or terminal unification"
        ∷ []
    }

canonicalYMStrictHodgeVariationRowCountIs5 :
  listCount canonicalYMStrictHodgeVariationRows ≡ 5
canonicalYMStrictHodgeVariationRowCountIs5 =
  refl

canonicalYMStrictHodgeVariationPureZeroCurrentIsInhabited :
  YMStrictHodgeVariationBlockerIndex.pureZeroCurrentDStarFEqualsJInhabited
    canonicalYMStrictHodgeVariationBlockerIndex
  ≡
  true
canonicalYMStrictHodgeVariationPureZeroCurrentIsInhabited =
  refl

canonicalYMStrictHodgeVariationFiniteIBPIsInhabited :
  YMStrictHodgeVariationBlockerIndex.finiteIBPLowerLawInhabited
    canonicalYMStrictHodgeVariationBlockerIndex
  ≡
  true
canonicalYMStrictHodgeVariationFiniteIBPIsInhabited =
  refl

canonicalYMStrictHodgeVariationVacuousPairingCalculated :
  YMStrictHodgeVariationBlockerIndex.vacuousStrictPairingCalculated
    canonicalYMStrictHodgeVariationBlockerIndex
  ≡
  true
canonicalYMStrictHodgeVariationVacuousPairingCalculated =
  refl

canonicalYMStrictHodgeVariationBlockerIsExact :
  YMStrictHodgeVariationBlockerIndex.exactStrictVariationBlocker
    canonicalYMStrictHodgeVariationBlockerIndex
  ≡
  YM.missingVariationPairingForSelectedHodgeStar
canonicalYMStrictHodgeVariationBlockerIsExact =
  refl

canonicalYMStrictHodgeVariationDoesNotPromote :
  YMStrictHodgeVariationBlockerIndex.strictYMPromoted
    canonicalYMStrictHodgeVariationBlockerIndex
  ≡
  false
canonicalYMStrictHodgeVariationDoesNotPromote =
  refl
