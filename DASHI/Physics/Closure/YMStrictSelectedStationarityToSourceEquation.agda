module DASHI.Physics.Closure.YMStrictSelectedStationarityToSourceEquation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMStrictSelectedBoundaryCancellationCriterion as IBP
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as Pairing
import DASHI.Physics.Closure.YMStrictSelectedNonzeroActionVariation as Nonzero
import DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling as Source

------------------------------------------------------------------------
-- Strict selected stationarity to sourced-equation reducer.
--
-- The existing strict selected package has two checked finite facts:
--
--   1. zero-boundary IBP reduces selected action variation to the selected
--      Euler-Lagrange pairing;
--   2. the selected current source is definitionally the selected covariant
--      derivative of the selected Hodge-dual curvature.
--
-- This module consumes both facts in one typed reducer.  It packages the
-- finite selected variational equation at a connection/variation together
-- with the selected D * F = J current law for the same connection.  The result
-- is still finite and selected: it does not identify a physical matter
-- current, does not prove the real D * F = J theorem, and does not construct
-- the self-adjoint YM Hamiltonian quotient.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedStationarityToSourceEquationStatus : Set where
  finiteSelectedStationarityReducesToSourcedEquationPhysicalYMBlocked :
    StrictSelectedStationarityToSourceEquationStatus

data StrictSelectedStationarityToSourceEquationRow : Set where
  strictSelectedPairingConsumedRow :
    StrictSelectedStationarityToSourceEquationRow

  zeroBoundaryIBPConsumedRow :
    StrictSelectedStationarityToSourceEquationRow

  sourceCurrentCouplingConsumedRow :
    StrictSelectedStationarityToSourceEquationRow

  stationarityHypothesisRow :
    StrictSelectedStationarityToSourceEquationRow

  eulerLagrangeZeroReductionRow :
    StrictSelectedStationarityToSourceEquationRow

  selectedDStarFEqualsCurrentRow :
    StrictSelectedStationarityToSourceEquationRow

  finiteVariationalSourcedEquationPackagedRow :
    StrictSelectedStationarityToSourceEquationRow

  physicalMatterAndRealEquationBlockedRow :
    StrictSelectedStationarityToSourceEquationRow

  hamiltonianQuotientBlockedRow :
    StrictSelectedStationarityToSourceEquationRow

  promotionGuardsFalseRow :
    StrictSelectedStationarityToSourceEquationRow

canonicalStrictSelectedStationarityToSourceEquationRows :
  List StrictSelectedStationarityToSourceEquationRow
canonicalStrictSelectedStationarityToSourceEquationRows =
  strictSelectedPairingConsumedRow
  ∷ zeroBoundaryIBPConsumedRow
  ∷ sourceCurrentCouplingConsumedRow
  ∷ stationarityHypothesisRow
  ∷ eulerLagrangeZeroReductionRow
  ∷ selectedDStarFEqualsCurrentRow
  ∷ finiteVariationalSourcedEquationPackagedRow
  ∷ physicalMatterAndRealEquationBlockedRow
  ∷ hamiltonianQuotientBlockedRow
  ∷ promotionGuardsFalseRow
  ∷ []

SelectedStationaryAt :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  Set
SelectedStationaryAt connection δA =
  Pairing.strictSelectedActionVariation connection δA
  ≡
  YMObs.ymSFGCUserSuppliedZeroActionScalar

SelectedEulerLagrangeZeroAt :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedVariationCarrier →
  Set
SelectedEulerLagrangeZeroAt connection δA =
  Pairing.strictSelectedHodgeVariationPairing connection δA
  ≡
  YMObs.ymSFGCUserSuppliedZeroActionScalar

selectedStationarityCanonical :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  SelectedStationaryAt connection δA
selectedStationarityCanonical connection δA =
  refl

selectedStationarityToEulerLagrangeZero :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  IBP.SelectedBoundaryClosedAt connection δA →
  SelectedStationaryAt connection δA →
  SelectedEulerLagrangeZeroAt connection δA
selectedStationarityToEulerLagrangeZero connection δA refl refl =
  refl

selectedStationarityToCurrentEquation :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  Source.strictSelectedEquationTarget connection
  ≡
  Source.strictSelectedCurrentSource connection
selectedStationarityToCurrentEquation connection =
  Source.strictSelectedEquationTargetEqualsCurrentSource connection

record StrictSelectedVariationalSourcedEquationAt
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier)
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) : Set where
  field
    boundaryClosed :
      IBP.SelectedBoundaryClosedAt connection δA

    stationary :
      SelectedStationaryAt connection δA

    actionVariationReducesToEulerLagrange :
      Pairing.strictSelectedActionVariation connection δA
      ≡
      Pairing.strictSelectedHodgeVariationPairing connection δA

    eulerLagrangePairingZero :
      SelectedEulerLagrangeZeroAt connection δA

    selectedDualCurvature :
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    selectedDualCurvatureIsHodgeOfConnectionCurvature :
      selectedDualCurvature
      ≡
      Source.strictSelectedSourceDualCurvature connection

    selectedDStarFEqualsCurrent :
      Source.strictSelectedEquationTarget connection
      ≡
      Source.strictSelectedCurrentSource connection

open StrictSelectedVariationalSourcedEquationAt public

strictSelectedVariationalSourcedEquationAt :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  StrictSelectedVariationalSourcedEquationAt connection δA
strictSelectedVariationalSourcedEquationAt connection δA =
  record
    { boundaryClosed =
        IBP.selectedBoundaryClosedCanonical connection δA
    ; stationary =
        selectedStationarityCanonical connection δA
    ; actionVariationReducesToEulerLagrange =
        IBP.selectedIBPWithCanonicalBoundaryIsEulerLagrange connection δA
    ; eulerLagrangePairingZero =
        selectedStationarityToEulerLagrangeZero
          connection
          δA
          (IBP.selectedBoundaryClosedCanonical connection δA)
          (selectedStationarityCanonical connection δA)
    ; selectedDualCurvature =
        Source.strictSelectedSourceDualCurvature connection
    ; selectedDualCurvatureIsHodgeOfConnectionCurvature =
        refl
    ; selectedDStarFEqualsCurrent =
        selectedStationarityToCurrentEquation connection
    }

canonicalStrictSelectedVariationalSourcedEquation :
  StrictSelectedVariationalSourcedEquationAt
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
    Nonzero.strictSelectedNonzeroVariation
canonicalStrictSelectedVariationalSourcedEquation =
  strictSelectedVariationalSourcedEquationAt
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
    Nonzero.strictSelectedNonzeroVariation

record StrictSelectedStationarityToSourceEquationReducer : Set₁ where
  field
    status :
      StrictSelectedStationarityToSourceEquationStatus

    consumedStrictSelectedPairing :
      Pairing.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictSelectedPairingIsCanonical :
      consumedStrictSelectedPairing
      ≡
      Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    consumedBoundaryCancellation :
      IBP.StrictSelectedBoundaryCancellationCriterion

    consumedBoundaryCancellationIsCanonical :
      consumedBoundaryCancellation
      ≡
      IBP.canonicalStrictSelectedBoundaryCancellationCriterion

    consumedSourceCurrentCoupling :
      Source.StrictSelectedSourceCurrentCouplingReceipt

    consumedSourceCurrentCouplingIsCanonical :
      consumedSourceCurrentCoupling
      ≡
      Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

    stationaryAt :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      Set

    stationaryAtIsSelected :
      stationaryAt ≡ SelectedStationaryAt

    eulerLagrangeZeroAt :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      Set

    eulerLagrangeZeroAtIsSelected :
      eulerLagrangeZeroAt ≡ SelectedEulerLagrangeZeroAt

    stationarityReducer :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      IBP.SelectedBoundaryClosedAt connection δA →
      SelectedStationaryAt connection δA →
      SelectedEulerLagrangeZeroAt connection δA

    selectedSourcedEquationAt :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedVariationCarrier →
      Set

    selectedSourcedEquationAtIsPackaged :
      selectedSourcedEquationAt
      ≡
      StrictSelectedVariationalSourcedEquationAt

    selectedSourcedEquationBuilder :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (δA : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      StrictSelectedVariationalSourcedEquationAt connection δA

    canonicalSelectedSourcedEquation :
      StrictSelectedVariationalSourcedEquationAt
        YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
        Nonzero.strictSelectedNonzeroVariation

    canonicalEulerLagrangePairingZero :
      eulerLagrangePairingZero canonicalSelectedSourcedEquation
      ≡
      refl

    canonicalSelectedDStarFEqualsCurrent :
      selectedDStarFEqualsCurrent canonicalSelectedSourcedEquation
      ≡
      refl

    finiteStationarityToSourcedEquationReduced :
      Bool

    finiteStationarityToSourcedEquationReducedIsTrue :
      finiteStationarityToSourcedEquationReduced ≡ true

    exactMatterCurrentCouplingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterCurrentCouplingBlockerIsMissingCurrentSourceCouplingToMatter :
      exactMatterCurrentCouplingBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

    exactRealDStarFEqualsJBlocker :
      YMObs.YangMillsFieldEquationMissingPrerequisite

    exactRealDStarFEqualsJBlockerIsMissingDStarFEqualsJLaw :
      exactRealDStarFEqualsJBlocker
      ≡
      YMObs.missingDStarFEqualsJLaw

    physicalMatterCurrentCoupled :
      Bool

    physicalMatterCurrentCoupledIsFalse :
      physicalMatterCurrentCoupled ≡ false

    physicalRealDStarFEqualsJPromoted :
      Bool

    physicalRealDStarFEqualsJPromotedIsFalse :
      physicalRealDStarFEqualsJPromoted ≡ false

    hamiltonianQuotientConstructed :
      Bool

    hamiltonianQuotientConstructedIsFalse :
      hamiltonianQuotientConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    rowIndex :
      List StrictSelectedStationarityToSourceEquationRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedStationarityToSourceEquationRows

    rowCount :
      Nat

    rowCountIs10 :
      rowCount ≡ 10

    reducerBoundary :
      List String

open StrictSelectedStationarityToSourceEquationReducer public

canonicalStrictSelectedStationarityToSourceEquationReducer :
  StrictSelectedStationarityToSourceEquationReducer
canonicalStrictSelectedStationarityToSourceEquationReducer =
  record
    { status =
        finiteSelectedStationarityReducesToSourcedEquationPhysicalYMBlocked
    ; consumedStrictSelectedPairing =
        Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictSelectedPairingIsCanonical =
        refl
    ; consumedBoundaryCancellation =
        IBP.canonicalStrictSelectedBoundaryCancellationCriterion
    ; consumedBoundaryCancellationIsCanonical =
        refl
    ; consumedSourceCurrentCoupling =
        Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; consumedSourceCurrentCouplingIsCanonical =
        refl
    ; stationaryAt =
        SelectedStationaryAt
    ; stationaryAtIsSelected =
        refl
    ; eulerLagrangeZeroAt =
        SelectedEulerLagrangeZeroAt
    ; eulerLagrangeZeroAtIsSelected =
        refl
    ; stationarityReducer =
        selectedStationarityToEulerLagrangeZero
    ; selectedSourcedEquationAt =
        StrictSelectedVariationalSourcedEquationAt
    ; selectedSourcedEquationAtIsPackaged =
        refl
    ; selectedSourcedEquationBuilder =
        strictSelectedVariationalSourcedEquationAt
    ; canonicalSelectedSourcedEquation =
        canonicalStrictSelectedVariationalSourcedEquation
    ; canonicalEulerLagrangePairingZero =
        refl
    ; canonicalSelectedDStarFEqualsCurrent =
        refl
    ; finiteStationarityToSourcedEquationReduced =
        true
    ; finiteStationarityToSourcedEquationReducedIsTrue =
        refl
    ; exactMatterCurrentCouplingBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterCurrentCouplingBlockerIsMissingCurrentSourceCouplingToMatter =
        refl
    ; exactRealDStarFEqualsJBlocker =
        YMObs.missingDStarFEqualsJLaw
    ; exactRealDStarFEqualsJBlockerIsMissingDStarFEqualsJLaw =
        refl
    ; physicalMatterCurrentCoupled =
        false
    ; physicalMatterCurrentCoupledIsFalse =
        refl
    ; physicalRealDStarFEqualsJPromoted =
        false
    ; physicalRealDStarFEqualsJPromotedIsFalse =
        refl
    ; hamiltonianQuotientConstructed =
        false
    ; hamiltonianQuotientConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; rowIndex =
        canonicalStrictSelectedStationarityToSourceEquationRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        10
    ; rowCountIs10 =
        refl
    ; reducerBoundary =
        "Consumes the strict selected Hodge variation pairing, zero-boundary IBP criterion, and strict selected source-current coupling receipts"
        ∷ "Defines selected stationarity as zero selected action variation on the finite user-supplied action-scalar carrier"
        ∷ "Under the selected zero-boundary hypothesis, stationarity reduces to zero selected Euler-Lagrange pairing"
        ∷ "Packages that variational reduction with the selected D * F equals selected-current source law for the same connection"
        ∷ "The selected dual curvature is still the Hodge wrapper of the selected connection curvature at the reference plaquette"
        ∷ "This closes a finite selected stationarity-to-source-equation reducer, not a physical matter-current interpretation"
        ∷ "The exact matter blocker remains missingCurrentSourceCouplingToMatter"
        ∷ "The exact real equation blocker remains missingDStarFEqualsJLaw"
        ∷ "The Hamiltonian quotient remains unconstructed"
        ∷ "Physical real D * F = J, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedStationarityToSourceEquationRowCountIs10 :
  listCount canonicalStrictSelectedStationarityToSourceEquationRows ≡ 10
canonicalStrictSelectedStationarityToSourceEquationRowCountIs10 =
  refl

canonicalStrictSelectedStationarityReducerClosed :
  finiteStationarityToSourcedEquationReduced
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  true
canonicalStrictSelectedStationarityReducerClosed =
  refl

canonicalStrictSelectedStationarityMatterBlockerExact :
  exactMatterCurrentCouplingBlocker
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  YMObs.missingCurrentSourceCouplingToMatter
canonicalStrictSelectedStationarityMatterBlockerExact =
  refl

canonicalStrictSelectedStationarityRealEquationBlockerExact :
  exactRealDStarFEqualsJBlocker
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  YMObs.missingDStarFEqualsJLaw
canonicalStrictSelectedStationarityRealEquationBlockerExact =
  refl

canonicalStrictSelectedStationarityPhysicalMatterFalse :
  physicalMatterCurrentCoupled
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  false
canonicalStrictSelectedStationarityPhysicalMatterFalse =
  refl

canonicalStrictSelectedStationarityPhysicalEquationFalse :
  physicalRealDStarFEqualsJPromoted
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  false
canonicalStrictSelectedStationarityPhysicalEquationFalse =
  refl

canonicalStrictSelectedStationarityHamiltonianQuotientFalse :
  hamiltonianQuotientConstructed
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  false
canonicalStrictSelectedStationarityHamiltonianQuotientFalse =
  refl

canonicalStrictSelectedStationarityClayYMFalse :
  clayYangMillsPromoted
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  false
canonicalStrictSelectedStationarityClayYMFalse =
  refl

canonicalStrictSelectedStationarityTerminalFalse :
  terminalPromotion
    canonicalStrictSelectedStationarityToSourceEquationReducer
  ≡
  false
canonicalStrictSelectedStationarityTerminalFalse =
  refl
