module DASHI.Physics.Closure.FiniteGaugeHodgeAdjointCompatibility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BTFiniteHodgeEffectiveActionTheoremBoundary as BTAction
import DASHI.Physics.Closure.BTFiniteHodgeStarObligation as BTHodge
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as Pairing
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Finite gauge/Hodge adjoint compatibility boundary.
--
-- This module records the next finite Hodge/effective-action compatibility
-- target after the BT finite Hodge-star obligation and the finite
-- effective-action theorem boundary.  It packages the weighted pairing,
-- selected finite Hodge star, formal adjoint target
--
--   < d_A alpha , beta > = < alpha , +/- * d_A * beta > + boundary
--
-- and a compatibility-defect carrier.  The selected finite IBP law is
-- consumed from YMStrictSelectedHodgeVariationPairing, but the genuine metric
-- Hodge adjointness proof on weighted BT cells remains open.  All promotion
-- flags remain false.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data FiniteGaugeHodgeAdjointCompatibilityStatus : Set where
  finiteSelectedAdjointCompatibilityBoundaryNamedPromotionBlocked :
    FiniteGaugeHodgeAdjointCompatibilityStatus

data FiniteGaugeHodgeAdjointCompatibilityRow : Set where
  btFiniteHodgeStarObligationConsumedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  btEffectiveActionBoundaryConsumedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  strictSelectedHodgeVariationPairingConsumedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  weightedPairingCarrierNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  finiteHodgeStarCarrierNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  covariantDerivativeCarrierNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  formalAdjointOperatorNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  adjointnessIdentityTargetNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  boundaryTermCarrierNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  compatibilityDefectCarrierNamedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  selectedFiniteIBPLawConsumedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  metricWeightedAdjointProofStillBlockedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  realDStarFEqualsJStillBlockedRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

  promotionGuardsFalseRow :
    FiniteGaugeHodgeAdjointCompatibilityRow

canonicalFiniteGaugeHodgeAdjointCompatibilityRows :
  List FiniteGaugeHodgeAdjointCompatibilityRow
canonicalFiniteGaugeHodgeAdjointCompatibilityRows =
  btFiniteHodgeStarObligationConsumedRow
  ∷ btEffectiveActionBoundaryConsumedRow
  ∷ strictSelectedHodgeVariationPairingConsumedRow
  ∷ weightedPairingCarrierNamedRow
  ∷ finiteHodgeStarCarrierNamedRow
  ∷ covariantDerivativeCarrierNamedRow
  ∷ formalAdjointOperatorNamedRow
  ∷ adjointnessIdentityTargetNamedRow
  ∷ boundaryTermCarrierNamedRow
  ∷ compatibilityDefectCarrierNamedRow
  ∷ selectedFiniteIBPLawConsumedRow
  ∷ metricWeightedAdjointProofStillBlockedRow
  ∷ realDStarFEqualsJStillBlockedRow
  ∷ promotionGuardsFalseRow
  ∷ []

data FiniteGaugeHodgeCompatibilityBlocker : Set where
  weightedBTMetricPairingMissing :
    FiniteGaugeHodgeCompatibilityBlocker

  selectedHodgeNotMetricHodgeStar :
    FiniteGaugeHodgeCompatibilityBlocker

  formalAdjointNotProvedForWeightedCells :
    FiniteGaugeHodgeCompatibilityBlocker

  compatibilityDefectNotShownZero :
    FiniteGaugeHodgeCompatibilityBlocker

  physicalMatterCurrentCouplingMissing :
    FiniteGaugeHodgeCompatibilityBlocker

  realDStarFEqualsJLawMissing :
    FiniteGaugeHodgeCompatibilityBlocker

canonicalFiniteGaugeHodgeCompatibilityBlockers :
  List FiniteGaugeHodgeCompatibilityBlocker
canonicalFiniteGaugeHodgeCompatibilityBlockers =
  weightedBTMetricPairingMissing
  ∷ selectedHodgeNotMetricHodgeStar
  ∷ formalAdjointNotProvedForWeightedCells
  ∷ compatibilityDefectNotShownZero
  ∷ physicalMatterCurrentCouplingMissing
  ∷ realDStarFEqualsJLawMissing
  ∷ []

data FiniteAdjointFailClosedGate : Set where
  selectedIBPOnlyGate :
    FiniteAdjointFailClosedGate

  metricPairingIdentificationGate :
    FiniteAdjointFailClosedGate

  formalAdjointEqualityGate :
    FiniteAdjointFailClosedGate

  defectZeroGate :
    FiniteAdjointFailClosedGate

  fieldEquationPromotionGate :
    FiniteAdjointFailClosedGate

canonicalFiniteAdjointFailClosedGates :
  List FiniteAdjointFailClosedGate
canonicalFiniteAdjointFailClosedGates =
  selectedIBPOnlyGate
  ∷ metricPairingIdentificationGate
  ∷ formalAdjointEqualityGate
  ∷ defectZeroGate
  ∷ fieldEquationPromotionGate
  ∷ []

data FiniteAdjointReceiptSupport : Set where
  selectedBTWeightAndPairingSupport :
    FiniteAdjointReceiptSupport

  selectedHodgeCarrierSupport :
    FiniteAdjointReceiptSupport

  selectedConnectionCarrierSupport :
    FiniteAdjointReceiptSupport

  selectedBoundaryTermSupport :
    FiniteAdjointReceiptSupport

  selectedDiscreteIBPLawSupport :
    FiniteAdjointReceiptSupport

canonicalFiniteAdjointReceiptSupport :
  List FiniteAdjointReceiptSupport
canonicalFiniteAdjointReceiptSupport =
  selectedBTWeightAndPairingSupport
  ∷ selectedHodgeCarrierSupport
  ∷ selectedConnectionCarrierSupport
  ∷ selectedBoundaryTermSupport
  ∷ selectedDiscreteIBPLawSupport
  ∷ []

record FiniteAdjointFailClosedLedger : Set where
  constructor mkFiniteAdjointFailClosedLedger
  field
    supportRows :
      List FiniteAdjointReceiptSupport
    supportRowsAreCanonical :
      supportRows ≡ canonicalFiniteAdjointReceiptSupport
    supportRowCount :
      Nat
    supportRowCountIs5 :
      supportRowCount ≡ 5
    gates :
      List FiniteAdjointFailClosedGate
    gatesAreCanonical :
      gates ≡ canonicalFiniteAdjointFailClosedGates
    gateCount :
      Nat
    gateCountIs5 :
      gateCount ≡ 5
    selectedFiniteIBPRecorded :
      Bool
    selectedFiniteIBPRecordedIsTrue :
      selectedFiniteIBPRecorded ≡ true
    metricBTAdjointnessClosed :
      Bool
    metricBTAdjointnessClosedIsFalse :
      metricBTAdjointnessClosed ≡ false
    compatibilityDefectClosed :
      Bool
    compatibilityDefectClosedIsFalse :
      compatibilityDefectClosed ≡ false
    fieldEquationPromotedFromLedger :
      Bool
    fieldEquationPromotedFromLedgerIsFalse :
      fieldEquationPromotedFromLedger ≡ false

open FiniteAdjointFailClosedLedger public

canonicalFiniteAdjointFailClosedLedger :
  FiniteAdjointFailClosedLedger
canonicalFiniteAdjointFailClosedLedger =
  mkFiniteAdjointFailClosedLedger
    canonicalFiniteAdjointReceiptSupport
    refl
    5
    refl
    canonicalFiniteAdjointFailClosedGates
    refl
    5
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

data WeightedFinitePairing : Set where
  weightedFinitePairingFromBTObligation :
    BTHodge.BTCellWeight →
    BTHodge.BTFinitePairingCarrier →
    WeightedFinitePairing

data FiniteGaugeHodgeStar : Set where
  finiteGaugeHodgeStarFromSelectedBTBoundary :
    BTAction.BTFiniteHodgeStarCarrier →
    FiniteGaugeHodgeStar

data FiniteGaugeCovariantDerivative : Set where
  finiteGaugeCovariantDerivativeFromSelectedConnection :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    FiniteGaugeCovariantDerivative

data FiniteGaugeFormalAdjoint : Set where
  finiteGaugeFormalAdjointFromSelectedHodge :
    FiniteGaugeHodgeStar →
    FiniteGaugeFormalAdjoint

data FiniteGaugeBoundaryTerm : Set where
  finiteGaugeBoundaryTermFromSelectedVariation :
    YMObs.YMSFGCUserSuppliedActionScalarCarrier →
    FiniteGaugeBoundaryTerm

data FiniteGaugeAdjointnessIdentityTarget : Set where
  finiteGaugeAdjointnessIdentityTarget :
    WeightedFinitePairing →
    FiniteGaugeCovariantDerivative →
    FiniteGaugeFormalAdjoint →
    FiniteGaugeBoundaryTerm →
    FiniteGaugeAdjointnessIdentityTarget

data FiniteGaugeHodgeCompatibilityDefect : Set where
  finiteGaugeHodgeCompatibilityDefect :
    FiniteGaugeAdjointnessIdentityTarget →
    FiniteGaugeHodgeCompatibilityDefect

canonicalWeightedFinitePairing :
  WeightedFinitePairing
canonicalWeightedFinitePairing =
  weightedFinitePairingFromBTObligation
    (BTHodge.BTFiniteHodgeStarObligation.selectedCellWeight
      BTHodge.canonicalBTFiniteHodgeStarObligation)
    (BTHodge.BTFiniteHodgeStarObligation.finitePairingTarget
      BTHodge.canonicalBTFiniteHodgeStarObligation)

canonicalFiniteGaugeHodgeStar :
  FiniteGaugeHodgeStar
canonicalFiniteGaugeHodgeStar =
  finiteGaugeHodgeStarFromSelectedBTBoundary
    BTAction.canonicalBTFiniteHodgeStar

canonicalFiniteGaugeCovariantDerivative :
  FiniteGaugeCovariantDerivative
canonicalFiniteGaugeCovariantDerivative =
  finiteGaugeCovariantDerivativeFromSelectedConnection
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

canonicalFiniteGaugeFormalAdjoint :
  FiniteGaugeFormalAdjoint
canonicalFiniteGaugeFormalAdjoint =
  finiteGaugeFormalAdjointFromSelectedHodge
    canonicalFiniteGaugeHodgeStar

canonicalFiniteGaugeBoundaryTerm :
  FiniteGaugeBoundaryTerm
canonicalFiniteGaugeBoundaryTerm =
  finiteGaugeBoundaryTermFromSelectedVariation
    (Pairing.strictSelectedBoundaryTerm
      YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection
      (YMObs.ymSFGCUserSuppliedVariationFromGaugeField
        SFGC.vacuumGaugeField))

canonicalFiniteGaugeAdjointnessIdentityTarget :
  FiniteGaugeAdjointnessIdentityTarget
canonicalFiniteGaugeAdjointnessIdentityTarget =
  finiteGaugeAdjointnessIdentityTarget
    canonicalWeightedFinitePairing
    canonicalFiniteGaugeCovariantDerivative
    canonicalFiniteGaugeFormalAdjoint
    canonicalFiniteGaugeBoundaryTerm

canonicalFiniteGaugeHodgeCompatibilityDefect :
  FiniteGaugeHodgeCompatibilityDefect
canonicalFiniteGaugeHodgeCompatibilityDefect =
  finiteGaugeHodgeCompatibilityDefect
    canonicalFiniteGaugeAdjointnessIdentityTarget

finiteGaugeSelectedIBPLaw :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  (variation : YMObs.YMSFGCUserSuppliedVariationCarrier) →
  Pairing.strictSelectedActionVariation connection variation
  ≡
  Pairing.strictActionScalarCombine
    (Pairing.strictSelectedHodgeVariationPairing connection variation)
    (Pairing.strictSelectedBoundaryTerm connection variation)
finiteGaugeSelectedIBPLaw =
  Pairing.strictSelectedDiscreteIBPLaw

record FiniteGaugeHodgeAdjointCompatibility : Set₂ where
  field
    status :
      FiniteGaugeHodgeAdjointCompatibilityStatus

    consumedBTFiniteHodgeStarObligation :
      BTHodge.BTFiniteHodgeStarObligation

    consumedBTFiniteHodgeStarObligationIsCanonical :
      consumedBTFiniteHodgeStarObligation
      ≡
      BTHodge.canonicalBTFiniteHodgeStarObligation

    consumedBTFiniteHodgeEffectiveActionBoundary :
      BTAction.BTFiniteHodgeEffectiveActionTheoremBoundary

    consumedBTFiniteHodgeEffectiveActionBoundaryIsCanonical :
      consumedBTFiniteHodgeEffectiveActionBoundary
      ≡
      BTAction.canonicalBTFiniteHodgeEffectiveActionTheoremBoundary

    consumedStrictSelectedHodgeVariationPairing :
      Pairing.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictSelectedHodgeVariationPairingIsCanonical :
      consumedStrictSelectedHodgeVariationPairing
      ≡
      Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    weightedPairing :
      WeightedFinitePairing

    weightedPairingIsCanonical :
      weightedPairing ≡ canonicalWeightedFinitePairing

    finiteHodgeStar :
      FiniteGaugeHodgeStar

    finiteHodgeStarIsCanonical :
      finiteHodgeStar ≡ canonicalFiniteGaugeHodgeStar

    covariantDerivative :
      FiniteGaugeCovariantDerivative

    covariantDerivativeIsCanonical :
      covariantDerivative ≡ canonicalFiniteGaugeCovariantDerivative

    formalAdjoint :
      FiniteGaugeFormalAdjoint

    formalAdjointIsCanonical :
      formalAdjoint ≡ canonicalFiniteGaugeFormalAdjoint

    adjointnessIdentityTarget :
      FiniteGaugeAdjointnessIdentityTarget

    adjointnessIdentityTargetIsCanonical :
      adjointnessIdentityTarget
      ≡
      canonicalFiniteGaugeAdjointnessIdentityTarget

    boundaryTerm :
      FiniteGaugeBoundaryTerm

    boundaryTermIsCanonical :
      boundaryTerm ≡ canonicalFiniteGaugeBoundaryTerm

    compatibilityDefect :
      FiniteGaugeHodgeCompatibilityDefect

    compatibilityDefectIsCanonical :
      compatibilityDefect ≡ canonicalFiniteGaugeHodgeCompatibilityDefect

    selectedFiniteIBPLaw :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      (variation : YMObs.YMSFGCUserSuppliedVariationCarrier) →
      Pairing.strictSelectedActionVariation connection variation
      ≡
      Pairing.strictActionScalarCombine
        (Pairing.strictSelectedHodgeVariationPairing connection variation)
        (Pairing.strictSelectedBoundaryTerm connection variation)

    selectedFiniteIBPLawIsCanonical :
      selectedFiniteIBPLaw ≡ finiteGaugeSelectedIBPLaw

    weightedPairingTargetNamed :
      Bool

    weightedPairingTargetNamedIsTrue :
      weightedPairingTargetNamed ≡ true

    finiteHodgeStarTargetNamed :
      Bool

    finiteHodgeStarTargetNamedIsTrue :
      finiteHodgeStarTargetNamed ≡ true

    adjointnessIdentityTargetNamed :
      Bool

    adjointnessIdentityTargetNamedIsTrue :
      adjointnessIdentityTargetNamed ≡ true

    compatibilityDefectTargetNamed :
      Bool

    compatibilityDefectTargetNamedIsTrue :
      compatibilityDefectTargetNamed ≡ true

    compatibilityDefectZeroProved :
      Bool

    compatibilityDefectZeroProvedIsFalse :
      compatibilityDefectZeroProved ≡ false

    metricWeightedAdjointnessPromoted :
      Bool

    metricWeightedAdjointnessPromotedIsFalse :
      metricWeightedAdjointnessPromoted ≡ false

    exactBlockers :
      List FiniteGaugeHodgeCompatibilityBlocker

    exactBlockersAreCanonical :
      exactBlockers
      ≡
      canonicalFiniteGaugeHodgeCompatibilityBlockers

    exactBlockerCount :
      Nat

    exactBlockerCountIs6 :
      exactBlockerCount ≡ 6

    failClosedLedger :
      FiniteAdjointFailClosedLedger

    failClosedLedgerIsCanonical :
      failClosedLedger ≡ canonicalFiniteAdjointFailClosedLedger

    failClosedLedgerSupportRowCount :
      supportRowCount failClosedLedger ≡ 5

    failClosedLedgerGateCount :
      gateCount failClosedLedger ≡ 5

    failClosedLedgerMetricAdjointFalse :
      metricBTAdjointnessClosed failClosedLedger ≡ false

    failClosedLedgerDefectFalse :
      compatibilityDefectClosed failClosedLedger ≡ false

    failClosedLedgerFieldEquationFalse :
      fieldEquationPromotedFromLedger failClosedLedger ≡ false

    rows :
      List FiniteGaugeHodgeAdjointCompatibilityRow

    rowsAreCanonical :
      rows ≡ canonicalFiniteGaugeHodgeAdjointCompatibilityRows

    rowCount :
      Nat

    rowCountIs14 :
      rowCount ≡ 14

    maxwellPromoted :
      Bool

    maxwellPromotedIsFalse :
      maxwellPromoted ≡ false

    yangMillsPromoted :
      Bool

    yangMillsPromotedIsFalse :
      yangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    compatibilityBoundary :
      List String

open FiniteGaugeHodgeAdjointCompatibility public

canonicalFiniteGaugeHodgeAdjointCompatibility :
  FiniteGaugeHodgeAdjointCompatibility
canonicalFiniteGaugeHodgeAdjointCompatibility =
  record
    { status =
        finiteSelectedAdjointCompatibilityBoundaryNamedPromotionBlocked
    ; consumedBTFiniteHodgeStarObligation =
        BTHodge.canonicalBTFiniteHodgeStarObligation
    ; consumedBTFiniteHodgeStarObligationIsCanonical =
        refl
    ; consumedBTFiniteHodgeEffectiveActionBoundary =
        BTAction.canonicalBTFiniteHodgeEffectiveActionTheoremBoundary
    ; consumedBTFiniteHodgeEffectiveActionBoundaryIsCanonical =
        refl
    ; consumedStrictSelectedHodgeVariationPairing =
        Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictSelectedHodgeVariationPairingIsCanonical =
        refl
    ; weightedPairing =
        canonicalWeightedFinitePairing
    ; weightedPairingIsCanonical =
        refl
    ; finiteHodgeStar =
        canonicalFiniteGaugeHodgeStar
    ; finiteHodgeStarIsCanonical =
        refl
    ; covariantDerivative =
        canonicalFiniteGaugeCovariantDerivative
    ; covariantDerivativeIsCanonical =
        refl
    ; formalAdjoint =
        canonicalFiniteGaugeFormalAdjoint
    ; formalAdjointIsCanonical =
        refl
    ; adjointnessIdentityTarget =
        canonicalFiniteGaugeAdjointnessIdentityTarget
    ; adjointnessIdentityTargetIsCanonical =
        refl
    ; boundaryTerm =
        canonicalFiniteGaugeBoundaryTerm
    ; boundaryTermIsCanonical =
        refl
    ; compatibilityDefect =
        canonicalFiniteGaugeHodgeCompatibilityDefect
    ; compatibilityDefectIsCanonical =
        refl
    ; selectedFiniteIBPLaw =
        finiteGaugeSelectedIBPLaw
    ; selectedFiniteIBPLawIsCanonical =
        refl
    ; weightedPairingTargetNamed =
        true
    ; weightedPairingTargetNamedIsTrue =
        refl
    ; finiteHodgeStarTargetNamed =
        true
    ; finiteHodgeStarTargetNamedIsTrue =
        refl
    ; adjointnessIdentityTargetNamed =
        true
    ; adjointnessIdentityTargetNamedIsTrue =
        refl
    ; compatibilityDefectTargetNamed =
        true
    ; compatibilityDefectTargetNamedIsTrue =
        refl
    ; compatibilityDefectZeroProved =
        false
    ; compatibilityDefectZeroProvedIsFalse =
        refl
    ; metricWeightedAdjointnessPromoted =
        false
    ; metricWeightedAdjointnessPromotedIsFalse =
        refl
    ; exactBlockers =
        canonicalFiniteGaugeHodgeCompatibilityBlockers
    ; exactBlockersAreCanonical =
        refl
    ; exactBlockerCount =
        6
    ; exactBlockerCountIs6 =
        refl
    ; failClosedLedger =
        canonicalFiniteAdjointFailClosedLedger
    ; failClosedLedgerIsCanonical =
        refl
    ; failClosedLedgerSupportRowCount =
        refl
    ; failClosedLedgerGateCount =
        refl
    ; failClosedLedgerMetricAdjointFalse =
        refl
    ; failClosedLedgerDefectFalse =
        refl
    ; failClosedLedgerFieldEquationFalse =
        refl
    ; rows =
        canonicalFiniteGaugeHodgeAdjointCompatibilityRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        14
    ; rowCountIs14 =
        refl
    ; maxwellPromoted =
        false
    ; maxwellPromotedIsFalse =
        refl
    ; yangMillsPromoted =
        false
    ; yangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; compatibilityBoundary =
        "Consumes canonicalBTFiniteHodgeStarObligation, canonicalBTFiniteHodgeEffectiveActionTheoremBoundary, and canonicalStrictSelectedHodgeVariationPairingCalculation"
        ∷ "Names weighted finite pairing from the BT Hodge obligation cell weight and pairing target"
        ∷ "Names finite Hodge star from the BT effective-action boundary selected Hodge carrier"
        ∷ "Names the formal adjoint target <d_A alpha,beta> = <alpha,+/- * d_A * beta> + boundary"
        ∷ "Consumes the selected finite IBP law, but does not prove metric weighted adjointness on BT primal/dual cells"
        ∷ "Fail-closed ledger records five supports and five gates: selected IBP only, metric pairing identification, formal adjoint equality, defect zero, and field-equation promotion"
        ∷ "Compatibility defect is named but not shown zero"
        ∷ "Maxwell, Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalFiniteGaugeHodgeAdjointCompatibilityRowCountIs14 :
  listCount canonicalFiniteGaugeHodgeAdjointCompatibilityRows ≡ 14
canonicalFiniteGaugeHodgeAdjointCompatibilityRowCountIs14 =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityBlockerCountIs6 :
  listCount canonicalFiniteGaugeHodgeCompatibilityBlockers ≡ 6
canonicalFiniteGaugeHodgeAdjointCompatibilityBlockerCountIs6 =
  refl

canonicalFiniteAdjointFailClosedLedgerSupportCountIs5 :
  listCount canonicalFiniteAdjointReceiptSupport ≡ 5
canonicalFiniteAdjointFailClosedLedgerSupportCountIs5 =
  refl

canonicalFiniteAdjointFailClosedLedgerGateCountIs5 :
  listCount canonicalFiniteAdjointFailClosedGates ≡ 5
canonicalFiniteAdjointFailClosedLedgerGateCountIs5 =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityLedgerMetricFalse :
  metricBTAdjointnessClosed
    (failClosedLedger canonicalFiniteGaugeHodgeAdjointCompatibility)
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityLedgerMetricFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityLedgerDefectFalse :
  compatibilityDefectClosed
    (failClosedLedger canonicalFiniteGaugeHodgeAdjointCompatibility)
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityLedgerDefectFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityLedgerFieldEquationFalse :
  fieldEquationPromotedFromLedger
    (failClosedLedger canonicalFiniteGaugeHodgeAdjointCompatibility)
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityLedgerFieldEquationFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityDefectFalse :
  compatibilityDefectZeroProved
    canonicalFiniteGaugeHodgeAdjointCompatibility
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityDefectFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityMetricAdjointFalse :
  metricWeightedAdjointnessPromoted
    canonicalFiniteGaugeHodgeAdjointCompatibility
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityMetricAdjointFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityMaxwellFalse :
  maxwellPromoted
    canonicalFiniteGaugeHodgeAdjointCompatibility
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityMaxwellFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityYMFalse :
  yangMillsPromoted
    canonicalFiniteGaugeHodgeAdjointCompatibility
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityYMFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityClayYMFalse :
  clayYangMillsPromoted
    canonicalFiniteGaugeHodgeAdjointCompatibility
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityClayYMFalse =
  refl

canonicalFiniteGaugeHodgeAdjointCompatibilityTerminalFalse :
  terminalPromotion
    canonicalFiniteGaugeHodgeAdjointCompatibility
  ≡
  false
canonicalFiniteGaugeHodgeAdjointCompatibilityTerminalFalse =
  refl
