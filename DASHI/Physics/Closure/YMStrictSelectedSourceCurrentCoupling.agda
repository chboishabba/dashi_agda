module DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.HodgeVariationPairingDepth9 as HV9
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMStrictSelectedHodgeVariationPairing as Pairing
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC

------------------------------------------------------------------------
-- Strict selected source-current coupling.
--
-- This module consumes the selected finite Hodge/current calculation and
-- makes the next coupling explicit: for each user-supplied non-flat
-- connection, the selected current source is the selected covariant derivative
-- of the selected Hodge-dual curvature at the reference plaquette.  The law is
-- definitional on the finite carrier.  It is not a physical matter current,
-- not a sourced Euler-Lagrange equation, and not a Yang-Mills/Clay promotion.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedSourceCurrentCouplingStatus : Set where
  strictSelectedFiniteSourceCurrentCoupledPhysicalYMBlocked :
    StrictSelectedSourceCurrentCouplingStatus

data StrictSelectedSourceCurrentCouplingRow : Set where
  selectedHodgeCarrierConsumedRow :
    StrictSelectedSourceCurrentCouplingRow

  selectedDualCurvatureSourceRow :
    StrictSelectedSourceCurrentCouplingRow

  selectedCovariantDerivativeTargetRow :
    StrictSelectedSourceCurrentCouplingRow

  selectedCurrentSourceRow :
    StrictSelectedSourceCurrentCouplingRow

  selectedEquationTargetLawRow :
    StrictSelectedSourceCurrentCouplingRow

  depth9AndVariationPairingConsumedRow :
    StrictSelectedSourceCurrentCouplingRow

  physicalMatterSourceBlockedRow :
    StrictSelectedSourceCurrentCouplingRow

  promotionGuardsFalseRow :
    StrictSelectedSourceCurrentCouplingRow

canonicalStrictSelectedSourceCurrentCouplingRows :
  List StrictSelectedSourceCurrentCouplingRow
canonicalStrictSelectedSourceCurrentCouplingRows =
  selectedHodgeCarrierConsumedRow
  ∷ selectedDualCurvatureSourceRow
  ∷ selectedCovariantDerivativeTargetRow
  ∷ selectedCurrentSourceRow
  ∷ selectedEquationTargetLawRow
  ∷ depth9AndVariationPairingConsumedRow
  ∷ physicalMatterSourceBlockedRow
  ∷ promotionGuardsFalseRow
  ∷ []

strictSelectedSourceFieldStrength :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  SFGC.SFGCSite2DFieldStrengthBridge
strictSelectedSourceFieldStrength connection =
  YMObs.ymSFGCUserSuppliedConnectionCurvature
    connection
    YMObs.sfgcReferencePlaquette

strictSelectedSourceDualCurvature :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
strictSelectedSourceDualCurvature connection =
  Pairing.strictSelectedHodgeStarToDual
    (strictSelectedSourceFieldStrength connection)

strictSelectedSourceDualCurvatureIsSelectedHodge :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
    (strictSelectedSourceDualCurvature connection)
  ≡
  YMObs.sfgcSelectedHodgeStarLowerCandidate
    (strictSelectedSourceFieldStrength connection)
strictSelectedSourceDualCurvatureIsSelectedHodge connection =
  refl

strictSelectedEquationTarget :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
strictSelectedEquationTarget connection =
  Pairing.strictSelectedCovariantDerivativeOnDual
    connection
    (strictSelectedSourceDualCurvature connection)

strictSelectedCurrentSource :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
strictSelectedCurrentSource connection =
  Pairing.strictSelectedCurrentFromDerivative
    connection
    (strictSelectedSourceDualCurvature connection)

strictSelectedEquationTargetEqualsCurrentSource :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  strictSelectedEquationTarget connection
  ≡
  strictSelectedCurrentSource connection
strictSelectedEquationTargetEqualsCurrentSource connection =
  refl

strictSelectedReferenceSourceDualCurvature :
  YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
strictSelectedReferenceSourceDualCurvature =
  strictSelectedSourceDualCurvature
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

strictSelectedReferenceEquationTarget :
  YMObs.YMSFGCUserSuppliedCurrentCarrier
strictSelectedReferenceEquationTarget =
  strictSelectedEquationTarget
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

strictSelectedReferenceCurrentSource :
  YMObs.YMSFGCUserSuppliedCurrentCarrier
strictSelectedReferenceCurrentSource =
  strictSelectedCurrentSource
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

strictSelectedReferenceEquationTargetEqualsCurrentSource :
  strictSelectedReferenceEquationTarget
  ≡
  strictSelectedReferenceCurrentSource
strictSelectedReferenceEquationTargetEqualsCurrentSource =
  refl

record StrictSelectedSourceCurrentCouplingReceipt : Set₁ where
  field
    status :
      StrictSelectedSourceCurrentCouplingStatus

    consumedDepth9Receipt :
      HV9.HodgeVariationPairingDepth9Receipt

    consumedDepth9ReceiptIsCanonical :
      consumedDepth9Receipt
      ≡
      HV9.canonicalHodgeVariationPairingDepth9Receipt

    consumedStrictSelectedPairing :
      Pairing.StrictSelectedHodgeVariationPairingCalculation

    consumedStrictSelectedPairingIsCanonical :
      consumedStrictSelectedPairing
      ≡
      Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation

    selectedHodgeStar :
      SFGC.SFGCSite2DFieldStrengthBridge →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    selectedHodgeStarIsStrictPairingHodge :
      selectedHodgeStar
      ≡
      Pairing.strictSelectedHodgeStarToDual

    selectedDualCurvatureSource :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    selectedDualCurvatureSourceIsSelectedHodge :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      YMObs.ymSFGCUserSuppliedDualCurvatureFieldStrength
        (selectedDualCurvatureSource connection)
      ≡
      YMObs.sfgcSelectedHodgeStarLowerCandidate
        (strictSelectedSourceFieldStrength connection)

    covariantDerivativeOnSelectedDual :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    covariantDerivativeOnSelectedDualIsStrict :
      covariantDerivativeOnSelectedDual
      ≡
      Pairing.strictSelectedCovariantDerivativeOnDual

    sourceCurrent :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    sourceCurrentIsSelectedDerivative :
      sourceCurrent
      ≡
      strictSelectedCurrentSource

    equationTarget :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    equationTargetIsSelectedDerivative :
      equationTarget
      ≡
      strictSelectedEquationTarget

    selectedDStarFEqualsCurrentSource :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      equationTarget connection
      ≡
      sourceCurrent connection

    referenceDualCurvature :
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    referenceEquationTarget :
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    referenceCurrentSource :
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    referenceEquationTargetEqualsCurrentSource :
      referenceEquationTarget
      ≡
      referenceCurrentSource

    dualCurvatureCarrier :
      Set

    dualCurvatureCarrierIsUserSupplied :
      dualCurvatureCarrier
      ≡
      YMObs.YMSFGCUserSuppliedDualCurvatureCarrier

    currentCarrier :
      Set

    currentCarrierIsUserSupplied :
      currentCarrier
      ≡
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    finiteSourceCurrentCoupled :
      Bool

    finiteSourceCurrentCoupledIsTrue :
      finiteSourceCurrentCoupled ≡ true

    exactMatterSourceBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterSourceBlockerIsCurrentSourceCouplingToMatter :
      exactMatterSourceBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

    exactPhysicalDStarFBlocker :
      YMObs.YangMillsFieldEquationMissingPrerequisite

    exactPhysicalDStarFBlockerIsDStarFEqualsJ :
      exactPhysicalDStarFBlocker
      ≡
      YMObs.missingDStarFEqualsJLaw

    physicalMatterSourcePromoted :
      Bool

    physicalMatterSourcePromotedIsFalse :
      physicalMatterSourcePromoted ≡ false

    physicalSourcedYangMillsPromoted :
      Bool

    physicalSourcedYangMillsPromotedIsFalse :
      physicalSourcedYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    rowIndex :
      List StrictSelectedSourceCurrentCouplingRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedSourceCurrentCouplingRows

    rowCount :
      Nat

    rowCountIs8 :
      rowCount ≡ 8

    receiptBoundary :
      List String

open StrictSelectedSourceCurrentCouplingReceipt public

canonicalStrictSelectedSourceCurrentCouplingReceipt :
  StrictSelectedSourceCurrentCouplingReceipt
canonicalStrictSelectedSourceCurrentCouplingReceipt =
  record
    { status =
        strictSelectedFiniteSourceCurrentCoupledPhysicalYMBlocked
    ; consumedDepth9Receipt =
        HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; consumedDepth9ReceiptIsCanonical =
        refl
    ; consumedStrictSelectedPairing =
        Pairing.canonicalStrictSelectedHodgeVariationPairingCalculation
    ; consumedStrictSelectedPairingIsCanonical =
        refl
    ; selectedHodgeStar =
        Pairing.strictSelectedHodgeStarToDual
    ; selectedHodgeStarIsStrictPairingHodge =
        refl
    ; selectedDualCurvatureSource =
        strictSelectedSourceDualCurvature
    ; selectedDualCurvatureSourceIsSelectedHodge =
        strictSelectedSourceDualCurvatureIsSelectedHodge
    ; covariantDerivativeOnSelectedDual =
        Pairing.strictSelectedCovariantDerivativeOnDual
    ; covariantDerivativeOnSelectedDualIsStrict =
        refl
    ; sourceCurrent =
        strictSelectedCurrentSource
    ; sourceCurrentIsSelectedDerivative =
        refl
    ; equationTarget =
        strictSelectedEquationTarget
    ; equationTargetIsSelectedDerivative =
        refl
    ; selectedDStarFEqualsCurrentSource =
        strictSelectedEquationTargetEqualsCurrentSource
    ; referenceDualCurvature =
        strictSelectedReferenceSourceDualCurvature
    ; referenceEquationTarget =
        strictSelectedReferenceEquationTarget
    ; referenceCurrentSource =
        strictSelectedReferenceCurrentSource
    ; referenceEquationTargetEqualsCurrentSource =
        strictSelectedReferenceEquationTargetEqualsCurrentSource
    ; dualCurvatureCarrier =
        YMObs.YMSFGCUserSuppliedDualCurvatureCarrier
    ; dualCurvatureCarrierIsUserSupplied =
        refl
    ; currentCarrier =
        YMObs.YMSFGCUserSuppliedCurrentCarrier
    ; currentCarrierIsUserSupplied =
        refl
    ; finiteSourceCurrentCoupled =
        true
    ; finiteSourceCurrentCoupledIsTrue =
        refl
    ; exactMatterSourceBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterSourceBlockerIsCurrentSourceCouplingToMatter =
        refl
    ; exactPhysicalDStarFBlocker =
        YMObs.missingDStarFEqualsJLaw
    ; exactPhysicalDStarFBlockerIsDStarFEqualsJ =
        refl
    ; physicalMatterSourcePromoted =
        false
    ; physicalMatterSourcePromotedIsFalse =
        refl
    ; physicalSourcedYangMillsPromoted =
        false
    ; physicalSourcedYangMillsPromotedIsFalse =
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
        canonicalStrictSelectedSourceCurrentCouplingRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        8
    ; rowCountIs8 =
        refl
    ; receiptBoundary =
        "Consumes the depth-9 Hodge variation receipt and strict selected Hodge variation pairing calculation"
        ∷ "The selected dual-curvature source is obtained by applying the strict selected Hodge wrapper to the connection curvature at sfgcReferencePlaquette"
        ∷ "The selected equation target is the strict selected covariant derivative on that selected dual-curvature carrier"
        ∷ "The selected source current is definitionally the same selected derivative current, so the finite D * F equals selected current law is refl-backed"
        ∷ "This is a finite selected carrier coupling, not a physical matter-current coupling"
        ∷ "The exact matter blocker remains missingCurrentSourceCouplingToMatter and the physical D * F = J blocker remains missingDStarFEqualsJLaw"
        ∷ "Physical sourced Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedSourceCurrentCouplingRowCountIs8 :
  listCount canonicalStrictSelectedSourceCurrentCouplingRows ≡ 8
canonicalStrictSelectedSourceCurrentCouplingRowCountIs8 =
  refl

canonicalStrictSelectedSourceCurrentCouplingCalculated :
  StrictSelectedSourceCurrentCouplingReceipt.finiteSourceCurrentCoupled
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  true
canonicalStrictSelectedSourceCurrentCouplingCalculated =
  refl

canonicalStrictSelectedSourceCurrentCouplingPhysicalMatterSourceFalse :
  StrictSelectedSourceCurrentCouplingReceipt.physicalMatterSourcePromoted
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  false
canonicalStrictSelectedSourceCurrentCouplingPhysicalMatterSourceFalse =
  refl

canonicalStrictSelectedSourceCurrentCouplingPhysicalYMSourcedFalse :
  StrictSelectedSourceCurrentCouplingReceipt.physicalSourcedYangMillsPromoted
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  false
canonicalStrictSelectedSourceCurrentCouplingPhysicalYMSourcedFalse =
  refl

canonicalStrictSelectedSourceCurrentCouplingClayYMFalse :
  StrictSelectedSourceCurrentCouplingReceipt.clayYangMillsPromoted
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  false
canonicalStrictSelectedSourceCurrentCouplingClayYMFalse =
  refl

canonicalStrictSelectedSourceCurrentCouplingTerminalFalse :
  StrictSelectedSourceCurrentCouplingReceipt.terminalPromotion
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  false
canonicalStrictSelectedSourceCurrentCouplingTerminalFalse =
  refl

canonicalStrictSelectedSourceCurrentCouplingMatterBlockerExact :
  StrictSelectedSourceCurrentCouplingReceipt.exactMatterSourceBlocker
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  YMObs.missingCurrentSourceCouplingToMatter
canonicalStrictSelectedSourceCurrentCouplingMatterBlockerExact =
  refl

canonicalStrictSelectedSourceCurrentCouplingDStarFBlockerExact :
  StrictSelectedSourceCurrentCouplingReceipt.exactPhysicalDStarFBlocker
    canonicalStrictSelectedSourceCurrentCouplingReceipt
  ≡
  YMObs.missingDStarFEqualsJLaw
canonicalStrictSelectedSourceCurrentCouplingDStarFBlockerExact =
  refl
