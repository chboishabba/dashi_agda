module DASHI.Physics.Closure.YMRealSourcedDStarFEquationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMFiniteSelectedPairingToRealCarrierBoundary as FiniteBoundary
import DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling as SourceCoupling

------------------------------------------------------------------------
-- Real sourced D * F = J boundary.
--
-- The strict selected source/current lane already calculates a finite selected
-- carrier law: selected D * F equals the selected current source.  The
-- finite-to-real boundary records that this evidence feeds the real carrier
-- boundary but does not construct the self-adjoint real YM Hamiltonian.  This
-- module packages the next exact boundary: the finite selected equation can be
-- re-expressed as a typed real-sourced equation target over boundary wrappers,
-- while the physical matter-current coupling and real D * F = J law remain
-- explicit missing primitives.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YMRealSourcedDStarFBoundaryStatus : Set where
  finiteSelectedDStarFCurrentReexpressedRealSourcedBoundaryBlocked :
    YMRealSourcedDStarFBoundaryStatus

data YMRealSourcedDStarFBoundaryRow : Set where
  strictSelectedSourceCurrentConsumedRow :
    YMRealSourcedDStarFBoundaryRow

  finiteSelectedToRealBoundaryConsumedRow :
    YMRealSourcedDStarFBoundaryRow

  selectedConnectionToRealBoundaryCarrierRow :
    YMRealSourcedDStarFBoundaryRow

  selectedDStarFTargetBoundaryRow :
    YMRealSourcedDStarFBoundaryRow

  selectedCurrentBoundaryRow :
    YMRealSourcedDStarFBoundaryRow

  finiteEquationReexpressedAsRealBoundaryRow :
    YMRealSourcedDStarFBoundaryRow

  matterCurrentCouplingBlockerRow :
    YMRealSourcedDStarFBoundaryRow

  realDStarFEqualsJBlockerRow :
    YMRealSourcedDStarFBoundaryRow

  promotionGuardsFalseRow :
    YMRealSourcedDStarFBoundaryRow

canonicalYMRealSourcedDStarFBoundaryRows :
  List YMRealSourcedDStarFBoundaryRow
canonicalYMRealSourcedDStarFBoundaryRows =
  strictSelectedSourceCurrentConsumedRow
  ∷ finiteSelectedToRealBoundaryConsumedRow
  ∷ selectedConnectionToRealBoundaryCarrierRow
  ∷ selectedDStarFTargetBoundaryRow
  ∷ selectedCurrentBoundaryRow
  ∷ finiteEquationReexpressedAsRealBoundaryRow
  ∷ matterCurrentCouplingBlockerRow
  ∷ realDStarFEqualsJBlockerRow
  ∷ promotionGuardsFalseRow
  ∷ []

data YMRealSourcedBoundaryCarrier : Set where
  realBoundaryFromSelectedConnection :
    YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
    YMRealSourcedBoundaryCarrier

data YMRealDStarFBoundaryTarget : Set where
  realDStarFBoundaryFromSelectedTarget :
    YMObs.YMSFGCUserSuppliedCurrentCarrier →
    YMRealDStarFBoundaryTarget

data YMRealMatterCurrentBoundary : Set where
  realMatterCurrentBoundaryFromSelectedCurrent :
    YMObs.YMSFGCUserSuppliedCurrentCarrier →
    YMRealMatterCurrentBoundary

realBoundaryConnection :
  YMRealSourcedBoundaryCarrier →
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier
realBoundaryConnection
  (realBoundaryFromSelectedConnection connection) =
  connection

realBoundaryDStarFTarget :
  YMRealSourcedBoundaryCarrier →
  YMRealDStarFBoundaryTarget
realBoundaryDStarFTarget carrier =
  realDStarFBoundaryFromSelectedTarget
    (SourceCoupling.strictSelectedEquationTarget
      (realBoundaryConnection carrier))

realBoundaryMatterCurrent :
  YMRealSourcedBoundaryCarrier →
  YMRealMatterCurrentBoundary
realBoundaryMatterCurrent carrier =
  realMatterCurrentBoundaryFromSelectedCurrent
    (SourceCoupling.strictSelectedCurrentSource
      (realBoundaryConnection carrier))

realBoundarySelectedDStarFEqualsSelectedCurrent :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  realDStarFBoundaryFromSelectedTarget
    (SourceCoupling.strictSelectedEquationTarget connection)
  ≡
  realDStarFBoundaryFromSelectedTarget
    (SourceCoupling.strictSelectedCurrentSource connection)
realBoundarySelectedDStarFEqualsSelectedCurrent connection =
  refl

canonicalRealSourcedBoundaryCarrier :
  YMRealSourcedBoundaryCarrier
canonicalRealSourcedBoundaryCarrier =
  realBoundaryFromSelectedConnection
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

canonicalRealSourcedDStarFTarget :
  YMRealDStarFBoundaryTarget
canonicalRealSourcedDStarFTarget =
  realBoundaryDStarFTarget canonicalRealSourcedBoundaryCarrier

canonicalRealSourcedMatterCurrent :
  YMRealMatterCurrentBoundary
canonicalRealSourcedMatterCurrent =
  realBoundaryMatterCurrent canonicalRealSourcedBoundaryCarrier

canonicalRealSourcedDStarFBoundaryEqualsSelectedCurrent :
  canonicalRealSourcedDStarFTarget
  ≡
  realDStarFBoundaryFromSelectedTarget
    SourceCoupling.strictSelectedReferenceCurrentSource
canonicalRealSourcedDStarFBoundaryEqualsSelectedCurrent =
  refl

record YMRealSourcedDStarFEquationBoundary : Set₁ where
  field
    status :
      YMRealSourcedDStarFBoundaryStatus

    consumedStrictSelectedSourceCurrentCoupling :
      SourceCoupling.StrictSelectedSourceCurrentCouplingReceipt

    consumedStrictSelectedSourceCurrentCouplingIsCanonical :
      consumedStrictSelectedSourceCurrentCoupling
      ≡
      SourceCoupling.canonicalStrictSelectedSourceCurrentCouplingReceipt

    consumedFiniteSelectedPairingToRealBoundary :
      FiniteBoundary.YMFiniteSelectedPairingToRealCarrierBoundary

    consumedFiniteSelectedPairingToRealBoundaryIsCanonical :
      consumedFiniteSelectedPairingToRealBoundary
      ≡
      FiniteBoundary.canonicalYMFiniteSelectedPairingToRealCarrierBoundary

    realBoundaryCarrier :
      Set

    realBoundaryCarrierIsSelectedWrapper :
      realBoundaryCarrier ≡ YMRealSourcedBoundaryCarrier

    realDStarFBoundaryTarget :
      Set

    realDStarFBoundaryTargetIsSelectedWrapper :
      realDStarFBoundaryTarget ≡ YMRealDStarFBoundaryTarget

    realMatterCurrentBoundary :
      Set

    realMatterCurrentBoundaryIsSelectedWrapper :
      realMatterCurrentBoundary ≡ YMRealMatterCurrentBoundary

    selectedConnectionToRealBoundary :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMRealSourcedBoundaryCarrier

    selectedConnectionToRealBoundaryIsCanonical :
      selectedConnectionToRealBoundary
      ≡
      realBoundaryFromSelectedConnection

    selectedDStarFTarget :
      YMRealSourcedBoundaryCarrier →
      YMRealDStarFBoundaryTarget

    selectedDStarFTargetIsCanonical :
      selectedDStarFTarget ≡ realBoundaryDStarFTarget

    selectedMatterCurrent :
      YMRealSourcedBoundaryCarrier →
      YMRealMatterCurrentBoundary

    selectedMatterCurrentIsCanonical :
      selectedMatterCurrent ≡ realBoundaryMatterCurrent

    selectedFiniteEquationReexpressedAtBoundary :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      realDStarFBoundaryFromSelectedTarget
        (SourceCoupling.strictSelectedEquationTarget connection)
      ≡
      realDStarFBoundaryFromSelectedTarget
        (SourceCoupling.strictSelectedCurrentSource connection)

    canonicalBoundaryCarrier :
      YMRealSourcedBoundaryCarrier

    canonicalBoundaryDStarFTarget :
      YMRealDStarFBoundaryTarget

    canonicalBoundaryMatterCurrent :
      YMRealMatterCurrentBoundary

    canonicalBoundaryDStarFTargetEqualsSelectedCurrent :
      canonicalBoundaryDStarFTarget
      ≡
      realDStarFBoundaryFromSelectedTarget
        SourceCoupling.strictSelectedReferenceCurrentSource

    finiteSelectedDStarFCurrentLawConsumed :
      Bool

    finiteSelectedDStarFCurrentLawConsumedIsTrue :
      finiteSelectedDStarFCurrentLawConsumed ≡ true

    finiteEvidenceFeedsRealBoundary :
      Bool

    finiteEvidenceFeedsRealBoundaryIsTrue :
      finiteEvidenceFeedsRealBoundary ≡ true

    realBoundaryEquationTargetTyped :
      Bool

    realBoundaryEquationTargetTypedIsTrue :
      realBoundaryEquationTargetTyped ≡ true

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

    strictYMPromoted :
      Bool

    strictYMPromotedIsFalse :
      strictYMPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    boundaryRows :
      List YMRealSourcedDStarFBoundaryRow

    boundaryRowsAreCanonical :
      boundaryRows ≡ canonicalYMRealSourcedDStarFBoundaryRows

    boundaryRowCount :
      Nat

    boundaryRowCountIs9 :
      boundaryRowCount ≡ 9

    boundary :
      List String

open YMRealSourcedDStarFEquationBoundary public

canonicalYMRealSourcedDStarFEquationBoundary :
  YMRealSourcedDStarFEquationBoundary
canonicalYMRealSourcedDStarFEquationBoundary =
  record
    { status =
        finiteSelectedDStarFCurrentReexpressedRealSourcedBoundaryBlocked
    ; consumedStrictSelectedSourceCurrentCoupling =
        SourceCoupling.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; consumedStrictSelectedSourceCurrentCouplingIsCanonical =
        refl
    ; consumedFiniteSelectedPairingToRealBoundary =
        FiniteBoundary.canonicalYMFiniteSelectedPairingToRealCarrierBoundary
    ; consumedFiniteSelectedPairingToRealBoundaryIsCanonical =
        refl
    ; realBoundaryCarrier =
        YMRealSourcedBoundaryCarrier
    ; realBoundaryCarrierIsSelectedWrapper =
        refl
    ; realDStarFBoundaryTarget =
        YMRealDStarFBoundaryTarget
    ; realDStarFBoundaryTargetIsSelectedWrapper =
        refl
    ; realMatterCurrentBoundary =
        YMRealMatterCurrentBoundary
    ; realMatterCurrentBoundaryIsSelectedWrapper =
        refl
    ; selectedConnectionToRealBoundary =
        realBoundaryFromSelectedConnection
    ; selectedConnectionToRealBoundaryIsCanonical =
        refl
    ; selectedDStarFTarget =
        realBoundaryDStarFTarget
    ; selectedDStarFTargetIsCanonical =
        refl
    ; selectedMatterCurrent =
        realBoundaryMatterCurrent
    ; selectedMatterCurrentIsCanonical =
        refl
    ; selectedFiniteEquationReexpressedAtBoundary =
        realBoundarySelectedDStarFEqualsSelectedCurrent
    ; canonicalBoundaryCarrier =
        canonicalRealSourcedBoundaryCarrier
    ; canonicalBoundaryDStarFTarget =
        canonicalRealSourcedDStarFTarget
    ; canonicalBoundaryMatterCurrent =
        canonicalRealSourcedMatterCurrent
    ; canonicalBoundaryDStarFTargetEqualsSelectedCurrent =
        refl
    ; finiteSelectedDStarFCurrentLawConsumed =
        true
    ; finiteSelectedDStarFCurrentLawConsumedIsTrue =
        refl
    ; finiteEvidenceFeedsRealBoundary =
        true
    ; finiteEvidenceFeedsRealBoundaryIsTrue =
        refl
    ; realBoundaryEquationTargetTyped =
        true
    ; realBoundaryEquationTargetTypedIsTrue =
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
    ; strictYMPromoted =
        false
    ; strictYMPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; boundaryRows =
        canonicalYMRealSourcedDStarFBoundaryRows
    ; boundaryRowsAreCanonical =
        refl
    ; boundaryRowCount =
        9
    ; boundaryRowCountIs9 =
        refl
    ; boundary =
        "Consumes canonicalStrictSelectedSourceCurrentCouplingReceipt and canonicalYMFiniteSelectedPairingToRealCarrierBoundary"
        ∷ "Re-expresses the finite selected D * F equals selected current law as a typed real-sourced boundary wrapper"
        ∷ "The boundary target is selected D * F on the reference connection, wrapped as YMRealDStarFBoundaryTarget"
        ∷ "The boundary current is the selected finite current, wrapped as YMRealMatterCurrentBoundary"
        ∷ "No physical matter source is coupled to the current wrapper"
        ∷ "The exact remaining matter blocker is missingCurrentSourceCouplingToMatter"
        ∷ "The exact remaining real sourced field-equation blocker is missingDStarFEqualsJLaw"
        ∷ "Physical real D * F = J, strict Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMRealSourcedDStarFBoundaryRowCountIs9 :
  listCount canonicalYMRealSourcedDStarFBoundaryRows ≡ 9
canonicalYMRealSourcedDStarFBoundaryRowCountIs9 =
  refl

canonicalYMRealSourcedDStarFBoundaryConsumesFiniteSelectedLaw :
  finiteSelectedDStarFCurrentLawConsumed
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  true
canonicalYMRealSourcedDStarFBoundaryConsumesFiniteSelectedLaw =
  refl

canonicalYMRealSourcedDStarFBoundaryEquationTargetTyped :
  realBoundaryEquationTargetTyped
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  true
canonicalYMRealSourcedDStarFBoundaryEquationTargetTyped =
  refl

canonicalYMRealSourcedDStarFMatterCurrentBlockerExact :
  exactMatterCurrentCouplingBlocker
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  YMObs.missingCurrentSourceCouplingToMatter
canonicalYMRealSourcedDStarFMatterCurrentBlockerExact =
  refl

canonicalYMRealSourcedDStarFEquationBlockerExact :
  exactRealDStarFEqualsJBlocker
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  YMObs.missingDStarFEqualsJLaw
canonicalYMRealSourcedDStarFEquationBlockerExact =
  refl

canonicalYMRealSourcedDStarFPhysicalMatterCurrentFalse :
  physicalMatterCurrentCoupled
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  false
canonicalYMRealSourcedDStarFPhysicalMatterCurrentFalse =
  refl

canonicalYMRealSourcedDStarFPhysicalEquationFalse :
  physicalRealDStarFEqualsJPromoted
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  false
canonicalYMRealSourcedDStarFPhysicalEquationFalse =
  refl

canonicalYMRealSourcedDStarFStrictYMFalse :
  strictYMPromoted
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  false
canonicalYMRealSourcedDStarFStrictYMFalse =
  refl

canonicalYMRealSourcedDStarFClayYMFalse :
  clayYangMillsPromoted
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  false
canonicalYMRealSourcedDStarFClayYMFalse =
  refl

canonicalYMRealSourcedDStarFTerminalFalse :
  terminalPromotion
    canonicalYMRealSourcedDStarFEquationBoundary
  ≡
  false
canonicalYMRealSourcedDStarFTerminalFalse =
  refl
