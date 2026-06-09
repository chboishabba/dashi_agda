module DASHI.Physics.Closure.YMStrictSelectedMatterCurrentAuthorityBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling as Source

------------------------------------------------------------------------
-- Strict selected matter-current authority bridge.
--
-- The selected finite source-current coupling is now checked in
-- `YMStrictSelectedSourceCurrentCoupling`: D * F equals the selected current
-- source definitionally on the user-supplied finite carrier.  This module
-- packages the next boundary without promotion: the finite selected current
-- carrier is available as a matter-current target only after an accepted
-- authority token supplies a physical matter-current interpretation and a
-- coupling law.  The exact remaining blocker is
-- `missingCurrentSourceCouplingToMatter`.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data StrictSelectedMatterCurrentAuthorityStatus : Set where
  selectedFiniteCurrentPackagedMatterAuthorityMissing :
    StrictSelectedMatterCurrentAuthorityStatus

data StrictSelectedMatterCurrentAuthorityRow : Set where
  sourceCurrentReceiptConsumedRow :
    StrictSelectedMatterCurrentAuthorityRow

  selectedCurrentCarrierExposedRow :
    StrictSelectedMatterCurrentAuthorityRow

  selectedCurrentSourceExposedRow :
    StrictSelectedMatterCurrentAuthorityRow

  matterCurrentAuthorityBoundaryRow :
    StrictSelectedMatterCurrentAuthorityRow

  matterCurrentAuthorityTokenRequestedRow :
    StrictSelectedMatterCurrentAuthorityRow

  matterCouplingLawRequestedRow :
    StrictSelectedMatterCurrentAuthorityRow

  exactMatterCouplingBlockerRow :
    StrictSelectedMatterCurrentAuthorityRow

  promotionGuardsFalseRow :
    StrictSelectedMatterCurrentAuthorityRow

canonicalStrictSelectedMatterCurrentAuthorityRows :
  List StrictSelectedMatterCurrentAuthorityRow
canonicalStrictSelectedMatterCurrentAuthorityRows =
  sourceCurrentReceiptConsumedRow
  ∷ selectedCurrentCarrierExposedRow
  ∷ selectedCurrentSourceExposedRow
  ∷ matterCurrentAuthorityBoundaryRow
  ∷ matterCurrentAuthorityTokenRequestedRow
  ∷ matterCouplingLawRequestedRow
  ∷ exactMatterCouplingBlockerRow
  ∷ promotionGuardsFalseRow
  ∷ []

data MatterCurrentAuthorityTokenRequest : Set where
  requestAcceptedPhysicalMatterCurrentAuthorityToken :
    MatterCurrentAuthorityTokenRequest

data MatterCurrentAuthorityDecision : Set where
  matterCurrentAuthorityNotAccepted :
    MatterCurrentAuthorityDecision

data MatterCurrentCouplingLawRequest : Set where
  requestMatterCurrentToSelectedCurrentCarrierCouplingLaw :
    MatterCurrentCouplingLawRequest

selectedMatterAuthorityCurrentCarrier : Set
selectedMatterAuthorityCurrentCarrier =
  Source.StrictSelectedSourceCurrentCouplingReceipt.currentCarrier
    Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

selectedMatterAuthorityCurrentCarrierIsUserSupplied :
  selectedMatterAuthorityCurrentCarrier
  ≡
  YMObs.YMSFGCUserSuppliedCurrentCarrier
selectedMatterAuthorityCurrentCarrierIsUserSupplied =
  refl

selectedMatterAuthorityCurrentSource :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
selectedMatterAuthorityCurrentSource =
  Source.StrictSelectedSourceCurrentCouplingReceipt.sourceCurrent
    Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

selectedMatterAuthorityCurrentSourceIsStrictSelected :
  selectedMatterAuthorityCurrentSource
  ≡
  Source.strictSelectedCurrentSource
selectedMatterAuthorityCurrentSourceIsStrictSelected =
  refl

selectedMatterAuthorityEquationTarget :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMObs.YMSFGCUserSuppliedCurrentCarrier
selectedMatterAuthorityEquationTarget =
  Source.StrictSelectedSourceCurrentCouplingReceipt.equationTarget
    Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

selectedMatterAuthorityEquationTargetEqualsCurrent :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  selectedMatterAuthorityEquationTarget connection
  ≡
  selectedMatterAuthorityCurrentSource connection
selectedMatterAuthorityEquationTargetEqualsCurrent =
  Source.StrictSelectedSourceCurrentCouplingReceipt.selectedDStarFEqualsCurrentSource
    Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

record MatterCurrentAuthorityBoundary : Set₁ where
  field
    authorityTokenRequest :
      MatterCurrentAuthorityTokenRequest

    authorityDecision :
      MatterCurrentAuthorityDecision

    couplingLawRequest :
      MatterCurrentCouplingLawRequest

    targetCarrier :
      Set

    targetCarrierIsSelectedCurrentCarrier :
      targetCarrier
      ≡
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    targetCurrentSource :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    targetCurrentSourceIsSelected :
      targetCurrentSource
      ≡
      Source.strictSelectedCurrentSource

    exactMatterCouplingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter :
      exactMatterCouplingBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

    authorityAccepted :
      Bool

    authorityAcceptedIsFalse :
      authorityAccepted ≡ false

    authorityBoundaryNotes :
      List String

open MatterCurrentAuthorityBoundary public

canonicalMatterCurrentAuthorityBoundary :
  MatterCurrentAuthorityBoundary
canonicalMatterCurrentAuthorityBoundary =
  record
    { authorityTokenRequest =
        requestAcceptedPhysicalMatterCurrentAuthorityToken
    ; authorityDecision =
        matterCurrentAuthorityNotAccepted
    ; couplingLawRequest =
        requestMatterCurrentToSelectedCurrentCarrierCouplingLaw
    ; targetCarrier =
        YMObs.YMSFGCUserSuppliedCurrentCarrier
    ; targetCarrierIsSelectedCurrentCarrier =
        refl
    ; targetCurrentSource =
        Source.strictSelectedCurrentSource
    ; targetCurrentSourceIsSelected =
        refl
    ; exactMatterCouplingBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter =
        refl
    ; authorityAccepted =
        false
    ; authorityAcceptedIsFalse =
        refl
    ; authorityBoundaryNotes =
        "The selected finite current carrier is inhabited and exposed as the target of a future matter-current interpretation"
        ∷ "No accepted physical matter-current authority token is supplied in this module"
        ∷ "No law identifies a physical matter current with the selected finite current source"
        ∷ "The exact blocker remains missingCurrentSourceCouplingToMatter"
        ∷ []
    }

record StrictSelectedMatterCurrentAuthorityBridge : Set₂ where
  field
    status :
      StrictSelectedMatterCurrentAuthorityStatus

    consumedSourceCurrentCoupling :
      Source.StrictSelectedSourceCurrentCouplingReceipt

    consumedSourceCurrentCouplingIsCanonical :
      consumedSourceCurrentCoupling
      ≡
      Source.canonicalStrictSelectedSourceCurrentCouplingReceipt

    finiteSourceCurrentCoupled :
      Bool

    finiteSourceCurrentCoupledIsTrue :
      finiteSourceCurrentCoupled ≡ true

    selectedCurrentCarrier :
      Set

    selectedCurrentCarrierIsUserSupplied :
      selectedCurrentCarrier
      ≡
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    selectedCurrentSource :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    selectedCurrentSourceIsStrict :
      selectedCurrentSource
      ≡
      Source.strictSelectedCurrentSource

    selectedEquationTarget :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    selectedEquationTargetEqualsCurrent :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      selectedEquationTarget connection
      ≡
      selectedCurrentSource connection

    matterCurrentAuthorityBoundary :
      MatterCurrentAuthorityBoundary

    matterCurrentAuthorityBoundaryIsCanonical :
      matterCurrentAuthorityBoundary
      ≡
      canonicalMatterCurrentAuthorityBoundary

    authorityTokenRequest :
      MatterCurrentAuthorityTokenRequest

    authorityTokenRequestIsPhysicalMatterCurrent :
      authorityTokenRequest
      ≡
      requestAcceptedPhysicalMatterCurrentAuthorityToken

    authorityDecision :
      MatterCurrentAuthorityDecision

    authorityDecisionIsNotAccepted :
      authorityDecision
      ≡
      matterCurrentAuthorityNotAccepted

    matterCurrentCouplingLawRequest :
      MatterCurrentCouplingLawRequest

    matterCurrentCouplingLawRequestIsSelectedCarrierCoupling :
      matterCurrentCouplingLawRequest
      ≡
      requestMatterCurrentToSelectedCurrentCarrierCouplingLaw

    exactMatterSourceBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterSourceBlockerIsMissingCurrentSourceCouplingToMatter :
      exactMatterSourceBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

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
      List StrictSelectedMatterCurrentAuthorityRow

    rowIndexIsCanonical :
      rowIndex ≡ canonicalStrictSelectedMatterCurrentAuthorityRows

    rowCount :
      Nat

    rowCountIs8 :
      rowCount ≡ 8

    receiptBoundary :
      List String

open StrictSelectedMatterCurrentAuthorityBridge public

canonicalStrictSelectedMatterCurrentAuthorityBridge :
  StrictSelectedMatterCurrentAuthorityBridge
canonicalStrictSelectedMatterCurrentAuthorityBridge =
  record
    { status =
        selectedFiniteCurrentPackagedMatterAuthorityMissing
    ; consumedSourceCurrentCoupling =
        Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; consumedSourceCurrentCouplingIsCanonical =
        refl
    ; finiteSourceCurrentCoupled =
        Source.StrictSelectedSourceCurrentCouplingReceipt.finiteSourceCurrentCoupled
          Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
    ; finiteSourceCurrentCoupledIsTrue =
        refl
    ; selectedCurrentCarrier =
        selectedMatterAuthorityCurrentCarrier
    ; selectedCurrentCarrierIsUserSupplied =
        selectedMatterAuthorityCurrentCarrierIsUserSupplied
    ; selectedCurrentSource =
        selectedMatterAuthorityCurrentSource
    ; selectedCurrentSourceIsStrict =
        selectedMatterAuthorityCurrentSourceIsStrictSelected
    ; selectedEquationTarget =
        selectedMatterAuthorityEquationTarget
    ; selectedEquationTargetEqualsCurrent =
        selectedMatterAuthorityEquationTargetEqualsCurrent
    ; matterCurrentAuthorityBoundary =
        canonicalMatterCurrentAuthorityBoundary
    ; matterCurrentAuthorityBoundaryIsCanonical =
        refl
    ; authorityTokenRequest =
        requestAcceptedPhysicalMatterCurrentAuthorityToken
    ; authorityTokenRequestIsPhysicalMatterCurrent =
        refl
    ; authorityDecision =
        matterCurrentAuthorityNotAccepted
    ; authorityDecisionIsNotAccepted =
        refl
    ; matterCurrentCouplingLawRequest =
        requestMatterCurrentToSelectedCurrentCarrierCouplingLaw
    ; matterCurrentCouplingLawRequestIsSelectedCarrierCoupling =
        refl
    ; exactMatterSourceBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterSourceBlockerIsMissingCurrentSourceCouplingToMatter =
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
        canonicalStrictSelectedMatterCurrentAuthorityRows
    ; rowIndexIsCanonical =
        refl
    ; rowCount =
        8
    ; rowCountIs8 =
        refl
    ; receiptBoundary =
        "Consumes canonicalStrictSelectedSourceCurrentCouplingReceipt rather than rebuilding the selected finite current law"
        ∷ "Exposes YMSFGCUserSuppliedCurrentCarrier and strictSelectedCurrentSource as the finite target for a future matter current"
        ∷ "Records an explicit request for an accepted physical matter-current authority token"
        ∷ "Records an explicit request for a law coupling that physical matter current to the selected finite current carrier"
        ∷ "The exact blocker is missingCurrentSourceCouplingToMatter"
        ∷ "Physical matter source, physical sourced Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalStrictSelectedMatterCurrentAuthorityRowCountIs8 :
  listCount canonicalStrictSelectedMatterCurrentAuthorityRows ≡ 8
canonicalStrictSelectedMatterCurrentAuthorityRowCountIs8 =
  refl

canonicalStrictSelectedMatterCurrentAuthorityConsumesSourceReceipt :
  StrictSelectedMatterCurrentAuthorityBridge.consumedSourceCurrentCoupling
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
canonicalStrictSelectedMatterCurrentAuthorityConsumesSourceReceipt =
  refl

canonicalStrictSelectedMatterCurrentAuthorityCurrentCarrierUserSupplied :
  StrictSelectedMatterCurrentAuthorityBridge.selectedCurrentCarrier
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  YMObs.YMSFGCUserSuppliedCurrentCarrier
canonicalStrictSelectedMatterCurrentAuthorityCurrentCarrierUserSupplied =
  refl

canonicalStrictSelectedMatterCurrentAuthorityTokenNotAccepted :
  MatterCurrentAuthorityBoundary.authorityAccepted
    (StrictSelectedMatterCurrentAuthorityBridge.matterCurrentAuthorityBoundary
      canonicalStrictSelectedMatterCurrentAuthorityBridge)
  ≡
  false
canonicalStrictSelectedMatterCurrentAuthorityTokenNotAccepted =
  refl

canonicalStrictSelectedMatterCurrentAuthorityMatterBlockerExact :
  StrictSelectedMatterCurrentAuthorityBridge.exactMatterSourceBlocker
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  YMObs.missingCurrentSourceCouplingToMatter
canonicalStrictSelectedMatterCurrentAuthorityMatterBlockerExact =
  refl

canonicalStrictSelectedMatterCurrentAuthorityPhysicalMatterFalse :
  StrictSelectedMatterCurrentAuthorityBridge.physicalMatterSourcePromoted
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  false
canonicalStrictSelectedMatterCurrentAuthorityPhysicalMatterFalse =
  refl

canonicalStrictSelectedMatterCurrentAuthorityPhysicalYMSourcedFalse :
  StrictSelectedMatterCurrentAuthorityBridge.physicalSourcedYangMillsPromoted
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  false
canonicalStrictSelectedMatterCurrentAuthorityPhysicalYMSourcedFalse =
  refl

canonicalStrictSelectedMatterCurrentAuthorityClayYMFalse :
  StrictSelectedMatterCurrentAuthorityBridge.clayYangMillsPromoted
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  false
canonicalStrictSelectedMatterCurrentAuthorityClayYMFalse =
  refl

canonicalStrictSelectedMatterCurrentAuthorityTerminalFalse :
  StrictSelectedMatterCurrentAuthorityBridge.terminalPromotion
    canonicalStrictSelectedMatterCurrentAuthorityBridge
  ≡
  false
canonicalStrictSelectedMatterCurrentAuthorityTerminalFalse =
  refl
