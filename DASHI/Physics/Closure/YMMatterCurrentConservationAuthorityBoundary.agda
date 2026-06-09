module DASHI.Physics.Closure.YMMatterCurrentConservationAuthorityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Physics.Closure.YMStrictSelectedMatterCurrentAuthorityBridge as Matter
import DASHI.Physics.Closure.YMStrictSelectedSourceCurrentCoupling as Source

------------------------------------------------------------------------
-- Matter-current conservation authority boundary.
--
-- The selected finite source-current coupling already proves, on the finite
-- user-supplied carrier, that the selected D * F target is the selected current
-- source.  The matter-current authority bridge exposes that selected current
-- as the target for a future physical matter interpretation.  This module adds
-- the next strict boundary: a selected finite conservation probe is typed over
-- the same current carrier, but no physical matter-current authority token and
-- no matter-current conservation law are accepted here.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data YMMatterCurrentConservationBoundaryStatus : Set where
  selectedFiniteCurrentConservationProbePackagedAuthorityBlocked :
    YMMatterCurrentConservationBoundaryStatus

data YMMatterCurrentConservationBoundaryRow : Set where
  matterAuthorityBridgeConsumedRow :
    YMMatterCurrentConservationBoundaryRow

  sourceCurrentCouplingConsumedRow :
    YMMatterCurrentConservationBoundaryRow

  selectedCurrentCarrierScopedRow :
    YMMatterCurrentConservationBoundaryRow

  selectedCurrentSourceScopedRow :
    YMMatterCurrentConservationBoundaryRow

  selectedConservationProbeCarrierRow :
    YMMatterCurrentConservationBoundaryRow

  selectedConservationProbeTypedRow :
    YMMatterCurrentConservationBoundaryRow

  selectedContinuityTargetTypedRow :
    YMMatterCurrentConservationBoundaryRow

  conservationAuthorityTokenRequestedRow :
    YMMatterCurrentConservationBoundaryRow

  conservationLawRequestedRow :
    YMMatterCurrentConservationBoundaryRow

  exactMatterCouplingBlockerRow :
    YMMatterCurrentConservationBoundaryRow

  promotionGuardsFalseRow :
    YMMatterCurrentConservationBoundaryRow

canonicalYMMatterCurrentConservationBoundaryRows :
  List YMMatterCurrentConservationBoundaryRow
canonicalYMMatterCurrentConservationBoundaryRows =
  matterAuthorityBridgeConsumedRow
  ∷ sourceCurrentCouplingConsumedRow
  ∷ selectedCurrentCarrierScopedRow
  ∷ selectedCurrentSourceScopedRow
  ∷ selectedConservationProbeCarrierRow
  ∷ selectedConservationProbeTypedRow
  ∷ selectedContinuityTargetTypedRow
  ∷ conservationAuthorityTokenRequestedRow
  ∷ conservationLawRequestedRow
  ∷ exactMatterCouplingBlockerRow
  ∷ promotionGuardsFalseRow
  ∷ []

data MatterCurrentConservationAuthorityRequest : Set where
  requestAcceptedMatterCurrentConservationAuthorityToken :
    MatterCurrentConservationAuthorityRequest

data MatterCurrentConservationAuthorityDecision : Set where
  matterCurrentConservationAuthorityNotAccepted :
    MatterCurrentConservationAuthorityDecision

data MatterCurrentConservationLawRequest : Set where
  requestMatterCurrentContinuityLawOnSelectedCurrentCarrier :
    MatterCurrentConservationLawRequest

data YMMatterCurrentConservationProbe : Set where
  selectedConservationProbeFromCurrent :
    YMObs.YMSFGCUserSuppliedCurrentCarrier →
    YMMatterCurrentConservationProbe

selectedConservationProbe :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMMatterCurrentConservationProbe
selectedConservationProbe connection =
  selectedConservationProbeFromCurrent
    (Source.strictSelectedCurrentSource connection)

selectedContinuityTarget :
  YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
  YMMatterCurrentConservationProbe
selectedContinuityTarget connection =
  selectedConservationProbeFromCurrent
    (Matter.selectedMatterAuthorityCurrentSource connection)

selectedContinuityTargetEqualsSelectedProbe :
  (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
  selectedContinuityTarget connection
  ≡
  selectedConservationProbe connection
selectedContinuityTargetEqualsSelectedProbe connection =
  refl

canonicalSelectedConservationProbe :
  YMMatterCurrentConservationProbe
canonicalSelectedConservationProbe =
  selectedConservationProbe
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

canonicalSelectedContinuityTarget :
  YMMatterCurrentConservationProbe
canonicalSelectedContinuityTarget =
  selectedContinuityTarget
    YMObs.ymSFGCUserSuppliedReferenceNonFlatConnection

canonicalSelectedContinuityTargetEqualsProbe :
  canonicalSelectedContinuityTarget
  ≡
  canonicalSelectedConservationProbe
canonicalSelectedContinuityTargetEqualsProbe =
  refl

record MatterCurrentConservationAuthorityBoundary : Set₁ where
  field
    authorityRequest :
      MatterCurrentConservationAuthorityRequest

    authorityDecision :
      MatterCurrentConservationAuthorityDecision

    conservationLawRequest :
      MatterCurrentConservationLawRequest

    currentCarrier :
      Set

    currentCarrierIsSelected :
      currentCarrier
      ≡
      YMObs.YMSFGCUserSuppliedCurrentCarrier

    conservationProbeCarrier :
      Set

    conservationProbeCarrierIsSelected :
      conservationProbeCarrier
      ≡
      YMMatterCurrentConservationProbe

    conservationProbe :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMMatterCurrentConservationProbe

    conservationProbeIsSelected :
      conservationProbe
      ≡
      selectedConservationProbe

    continuityTarget :
      YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier →
      YMMatterCurrentConservationProbe

    continuityTargetIsSelected :
      continuityTarget
      ≡
      selectedContinuityTarget

    selectedContinuityTargetEqualsProbe :
      (connection : YMObs.YMSFGCUserSuppliedNonFlatConnectionCarrier) →
      continuityTarget connection
      ≡
      conservationProbe connection

    exactMatterCouplingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter :
      exactMatterCouplingBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

    conservationAuthorityAccepted :
      Bool

    conservationAuthorityAcceptedIsFalse :
      conservationAuthorityAccepted ≡ false

    conservationLawAccepted :
      Bool

    conservationLawAcceptedIsFalse :
      conservationLawAccepted ≡ false

    boundaryNotes :
      List String

open MatterCurrentConservationAuthorityBoundary public

canonicalMatterCurrentConservationAuthorityBoundary :
  MatterCurrentConservationAuthorityBoundary
canonicalMatterCurrentConservationAuthorityBoundary =
  record
    { authorityRequest =
        requestAcceptedMatterCurrentConservationAuthorityToken
    ; authorityDecision =
        matterCurrentConservationAuthorityNotAccepted
    ; conservationLawRequest =
        requestMatterCurrentContinuityLawOnSelectedCurrentCarrier
    ; currentCarrier =
        YMObs.YMSFGCUserSuppliedCurrentCarrier
    ; currentCarrierIsSelected =
        refl
    ; conservationProbeCarrier =
        YMMatterCurrentConservationProbe
    ; conservationProbeCarrierIsSelected =
        refl
    ; conservationProbe =
        selectedConservationProbe
    ; conservationProbeIsSelected =
        refl
    ; continuityTarget =
        selectedContinuityTarget
    ; continuityTargetIsSelected =
        refl
    ; selectedContinuityTargetEqualsProbe =
        selectedContinuityTargetEqualsSelectedProbe
    ; exactMatterCouplingBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter =
        refl
    ; conservationAuthorityAccepted =
        false
    ; conservationAuthorityAcceptedIsFalse =
        refl
    ; conservationLawAccepted =
        false
    ; conservationLawAcceptedIsFalse =
        refl
    ; boundaryNotes =
        "The selected finite current carrier is the only current carrier scoped here"
        ∷ "A finite conservation probe is typed from the selected current source"
        ∷ "The continuity target is definitionally the same selected finite current probe"
        ∷ "No accepted physical matter-current conservation authority token is supplied"
        ∷ "No physical continuity equation for matter current is promoted"
        ∷ "The exact blocker remains missingCurrentSourceCouplingToMatter"
        ∷ []
    }

record YMMatterCurrentConservationAuthorityBoundary : Set₂ where
  field
    status :
      YMMatterCurrentConservationBoundaryStatus

    consumedMatterCurrentAuthorityBridge :
      Matter.StrictSelectedMatterCurrentAuthorityBridge

    consumedMatterCurrentAuthorityBridgeIsCanonical :
      consumedMatterCurrentAuthorityBridge
      ≡
      Matter.canonicalStrictSelectedMatterCurrentAuthorityBridge

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

    conservationBoundary :
      MatterCurrentConservationAuthorityBoundary

    conservationBoundaryIsCanonical :
      conservationBoundary
      ≡
      canonicalMatterCurrentConservationAuthorityBoundary

    canonicalProbe :
      YMMatterCurrentConservationProbe

    canonicalProbeIsSelected :
      canonicalProbe
      ≡
      canonicalSelectedConservationProbe

    canonicalContinuityTarget :
      YMMatterCurrentConservationProbe

    canonicalContinuityTargetEqualsProbe :
      canonicalContinuityTarget
      ≡
      canonicalProbe

    finiteConservationProbeTyped :
      Bool

    finiteConservationProbeTypedIsTrue :
      finiteConservationProbeTyped ≡ true

    finiteContinuityTargetTyped :
      Bool

    finiteContinuityTargetTypedIsTrue :
      finiteContinuityTargetTyped ≡ true

    physicalMatterCurrentAuthorityAccepted :
      Bool

    physicalMatterCurrentAuthorityAcceptedIsFalse :
      physicalMatterCurrentAuthorityAccepted ≡ false

    physicalMatterCurrentConservationAccepted :
      Bool

    physicalMatterCurrentConservationAcceptedIsFalse :
      physicalMatterCurrentConservationAccepted ≡ false

    physicalMatterCurrentPromoted :
      Bool

    physicalMatterCurrentPromotedIsFalse :
      physicalMatterCurrentPromoted ≡ false

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

    exactMatterCouplingBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter :
      exactMatterCouplingBlocker
      ≡
      YMObs.missingCurrentSourceCouplingToMatter

    rows :
      List YMMatterCurrentConservationBoundaryRow

    rowsAreCanonical :
      rows ≡ canonicalYMMatterCurrentConservationBoundaryRows

    rowCount :
      Nat

    rowCountIs11 :
      rowCount ≡ 11

    receiptBoundary :
      List String

open YMMatterCurrentConservationAuthorityBoundary public

canonicalYMMatterCurrentConservationAuthorityBoundary :
  YMMatterCurrentConservationAuthorityBoundary
canonicalYMMatterCurrentConservationAuthorityBoundary =
  record
    { status =
        selectedFiniteCurrentConservationProbePackagedAuthorityBlocked
    ; consumedMatterCurrentAuthorityBridge =
        Matter.canonicalStrictSelectedMatterCurrentAuthorityBridge
    ; consumedMatterCurrentAuthorityBridgeIsCanonical =
        refl
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
        Matter.StrictSelectedMatterCurrentAuthorityBridge.selectedCurrentCarrier
          Matter.canonicalStrictSelectedMatterCurrentAuthorityBridge
    ; selectedCurrentCarrierIsUserSupplied =
        refl
    ; selectedCurrentSource =
        Matter.StrictSelectedMatterCurrentAuthorityBridge.selectedCurrentSource
          Matter.canonicalStrictSelectedMatterCurrentAuthorityBridge
    ; selectedCurrentSourceIsStrict =
        refl
    ; conservationBoundary =
        canonicalMatterCurrentConservationAuthorityBoundary
    ; conservationBoundaryIsCanonical =
        refl
    ; canonicalProbe =
        canonicalSelectedConservationProbe
    ; canonicalProbeIsSelected =
        refl
    ; canonicalContinuityTarget =
        canonicalSelectedContinuityTarget
    ; canonicalContinuityTargetEqualsProbe =
        refl
    ; finiteConservationProbeTyped =
        true
    ; finiteConservationProbeTypedIsTrue =
        refl
    ; finiteContinuityTargetTyped =
        true
    ; finiteContinuityTargetTypedIsTrue =
        refl
    ; physicalMatterCurrentAuthorityAccepted =
        false
    ; physicalMatterCurrentAuthorityAcceptedIsFalse =
        refl
    ; physicalMatterCurrentConservationAccepted =
        false
    ; physicalMatterCurrentConservationAcceptedIsFalse =
        refl
    ; physicalMatterCurrentPromoted =
        false
    ; physicalMatterCurrentPromotedIsFalse =
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
    ; exactMatterCouplingBlocker =
        YMObs.missingCurrentSourceCouplingToMatter
    ; exactMatterCouplingBlockerIsMissingCurrentSourceCouplingToMatter =
        refl
    ; rows =
        canonicalYMMatterCurrentConservationBoundaryRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        11
    ; rowCountIs11 =
        refl
    ; receiptBoundary =
        "Consumes the strict selected matter-current authority bridge and the strict selected source-current coupling receipt"
        ∷ "Packages a selected finite conservation probe over YMSFGCUserSuppliedCurrentCarrier"
        ∷ "Records that the selected continuity target is definitionally the same finite current probe"
        ∷ "Keeps physical matter-current authority and physical matter-current conservation unaccepted"
        ∷ "The exact blocker remains missingCurrentSourceCouplingToMatter"
        ∷ "Physical matter/current, real sourced Yang-Mills, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMMatterCurrentConservationBoundaryRowCountIs11 :
  listCount canonicalYMMatterCurrentConservationBoundaryRows ≡ 11
canonicalYMMatterCurrentConservationBoundaryRowCountIs11 =
  refl

canonicalYMMatterCurrentConservationConsumesMatterBridge :
  consumedMatterCurrentAuthorityBridge
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  Matter.canonicalStrictSelectedMatterCurrentAuthorityBridge
canonicalYMMatterCurrentConservationConsumesMatterBridge =
  refl

canonicalYMMatterCurrentConservationConsumesSourceCoupling :
  consumedSourceCurrentCoupling
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  Source.canonicalStrictSelectedSourceCurrentCouplingReceipt
canonicalYMMatterCurrentConservationConsumesSourceCoupling =
  refl

canonicalYMMatterCurrentConservationProbeTyped :
  finiteConservationProbeTyped
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  true
canonicalYMMatterCurrentConservationProbeTyped =
  refl

canonicalYMMatterCurrentContinuityTargetTyped :
  finiteContinuityTargetTyped
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  true
canonicalYMMatterCurrentContinuityTargetTyped =
  refl

canonicalYMMatterCurrentConservationTargetEqualsProbe :
  canonicalContinuityTarget
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  canonicalProbe
    canonicalYMMatterCurrentConservationAuthorityBoundary
canonicalYMMatterCurrentConservationTargetEqualsProbe =
  refl

canonicalYMMatterCurrentConservationAuthorityFalse :
  physicalMatterCurrentAuthorityAccepted
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  false
canonicalYMMatterCurrentConservationAuthorityFalse =
  refl

canonicalYMMatterCurrentConservationLawFalse :
  physicalMatterCurrentConservationAccepted
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  false
canonicalYMMatterCurrentConservationLawFalse =
  refl

canonicalYMMatterCurrentConservationMatterCurrentFalse :
  physicalMatterCurrentPromoted
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  false
canonicalYMMatterCurrentConservationMatterCurrentFalse =
  refl

canonicalYMMatterCurrentConservationRealSourcedYMFalse :
  physicalSourcedYangMillsPromoted
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  false
canonicalYMMatterCurrentConservationRealSourcedYMFalse =
  refl

canonicalYMMatterCurrentConservationClayYMFalse :
  clayYangMillsPromoted
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  false
canonicalYMMatterCurrentConservationClayYMFalse =
  refl

canonicalYMMatterCurrentConservationTerminalFalse :
  terminalPromotion
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  false
canonicalYMMatterCurrentConservationTerminalFalse =
  refl

canonicalYMMatterCurrentConservationBlockerExact :
  exactMatterCouplingBlocker
    canonicalYMMatterCurrentConservationAuthorityBoundary
  ≡
  YMObs.missingCurrentSourceCouplingToMatter
canonicalYMMatterCurrentConservationBlockerExact =
  refl
