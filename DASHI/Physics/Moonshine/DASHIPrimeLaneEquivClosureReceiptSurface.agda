module DASHI.Physics.Moonshine.DASHIPrimeLaneEquivClosureReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Physics.Moonshine.DASHIMonsterVOAUniquenessReceipt as Unique
import DASHI.Physics.Moonshine.DASHIPrimeLaneVOATypeReceipt as VOAType
import DASHI.Physics.Moonshine.DongLiMasonOrbifoldReceiptSurface as DLM
import DASHI.Physics.Moonshine.PrimeLaneVOAEquivalenceReceiptSurface as Bridge

------------------------------------------------------------------------
-- DASHI prime-lane equivalence closure receipt.
--
-- The underlying PrimeLaneVOAEquivalenceReceiptSurface deliberately remains a
-- candidate/provenance surface.  This module is the small authority-boundary wrapper
-- that records the Paper 2 composition:
--
--   P2-A: G2 + G4 give the prime-lane VOA type target.
--   P2-B: FLM + vEMS identify the c=24 target with the Monster orbifold.
--   DLM:  the orbifold weight-1 Lie algebra table is accepted authority.
--
-- Consuming those three receipts records an authority-backed
-- DASHIPrimeLaneEquiv transport bridge candidate for lane-dimension use.  It
-- does not promote the local VOA/Monster theorem, the lane-dimension theorem,
-- the Clay mass gap, or the terminal claim.

data DASHIPrimeLaneEquivClosureStatus : Set where
  p2AP2BDLMClosureAuthorityBackedNoLocalPromotion :
    DASHIPrimeLaneEquivClosureStatus

data DASHIPrimeLaneEquivClosureBoundary : Set where
  boundaryConsumesCandidateBridge :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryConsumesPrimeLaneVOAType :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryConsumesMonsterVOAUniqueness :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryConsumesDLMOrbifoldTable :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryNoLocalVOAMonsterPromotion :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryNoLaneDimensionPromotion :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryNoClayMassGapPromotion :
    DASHIPrimeLaneEquivClosureBoundary

  boundaryNoUngardedTerminalPromotion :
    DASHIPrimeLaneEquivClosureBoundary

canonicalDASHIPrimeLaneEquivClosureBoundaries :
  List DASHIPrimeLaneEquivClosureBoundary
canonicalDASHIPrimeLaneEquivClosureBoundaries =
  boundaryConsumesCandidateBridge
  ∷ boundaryConsumesPrimeLaneVOAType
  ∷ boundaryConsumesMonsterVOAUniqueness
  ∷ boundaryConsumesDLMOrbifoldTable
  ∷ boundaryNoLocalVOAMonsterPromotion
  ∷ boundaryNoLaneDimensionPromotion
  ∷ boundaryNoClayMassGapPromotion
  ∷ boundaryNoUngardedTerminalPromotion
  ∷ []

record ClosedDASHIPrimeLaneEquiv
  (p : Lane.MonsterPrimeLane) :
  Setω where
  field
    sourceCandidateBridge :
      Bridge.DASHIPrimeLaneEquiv p

    primeLaneVOAType :
      VOAType.PrimeLaneVOAType p

    closedForLane :
      Lane.MonsterPrimeLane

    closedForLaneIsInput :
      closedForLane ≡ p

    sourceCandidateStillAuditable :
      Bool

    sourceCandidateStillAuditableIsTrue :
      sourceCandidateStillAuditable ≡ true

    p2AConsumed :
      Bool

    p2AConsumedIsTrue :
      p2AConsumed ≡ true

    p2BConsumed :
      Bool

    p2BConsumedIsTrue :
      p2BConsumed ≡ true

    dlmAuthorityConsumed :
      Bool

    dlmAuthorityConsumedIsTrue :
      dlmAuthorityConsumed ≡ true

    dashiPrimeLaneEquivClosed :
      Bool

    dashiPrimeLaneEquivClosedIsTrue :
      dashiPrimeLaneEquivClosed ≡ true

    usableForLaneDimensionPromotion :
      Bool

    usableForLaneDimensionPromotionIsFalse :
      usableForLaneDimensionPromotion ≡ false

open ClosedDASHIPrimeLaneEquiv public

canonicalClosedDASHIPrimeLaneEquiv :
  (p : Lane.MonsterPrimeLane) →
  ClosedDASHIPrimeLaneEquiv p
canonicalClosedDASHIPrimeLaneEquiv p =
  record
    { sourceCandidateBridge =
        Bridge.canonicalDASHIPrimeLaneEquiv p
    ; primeLaneVOAType =
        VOAType.canonicalPrimeLaneVOAType p
    ; closedForLane =
        p
    ; closedForLaneIsInput =
        refl
    ; sourceCandidateStillAuditable =
        true
    ; sourceCandidateStillAuditableIsTrue =
        refl
    ; p2AConsumed =
        true
    ; p2AConsumedIsTrue =
        refl
    ; p2BConsumed =
        true
    ; p2BConsumedIsTrue =
        refl
    ; dlmAuthorityConsumed =
        true
    ; dlmAuthorityConsumedIsTrue =
        refl
    ; dashiPrimeLaneEquivClosed =
        true
    ; dashiPrimeLaneEquivClosedIsTrue =
        refl
    ; usableForLaneDimensionPromotion =
        false
    ; usableForLaneDimensionPromotionIsFalse =
        refl
    }

record DASHIPrimeLaneEquivClosureReceipt : Setω where
  field
    status :
      DASHIPrimeLaneEquivClosureStatus

    candidateBridgeSurface :
      Bridge.DASHIPrimeLaneEquivReceiptSurface

    primeLaneVOATypeReceipt :
      VOAType.DASHIPrimeLaneVOATypeReceipt

    monsterVOAUniquenessReceipt :
      Unique.DASHIMonsterVOAUniquenessReceipt

    dlmOrbifoldReceipt :
      DLM.DongLiMasonOrbifoldReceiptSurface

    closedAt :
      (p : Lane.MonsterPrimeLane) →
      ClosedDASHIPrimeLaneEquiv p

    p2AClosed :
      Bool

    p2AClosedIsTrue :
      p2AClosed ≡ true

    p2BClosed :
      Bool

    p2BClosedIsTrue :
      p2BClosed ≡ true

    dlmClosed :
      Bool

    dlmClosedIsTrue :
      dlmClosed ≡ true

    dashiPrimeLaneEquivClosurePromoted :
      Bool

    dashiPrimeLaneEquivClosurePromotedIsFalse :
      dashiPrimeLaneEquivClosurePromoted ≡ false

    laneDimensionPromotableFromClosure :
      Bool

    laneDimensionPromotableFromClosureIsFalse :
      laneDimensionPromotableFromClosure ≡ false

    continuumClayMassGapPromoted :
      Bool

    continuumClayMassGapPromotedIsFalse :
      continuumClayMassGapPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    terminalClaimRemainsGuardedByOtherAuthorities :
      Bool

    terminalClaimRemainsGuardedByOtherAuthoritiesIsTrue :
      terminalClaimRemainsGuardedByOtherAuthorities ≡ true

    boundaries :
      List DASHIPrimeLaneEquivClosureBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalDASHIPrimeLaneEquivClosureBoundaries

    receiptBoundary :
      List String

open DASHIPrimeLaneEquivClosureReceipt public

canonicalDASHIPrimeLaneEquivClosureReceipt :
  DASHIPrimeLaneEquivClosureReceipt
canonicalDASHIPrimeLaneEquivClosureReceipt =
  record
    { status =
        p2AP2BDLMClosureAuthorityBackedNoLocalPromotion
    ; candidateBridgeSurface =
        Bridge.canonicalDASHIPrimeLaneEquivReceiptSurface
    ; primeLaneVOATypeReceipt =
        VOAType.canonicalDASHIPrimeLaneVOATypeReceipt
    ; monsterVOAUniquenessReceipt =
        Unique.canonicalDASHIMonsterVOAUniquenessReceipt
    ; dlmOrbifoldReceipt =
        DLM.canonicalDongLiMasonOrbifoldReceiptSurface
    ; closedAt =
        canonicalClosedDASHIPrimeLaneEquiv
    ; p2AClosed =
        true
    ; p2AClosedIsTrue =
        refl
    ; p2BClosed =
        true
    ; p2BClosedIsTrue =
        refl
    ; dlmClosed =
        true
    ; dlmClosedIsTrue =
        refl
    ; dashiPrimeLaneEquivClosurePromoted =
        false
    ; dashiPrimeLaneEquivClosurePromotedIsFalse =
        refl
    ; laneDimensionPromotableFromClosure =
        false
    ; laneDimensionPromotableFromClosureIsFalse =
        refl
    ; continuumClayMassGapPromoted =
        false
    ; continuumClayMassGapPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; terminalClaimRemainsGuardedByOtherAuthorities =
        true
    ; terminalClaimRemainsGuardedByOtherAuthoritiesIsTrue =
        refl
    ; boundaries =
        canonicalDASHIPrimeLaneEquivClosureBoundaries
    ; boundariesAreCanonical =
        refl
    ; receiptBoundary =
        "P2-A prime-lane VOA type receipt is consumed as the G2/G4 -> VOA leg"
        ∷ "P2-B Monster VOA uniqueness receipt is consumed as the c=24 Monster-orbifold leg"
        ∷ "Dong-Li-Mason orbifold weight-1 Lie algebra authority is consumed as the gauge-rank table"
        ∷ "The original DASHIPrimeLaneEquiv candidate surface remains auditable as provenance"
        ∷ "This wrapper records an authority-backed bridge candidate but does not promote a local VOA/Monster theorem"
        ∷ "laneDimensionPromotableFromClosure remains false without a separate promotion authority"
        ∷ "continuumClayMassGapPromoted remains false"
        ∷ "terminalClaimPromoted remains false here and is guarded by the wider terminal authority package"
        ∷ []
    }

canonicalDASHIPrimeLaneEquivClosurePromoted :
  Bool
canonicalDASHIPrimeLaneEquivClosurePromoted =
  DASHIPrimeLaneEquivClosureReceipt.dashiPrimeLaneEquivClosurePromoted
    canonicalDASHIPrimeLaneEquivClosureReceipt

canonicalDASHIPrimeLaneEquivClosurePromotedIsFalse :
  canonicalDASHIPrimeLaneEquivClosurePromoted ≡ false
canonicalDASHIPrimeLaneEquivClosurePromotedIsFalse =
  refl

canonicalLaneDimensionPromotableFromDASHIPrimeLaneEquivClosure :
  Bool
canonicalLaneDimensionPromotableFromDASHIPrimeLaneEquivClosure =
  DASHIPrimeLaneEquivClosureReceipt.laneDimensionPromotableFromClosure
    canonicalDASHIPrimeLaneEquivClosureReceipt

canonicalLaneDimensionPromotableFromDASHIPrimeLaneEquivClosureIsFalse :
  canonicalLaneDimensionPromotableFromDASHIPrimeLaneEquivClosure ≡ false
canonicalLaneDimensionPromotableFromDASHIPrimeLaneEquivClosureIsFalse =
  refl

canonicalContinuumClayMassGapPromoted :
  Bool
canonicalContinuumClayMassGapPromoted =
  DASHIPrimeLaneEquivClosureReceipt.continuumClayMassGapPromoted
    canonicalDASHIPrimeLaneEquivClosureReceipt

canonicalContinuumClayMassGapPromotedIsFalse :
  canonicalContinuumClayMassGapPromoted ≡ false
canonicalContinuumClayMassGapPromotedIsFalse =
  refl

canonicalTerminalClaimPromoted :
  Bool
canonicalTerminalClaimPromoted =
  DASHIPrimeLaneEquivClosureReceipt.terminalClaimPromoted
    canonicalDASHIPrimeLaneEquivClosureReceipt

canonicalTerminalClaimPromotedIsFalse :
  canonicalTerminalClaimPromoted ≡ false
canonicalTerminalClaimPromotedIsFalse =
  refl
