module DASHI.Physics.Closure.ClayRoadmapAssignmentPrep where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YML1StatusReceipt as YML1
import DASHI.Physics.Closure.NSFrameRestrictionReceipt as NSFrame

data NextClayAssignment : Set where
  ymL2UniformPlaquetteCorrelatorBound :
    NextClayAssignment

  ymL2WeakCouplingLargeBetaExpansion :
    NextClayAssignment

  nsRestrictedZeroMeanFrameLowerBound :
    NextClayAssignment

  nsNonlinearTermAfterFrameBound :
    NextClayAssignment

canonicalNextClayAssignments : List NextClayAssignment
canonicalNextClayAssignments =
  ymL2UniformPlaquetteCorrelatorBound
  ∷ ymL2WeakCouplingLargeBetaExpansion
  ∷ nsRestrictedZeroMeanFrameLowerBound
  ∷ nsNonlinearTermAfterFrameBound
  ∷ []

ymL2TargetLabel : String
ymL2TargetLabel =
  "YM L2 next target: uniform two-plaquette correlator bounds as D -> infinity, weak-coupling/large-beta expansion target, depends on finite-lattice L1."

nsC6TargetLabel : String
nsC6TargetLabel =
  "Prove the restricted zero-mean frame lower bound, then revisit nonlinear term passage."

data ClayRoadmapAssignmentPromotion : Set where

clayRoadmapAssignmentPromotionImpossibleHere :
  ClayRoadmapAssignmentPromotion →
  ⊥
clayRoadmapAssignmentPromotionImpossibleHere ()

record ClayRoadmapAssignmentPrep : Setω where
  field
    ymL1Status :
      YML1.YML1StatusReceipt

    ymL1InhabitedFiniteScope :
      YML1.ymL1CarrierLatticeInhabited ymL1Status ≡ true

    nsFrameRestriction :
      NSFrame.NSFrameRestrictionReceipt

    nsRestrictedFrameStillOpen :
      NSFrame.restrictedFrameBoundProved nsFrameRestriction ≡ false

    ymL2Target :
      String

    ymL2TargetIsCanonical :
      ymL2Target ≡ ymL2TargetLabel

    nsC6Target :
      String

    nsC6TargetIsCanonical :
      nsC6Target ≡ nsC6TargetLabel

    nextAssignments :
      List NextClayAssignment

    nextAssignmentsAreCanonical :
      nextAssignments ≡ canonicalNextClayAssignments

    assignmentCount :
      Nat

    assignmentCountIsFour :
      assignmentCount ≡ 4

    finiteLatticeL1DependencyRecorded :
      Bool

    finiteLatticeL1DependencyRecordedIsTrue :
      finiteLatticeL1DependencyRecorded ≡ true

    weakCouplingLargeBetaExpansionTarget :
      Bool

    weakCouplingLargeBetaExpansionTargetIsTrue :
      weakCouplingLargeBetaExpansionTarget ≡ true

    twoPlaquetteBoundsProved :
      Bool

    twoPlaquetteBoundsProvedIsFalse :
      twoPlaquetteBoundsProved ≡ false

    dInfinityLimitClosed :
      Bool

    dInfinityLimitClosedIsFalse :
      dInfinityLimitClosed ≡ false

    documentationReceipt :
      Bool

    documentationReceiptIsTrue :
      documentationReceipt ≡ true

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    exactStandardModelPromoted :
      Bool

    exactStandardModelPromotedIsFalse :
      exactStandardModelPromoted ≡ false

    exactPhysicalCKMPromoted :
      Bool

    exactPhysicalCKMPromotedIsFalse :
      exactPhysicalCKMPromoted ≡ false

    promotionFlags :
      List ClayRoadmapAssignmentPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ClayRoadmapAssignmentPrep public

canonicalClayRoadmapAssignmentPrep :
  ClayRoadmapAssignmentPrep
canonicalClayRoadmapAssignmentPrep =
  record
    { ymL1Status =
        YML1.canonicalYML1StatusReceipt
    ; ymL1InhabitedFiniteScope =
        refl
    ; nsFrameRestriction =
        NSFrame.canonicalNSFrameRestrictionReceipt
    ; nsRestrictedFrameStillOpen =
        refl
    ; ymL2Target =
        ymL2TargetLabel
    ; ymL2TargetIsCanonical =
        refl
    ; nsC6Target =
        nsC6TargetLabel
    ; nsC6TargetIsCanonical =
        refl
    ; nextAssignments =
        canonicalNextClayAssignments
    ; nextAssignmentsAreCanonical =
        refl
    ; assignmentCount =
        4
    ; assignmentCountIsFour =
        refl
    ; finiteLatticeL1DependencyRecorded =
        true
    ; finiteLatticeL1DependencyRecordedIsTrue =
        refl
    ; weakCouplingLargeBetaExpansionTarget =
        true
    ; weakCouplingLargeBetaExpansionTargetIsTrue =
        refl
    ; twoPlaquetteBoundsProved =
        false
    ; twoPlaquetteBoundsProvedIsFalse =
        refl
    ; dInfinityLimitClosed =
        false
    ; dInfinityLimitClosedIsFalse =
        refl
    ; documentationReceipt =
        true
    ; documentationReceiptIsTrue =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; exactStandardModelPromoted =
        false
    ; exactStandardModelPromotedIsFalse =
        refl
    ; exactPhysicalCKMPromoted =
        false
    ; exactPhysicalCKMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Manager B Worker D assignment prep consumes current YM L1 and NS restricted-frame status receipts."
        ∷ "YM L2 uniform two-plaquette correlator bounds as D -> infinity are assigned but not proved here."
        ∷ "The YM L2 target route is weak-coupling / large-beta expansion and depends on finite-lattice L1."
        ∷ "NS restricted zero-mean frame and nonlinear-passage targets are assigned but not proved here."
        ∷ "No Clay, exact SM, exact physical CKM, or terminal promotion is asserted."
        ∷ []
    }

clayRoadmapAssignmentPrepKeepsTerminalFalse :
  terminalClaimPromoted canonicalClayRoadmapAssignmentPrep ≡ false
clayRoadmapAssignmentPrepKeepsTerminalFalse =
  refl
