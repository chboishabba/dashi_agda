module DASHI.Physics.Closure.CrossGateCompositionTheorems where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierToPhysicsFunctorAdjoint as Gate1Adjoint
import DASHI.Physics.Closure.CKMCarrierMixingReceipt as CKM
import DASHI.Physics.Closure.CrossGateConsistency as Gate8Consistency
import DASHI.Physics.Closure.HiggsElectroweakBoundary as HiggsEW
import DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility as YDHR
import DASHI.Physics.Closure.YukawaFromCarrier as Yukawa
import DASHI.Physics.QFT.DHRTensorDualGroupReconstruction as DHRTensor
import DASHI.Physics.QFT.DHRThermodynamicLimit as DHRLimit
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Quantum.Stone as Stone

------------------------------------------------------------------------
-- Cross-gate composition theorem surface.
--
-- The existing gate receipts already package the upstream witnesses.  This
-- module assembles them into a single composition surface so the repo has a
-- typed place to record how the Gate 1/6, Gate 5, and Gate 7 boundary layers
-- fit together.  It does not promote any gate; it only records the composed
-- receipts and the fail-closed status of the aggregate pipeline.

record Gate1Gate6DHRLimitCompositionReceipt : Setω where
  field
    carrierFunctorAdjointReceipt :
      Gate1Adjoint.CarrierToPhysicsFunctorAdjointReceipt

    thermodynamicLimitReceipt :
      DHRLimit.DHRThermodynamicLimitReceipt

    filteredColimitPreservationThreaded :
      Bool

    filteredColimitPreservationThreadedIsFalse :
      filteredColimitPreservationThreaded ≡ false

    dhrSectorCompatibilityThreaded :
      Bool

    dhrSectorCompatibilityThreadedIsFalse :
      dhrSectorCompatibilityThreaded ≡ false

    gate1Gate6LimitCompositionPromoted :
      Bool

    gate1Gate6LimitCompositionPromotedIsFalse :
      gate1Gate6LimitCompositionPromoted ≡ false

    compositionBoundary :
      List String

open Gate1Gate6DHRLimitCompositionReceipt public

canonicalGate1Gate6DHRLimitCompositionReceipt :
  Gate1Gate6DHRLimitCompositionReceipt
canonicalGate1Gate6DHRLimitCompositionReceipt =
  record
    { carrierFunctorAdjointReceipt =
        Gate1Adjoint.canonicalCarrierToPhysicsFunctorAdjointReceipt
    ; thermodynamicLimitReceipt =
        DHRLimit.canonicalDHRThermodynamicLimitReceipt
    ; filteredColimitPreservationThreaded =
        false
    ; filteredColimitPreservationThreadedIsFalse =
        refl
    ; dhrSectorCompatibilityThreaded =
        false
    ; dhrSectorCompatibilityThreadedIsFalse =
        refl
    ; gate1Gate6LimitCompositionPromoted =
        false
    ; gate1Gate6LimitCompositionPromotedIsFalse =
        refl
    ; compositionBoundary =
        "Gate 1/Gate 6 reconstruction is threaded through the DHR thermodynamic-limit receipt"
        ∷ "Filtered-colimit preservation remains a concrete target surface, not a promoted theorem"
        ∷ "DHR-sector compatibility remains carried as a fail-closed composition witness"
        ∷ "The aggregate Gate 1/Gate 6 limit composition is not promoted"
        ∷ []
    }

record Gate5StoneGNSCarrierFunctorCompositionReceipt : Setω where
  field
    carrierFunctorAdjointReceipt :
      Gate1Adjoint.CarrierToPhysicsFunctorAdjointReceipt

    gnsHilbertBridgeReceipt :
      Stone.GNSHilbertBridgeReceipt

    u5GNSHilbertToStoneHandoffReceipt :
      Stone.U5GNSHilbertToStoneHandoffReceipt

    gnsBridgeThreaded :
      Bool

    gnsBridgeThreadedIsTrue :
      gnsBridgeThreaded ≡ true

    stoneProgressThreaded :
      Bool

    stoneProgressThreadedIsTrue :
      stoneProgressThreaded ≡ true

    carrierFunctorCompatibilityPromoted :
      Bool

    carrierFunctorCompatibilityPromotedIsFalse :
      carrierFunctorCompatibilityPromoted ≡ false

    compositionBoundary :
      List String

open Gate5StoneGNSCarrierFunctorCompositionReceipt public

canonicalGate5StoneGNSCarrierFunctorCompositionReceipt :
  Gate5StoneGNSCarrierFunctorCompositionReceipt
canonicalGate5StoneGNSCarrierFunctorCompositionReceipt =
  record
    { carrierFunctorAdjointReceipt =
        Gate1Adjoint.canonicalCarrierToPhysicsFunctorAdjointReceipt
    ; gnsHilbertBridgeReceipt =
        Stone.canonicalGNSHilbertBridgeReceipt
    ; u5GNSHilbertToStoneHandoffReceipt =
        Stone.canonicalU5GNSHilbertToStoneHandoffReceipt
    ; gnsBridgeThreaded =
        true
    ; gnsBridgeThreadedIsTrue =
        refl
    ; stoneProgressThreaded =
        true
    ; stoneProgressThreadedIsTrue =
        refl
    ; carrierFunctorCompatibilityPromoted =
        false
    ; carrierFunctorCompatibilityPromotedIsFalse =
        refl
    ; compositionBoundary =
        "Stone threads the GNS bridge and the finite handoff receipt as an explicit compatibility surface"
        ∷ "The Gate 1 carrier functor adjoint receipt is consumed alongside the Stone bridge receipts"
        ∷ "The compatibility layer is recorded, but no carrier-functor promotion is introduced here"
        ∷ []
    }

record Gate7ElectroweakMassMixingCompositionReceipt : Setω where
  field
    electroweakBoundaryReceipt :
      HiggsEW.HiggsElectroweakBoundaryReceipt

    ckmExactWitnessChainReceipt :
      CKM.CKMExactWitnessChainCarrierReceipt

    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    ckmCompatibilityTargetRecorded :
      Bool

    ckmCompatibilityTargetRecordedIsTrue :
      ckmCompatibilityTargetRecorded ≡ true

    massMixingCompositionPromoted :
      Bool

    massMixingCompositionPromotedIsFalse :
      massMixingCompositionPromoted ≡ false

    compositionBoundary :
      List String

open Gate7ElectroweakMassMixingCompositionReceipt public

canonicalGate7ElectroweakMassMixingCompositionReceipt :
  Gate7ElectroweakMassMixingCompositionReceipt
canonicalGate7ElectroweakMassMixingCompositionReceipt =
  record
    { electroweakBoundaryReceipt =
        HiggsEW.canonicalHiggsElectroweakBoundaryReceipt
    ; ckmExactWitnessChainReceipt =
        CKM.canonicalCKMExactWitnessChainCarrierReceipt
    ; vHiggsAdapter4BoundaryRetained =
        HiggsEW.HiggsElectroweakBoundaryReceipt.higgsNeutralTargetRecorded
          HiggsEW.canonicalHiggsElectroweakBoundaryReceipt
    ; vHiggsAdapter4BoundaryRetainedIsTrue =
        refl
    ; ckmCompatibilityTargetRecorded =
        HiggsEW.HiggsElectroweakBoundaryReceipt.ckmCompatibilityTargetRecorded
          HiggsEW.canonicalHiggsElectroweakBoundaryReceipt
    ; ckmCompatibilityTargetRecordedIsTrue =
        refl
    ; massMixingCompositionPromoted =
        false
    ; massMixingCompositionPromotedIsFalse =
        refl
    ; compositionBoundary =
        "The electroweak boundary receipt already threads the v_Higgs adapter and CKM compatibility targets"
        ∷ "The CKM exact witness chain is consumed as a boundary input, not promoted as a new theorem"
        ∷ "Mass-mixing composition is recorded fail-closed at the Gate 7 surface"
        ∷ []
    }

record Gate8Term3DHRYukawaCompatibilityReceipt : Setω where
  field
    yukawaFromCarrierReceipt :
      Yukawa.YukawaFromCarrierReceipt

    dhrYukawaCompatibilityReceipt :
      YDHR.YukawaDHRIntertwinerCompatibilityReceipt

    dhrTensorDualTargetSurface :
      DHRTensor.DHRSectorTensorDualTargetSurface

    dhrIntertwinerTensorFusionProgress :
      DHRTensor.DHRIntertwinerTensorFusionAssociatorUnitProgress

    exactSMMatchBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    carrierDerivedReceiptThreaded :
      Bool

    carrierDerivedReceiptThreadedIsTrue :
      carrierDerivedReceiptThreaded ≡ true

    carrierCKMMatrixAgrees :
      YDHR.carrierCKMMatrix
        dhrYukawaCompatibilityReceipt
      ≡
      Yukawa.ckmCarrierMatrix
        yukawaFromCarrierReceipt

    upYukawaMatrixAgrees :
      YDHR.upYukawaMatrix
      ≡
      Yukawa.upYukawaMatrix
        yukawaFromCarrierReceipt

    downYukawaMatrixAgrees :
      YDHR.downYukawaMatrix
      ≡
      Yukawa.downYukawaMatrix
        yukawaFromCarrierReceipt

    physicalFermionMassReceiptsConstructed :
      Bool

    physicalFermionMassReceiptsConstructedMatchesDHRReceipt :
      physicalFermionMassReceiptsConstructed
      ≡
      YDHR.physicalFermionMassReceiptsConstructed
        dhrYukawaCompatibilityReceipt

    physicalFermionMassReceiptsConstructedIsFalse :
      physicalFermionMassReceiptsConstructed ≡ false

    genericYukawaEigenbasisConstructed :
      Bool

    genericYukawaEigenbasisConstructedMatchesDHRReceipt :
      genericYukawaEigenbasisConstructed
      ≡
      YDHR.genericYukawaSplittingFieldEigenbasisConstructed
        dhrYukawaCompatibilityReceipt

    genericYukawaEigenbasisConstructedIsFalse :
      genericYukawaEigenbasisConstructed ≡ false

    absoluteHiggsScaleConstructed :
      Bool

    absoluteHiggsScaleConstructedMatchesDHRReceipt :
      absoluteHiggsScaleConstructed
      ≡
      YDHR.absoluteHiggsScaleW4CalibrationConstructed
        dhrYukawaCompatibilityReceipt

    absoluteHiggsScaleConstructedIsFalse :
      absoluteHiggsScaleConstructed ≡ false

    dhrIntertwinerActionBeyondIdentityConstructed :
      Bool

    dhrIntertwinerActionBeyondIdentityConstructedMatchesDHRReceipt :
      dhrIntertwinerActionBeyondIdentityConstructed
      ≡
      YDHR.dhrActionBeyondIdentityConstructed
        dhrYukawaCompatibilityReceipt

    dhrIntertwinerActionBeyondIdentityConstructedIsFalse :
      dhrIntertwinerActionBeyondIdentityConstructed ≡ false

    gate8Term3Promoted :
      Bool

    gate8Term3PromotedIsFalse :
      gate8Term3Promoted ≡ false

    term3Boundary :
      List String

open Gate8Term3DHRYukawaCompatibilityReceipt public

canonicalGate8Term3DHRYukawaCompatibilityReceipt :
  Gate8Term3DHRYukawaCompatibilityReceipt
canonicalGate8Term3DHRYukawaCompatibilityReceipt =
  record
    { yukawaFromCarrierReceipt =
        Yukawa.canonicalYukawaFromCarrier
    ; dhrYukawaCompatibilityReceipt =
        YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; dhrTensorDualTargetSurface =
        DHRTensor.canonicalDHRSectorTensorDualTargetSurface
    ; dhrIntertwinerTensorFusionProgress =
        DHRTensor.canonicalDHRIntertwinerTensorFusionAssociatorUnitProgress
    ; exactSMMatchBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; carrierDerivedReceiptThreaded =
        true
    ; carrierDerivedReceiptThreadedIsTrue =
        refl
    ; carrierCKMMatrixAgrees =
        refl
    ; upYukawaMatrixAgrees =
        refl
    ; downYukawaMatrixAgrees =
        refl
    ; physicalFermionMassReceiptsConstructed =
        YDHR.physicalFermionMassReceiptsConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; physicalFermionMassReceiptsConstructedMatchesDHRReceipt =
        refl
    ; physicalFermionMassReceiptsConstructedIsFalse =
        refl
    ; genericYukawaEigenbasisConstructed =
        YDHR.genericYukawaSplittingFieldEigenbasisConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; genericYukawaEigenbasisConstructedMatchesDHRReceipt =
        refl
    ; genericYukawaEigenbasisConstructedIsFalse =
        refl
    ; absoluteHiggsScaleConstructed =
        YDHR.absoluteHiggsScaleW4CalibrationConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; absoluteHiggsScaleConstructedMatchesDHRReceipt =
        refl
    ; absoluteHiggsScaleConstructedIsFalse =
        refl
    ; dhrIntertwinerActionBeyondIdentityConstructed =
        YDHR.dhrActionBeyondIdentityConstructed
          YDHR.canonicalYukawaDHRIntertwinerCompatibility
    ; dhrIntertwinerActionBeyondIdentityConstructedMatchesDHRReceipt =
        refl
    ; dhrIntertwinerActionBeyondIdentityConstructedIsFalse =
        refl
    ; gate8Term3Promoted =
        false
    ; gate8Term3PromotedIsFalse =
        refl
    ; term3Boundary =
        "Gate8.term3 consumes the concrete carrier-derived CKM/Yukawa receipt and the DHR/Yukawa compatibility receipt"
        ∷ "The CKM carrier matrix and up/down Yukawa matrices are wired definitionally across both receipts"
        ∷ "DHR tensor/dual target sockets and the exact-SM blocker receipt are threaded as context only"
        ∷ "Physical masses, generic eigenbasis, absolute Higgs scale, and DHR intertwiner action beyond identity remain false"
        ∷ "No Gate 8, Standard Model, DHR reconstruction, or physical Yukawa promotion is asserted"
        ∷ []
    }

record Gate8CrossGateCompositionTheorems : Setω₆ where
  field
    gate1Gate6DHRLimitComposition :
      Gate1Gate6DHRLimitCompositionReceipt

    gate5StoneGNSCarrierFunctorComposition :
      Gate5StoneGNSCarrierFunctorCompositionReceipt

    gate7ElectroweakMassMixingComposition :
      Gate7ElectroweakMassMixingCompositionReceipt

    gate8Term3DHRYukawaCompatibility :
      Gate8Term3DHRYukawaCompatibilityReceipt

    gate8CrossGateConsistencyReceipt :
      Gate8Consistency.Gate8CrossGateConsistencyReceipt

    gate8ConsistencyThreaded :
      Bool

    gate8ConsistencyThreadedIsFalse :
      gate8ConsistencyThreaded ≡ false

    gate8CompositionPromoted :
      Bool

    gate8CompositionPromotedIsFalse :
      gate8CompositionPromoted ≡ false

    compositionBoundary :
      List String

open Gate8CrossGateCompositionTheorems public

canonicalGate8CrossGateCompositionTheorems :
  Gate8CrossGateCompositionTheorems
canonicalGate8CrossGateCompositionTheorems =
  record
    { gate1Gate6DHRLimitComposition =
        canonicalGate1Gate6DHRLimitCompositionReceipt
    ; gate5StoneGNSCarrierFunctorComposition =
        canonicalGate5StoneGNSCarrierFunctorCompositionReceipt
    ; gate7ElectroweakMassMixingComposition =
        canonicalGate7ElectroweakMassMixingCompositionReceipt
    ; gate8Term3DHRYukawaCompatibility =
        canonicalGate8Term3DHRYukawaCompatibilityReceipt
    ; gate8CrossGateConsistencyReceipt =
        Gate8Consistency.canonicalGate8CrossGateConsistencyReceipt
    ; gate8ConsistencyThreaded =
        false
    ; gate8ConsistencyThreadedIsFalse =
        refl
    ; gate8CompositionPromoted =
        false
    ; gate8CompositionPromotedIsFalse =
        refl
    ; compositionBoundary =
        "Cross-gate composition is recorded across the Gate 1/Gate 6, Gate 5, and Gate 7 boundary receipts"
        ∷ "Gate 8 consumes the explicit fail-closed cross-gate consistency receipt"
        ∷ "Gate8.term3 now threads carrier-derived CKM/Yukawa receipts into the DHR compatibility sockets"
        ∷ "The layer assembles typed receipts only; it does not promote Gate 8"
        ∷ "The three component compositions remain fail-closed and reusable by downstream surfaces"
        ∷ []
    }
