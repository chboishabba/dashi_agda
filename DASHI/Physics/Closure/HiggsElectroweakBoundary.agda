module DASHI.Physics.Closure.HiggsElectroweakBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierMixingReceipt as CKM
import DASHI.Physics.Closure.CKMCarrierDerived as CKMD
import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs
import DASHI.Physics.Closure.CKMExactWitnesses as Exact
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.YukawaFromCarrier as Yukawa

------------------------------------------------------------------------
-- Higgs / electroweak boundary surface.
--
-- The boundary records the external v_Higgs, W, Z, g, and g' anchors as a
-- typed receipt shape.  It reuses the existing Higgs symmetry-breaking
-- receipt, but keeps the numerical electroweak calibration and the CKM /
-- Yukawa compatibility as boundary targets rather than promoted claims.

data HiggsElectroweakBoundaryStatus : Set where
  boundaryOnlyNoPromotion :
    HiggsElectroweakBoundaryStatus

data HiggsElectroweakOpenObligation : Set where
  missingBoundaryToken :
    HiggsElectroweakOpenObligation

  missingResidualU1EMSurvival :
    HiggsElectroweakOpenObligation

  missingVevMassLawConsistency :
    HiggsElectroweakOpenObligation

  missingCKMYukawaCompatibility :
    HiggsElectroweakOpenObligation

  missingMassRatioConsistency :
    HiggsElectroweakOpenObligation

canonicalHiggsElectroweakOpenObligations :
  List HiggsElectroweakOpenObligation
canonicalHiggsElectroweakOpenObligations =
  missingBoundaryToken
  ∷ missingResidualU1EMSurvival
  ∷ missingVevMassLawConsistency
  ∷ missingCKMYukawaCompatibility
  ∷ missingMassRatioConsistency
  ∷ []

data HiggsElectroweakProofShape : Set where
  generatorSurvivalTarget :
    HiggsElectroweakProofShape

  vevAdapterTarget :
    HiggsElectroweakProofShape

  massLawTarget :
    HiggsElectroweakProofShape

  ckmCompatibilityTarget :
    HiggsElectroweakProofShape

  massRatioTarget :
    HiggsElectroweakProofShape

canonicalHiggsElectroweakProofShape :
  List HiggsElectroweakProofShape
canonicalHiggsElectroweakProofShape =
  generatorSurvivalTarget
  ∷ vevAdapterTarget
  ∷ massLawTarget
  ∷ ckmCompatibilityTarget
  ∷ massRatioTarget
  ∷ []

data HiggsElectroweakFailClosedBlocker : Set where
  missingAbsoluteVHiggsW4Authority :
    HiggsElectroweakFailClosedBlocker

  missingVEVSICalibration :
    HiggsElectroweakFailClosedBlocker

  missingWMassZMassPhysicalCalibration :
    HiggsElectroweakFailClosedBlocker

  missingPhysicalCKMSplittingFieldEigenbasis :
    HiggsElectroweakFailClosedBlocker

canonicalHiggsElectroweakFailClosedBlockers :
  List HiggsElectroweakFailClosedBlocker
canonicalHiggsElectroweakFailClosedBlockers =
  missingAbsoluteVHiggsW4Authority
  ∷ missingVEVSICalibration
  ∷ missingWMassZMassPhysicalCalibration
  ∷ missingPhysicalCKMSplittingFieldEigenbasis
  ∷ []

record HiggsElectroweakBoundaryReceipt : Setω where
  field
    upstreamHiggsReceipt :
      Higgs.HiggsSymmetryBreakingReceipt

    upstreamHiggsDependencyReceipt :
      Higgs.HiggsSymmetryBreakingDependencyReceipt

    ckmExactWitnessChainReceipt :
      CKM.CKMExactWitnessChainCarrierReceipt

    ckmCarrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    ckmUnitaryReceipt :
      CKMU.CKMUnitaryReceipt

    yukawaFromCarrierReceipt :
      Yukawa.YukawaFromCarrierReceipt

    absoluteHiggsVEVW4CalibrationFailClosed :
      Higgs.AbsoluteHiggsVEVW4CalibrationFailClosedReceipt

    carrierCKMMatrix :
      Matter.MixingMatrix

    carrierCKMMatrixIsCarrierDerived :
      carrierCKMMatrix
      ≡
      CKMD.ckmCarrierMatrix ckmCarrierDerivedReceipt

    carrierCKMMatrixIsYukawaReceiptMatrix :
      carrierCKMMatrix
      ≡
      Yukawa.ckmCarrierMatrix yukawaFromCarrierReceipt

    carrierCKMMatrixIsIdentity :
      carrierCKMMatrix ≡ Matter.identityMixingMatrix

    vHiggsLabel :
      String

    vHiggsLabelIsCanonical :
      vHiggsLabel ≡ "v_Higgs-adapter4-boundary"

    wMassLabel :
      String

    wMassLabelIsCanonical :
      wMassLabel ≡ "M_W-boundary"

    zMassLabel :
      String

    zMassLabelIsCanonical :
      zMassLabel ≡ "M_Z-boundary"

    gCouplingLabel :
      String

    gCouplingLabelIsCanonical :
      gCouplingLabel ≡ "g-coupling-boundary"

    gPrimeCouplingLabel :
      String

    gPrimeCouplingLabelIsCanonical :
      gPrimeCouplingLabel ≡ "g-prime-coupling-boundary"

    emGeneratorLabel :
      String

    emGeneratorLabelIsCanonical :
      emGeneratorLabel ≡ "Q_EM = T3 + Y/2"

    higgsNeutralTargetRecorded :
      Bool

    higgsNeutralTargetRecordedIsTrue :
      higgsNeutralTargetRecorded ≡ true

    massLawTargetRecorded :
      Bool

    massLawTargetRecordedIsTrue :
      massLawTargetRecorded ≡ true

    ckmCompatibilityTargetRecorded :
      Bool

    ckmCompatibilityTargetRecordedIsTrue :
      ckmCompatibilityTargetRecorded ≡ true

    electroweakPromotion :
      Bool

    electroweakPromotionIsFalse :
      electroweakPromotion ≡ false

    openObligations :
      List HiggsElectroweakOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalHiggsElectroweakOpenObligations

    proofShape :
      List HiggsElectroweakProofShape

    proofShapeIsCanonical :
      proofShape ≡ canonicalHiggsElectroweakProofShape

    failClosedBlockers :
      List HiggsElectroweakFailClosedBlocker

    failClosedBlockersAreCanonical :
      failClosedBlockers ≡ canonicalHiggsElectroweakFailClosedBlockers

    firstFailClosedBlocker :
      HiggsElectroweakFailClosedBlocker

    firstFailClosedBlockerIsAbsoluteVHiggsW4 :
      firstFailClosedBlocker ≡ missingAbsoluteVHiggsW4Authority

    boundaryNotes :
      List String

open HiggsElectroweakBoundaryReceipt public

canonicalHiggsElectroweakBoundaryReceipt :
  HiggsElectroweakBoundaryReceipt
canonicalHiggsElectroweakBoundaryReceipt =
  record
    { upstreamHiggsReceipt =
        Higgs.canonicalHiggsSymmetryBreakingReceipt
    ; upstreamHiggsDependencyReceipt =
        Higgs.canonicalHiggsSymmetryBreakingDependencyReceipt
    ; ckmExactWitnessChainReceipt =
        CKM.canonicalCKMExactWitnessChainCarrierReceipt
    ; ckmCarrierDerivedReceipt =
        CKMD.canonicalCKMCarrierDerived
    ; ckmUnitaryReceipt =
        CKMU.canonicalCKMUnitary
    ; yukawaFromCarrierReceipt =
        Yukawa.canonicalYukawaFromCarrier
    ; absoluteHiggsVEVW4CalibrationFailClosed =
        Higgs.canonicalAbsoluteHiggsVEVW4CalibrationFailClosedReceipt
    ; carrierCKMMatrix =
        CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
    ; carrierCKMMatrixIsCarrierDerived =
        refl
    ; carrierCKMMatrixIsYukawaReceiptMatrix =
        refl
    ; carrierCKMMatrixIsIdentity =
        refl
    ; vHiggsLabel =
        "v_Higgs-adapter4-boundary"
    ; vHiggsLabelIsCanonical =
        refl
    ; wMassLabel =
        "M_W-boundary"
    ; wMassLabelIsCanonical =
        refl
    ; zMassLabel =
        "M_Z-boundary"
    ; zMassLabelIsCanonical =
        refl
    ; gCouplingLabel =
        "g-coupling-boundary"
    ; gCouplingLabelIsCanonical =
        refl
    ; gPrimeCouplingLabel =
        "g-prime-coupling-boundary"
    ; gPrimeCouplingLabelIsCanonical =
        refl
    ; emGeneratorLabel =
        "Q_EM = T3 + Y/2"
    ; emGeneratorLabelIsCanonical =
        refl
    ; higgsNeutralTargetRecorded =
        true
    ; higgsNeutralTargetRecordedIsTrue =
        refl
    ; massLawTargetRecorded =
        true
    ; massLawTargetRecordedIsTrue =
        refl
    ; ckmCompatibilityTargetRecorded =
        true
    ; ckmCompatibilityTargetRecordedIsTrue =
        refl
    ; electroweakPromotion =
        false
    ; electroweakPromotionIsFalse =
        refl
    ; openObligations =
        canonicalHiggsElectroweakOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; proofShape =
        canonicalHiggsElectroweakProofShape
    ; proofShapeIsCanonical =
        refl
    ; failClosedBlockers =
        canonicalHiggsElectroweakFailClosedBlockers
    ; failClosedBlockersAreCanonical =
        refl
    ; firstFailClosedBlocker =
        missingAbsoluteVHiggsW4Authority
    ; firstFailClosedBlockerIsAbsoluteVHiggsW4 =
        refl
    ; boundaryNotes =
        "The existing Higgs symmetry-breaking receipt remains the upstream anchor"
        ∷ "v_Higgs is recorded as an adapter boundary, not derived from the carrier"
        ∷ "The carrier-derived CKM, CKM-unitarity, and Yukawa-from-carrier receipts agree on the concrete identity matrix"
        ∷ "The CKM exact witness chain is threaded only as a compatibility target"
        ∷ "Absolute Higgs/VEV/W4 calibration and physical splitting-field/eigenbasis promotion remain fail-closed blockers"
        ∷ "The W/Z mass laws are boundary equations, not a terminal electroweak promotion"
        ∷ []
    }

record HiggsElectroweakGate7BoundaryBridgeReceipt : Setω where
  field
    vHiggsAdapter4BoundaryRetained :
      Bool

    vHiggsAdapter4BoundaryRetainedIsTrue :
      vHiggsAdapter4BoundaryRetained ≡ true

    ckmExactWitnessChainReceipt :
      Exact.CKMExactWitnessChain

    ckmExactWitnessChainReceiptIsCanonical :
      ckmExactWitnessChainReceipt
      ≡
      Exact.canonicalCKMExactWitnessChain

    gate7ElectroweakBridgePromoted :
      Bool

    gate7ElectroweakBridgePromotedIsFalse :
      gate7ElectroweakBridgePromoted ≡ false

    bridgeBoundary :
      List String

open HiggsElectroweakGate7BoundaryBridgeReceipt public

canonicalHiggsElectroweakGate7BoundaryBridgeReceipt :
  HiggsElectroweakGate7BoundaryBridgeReceipt
canonicalHiggsElectroweakGate7BoundaryBridgeReceipt = record
  { vHiggsAdapter4BoundaryRetained =
      Higgs.vHiggsAdapter4Boundary
        Higgs.canonicalHiggsSymmetryBreakingDependencyReceipt
  ; vHiggsAdapter4BoundaryRetainedIsTrue =
      refl
  ; ckmExactWitnessChainReceipt =
      Exact.canonicalCKMExactWitnessChain
  ; ckmExactWitnessChainReceiptIsCanonical =
      refl
  ; gate7ElectroweakBridgePromoted =
      false
  ; gate7ElectroweakBridgePromotedIsFalse =
      refl
  ; bridgeBoundary =
      "The electroweak receipt retains v_Higgs as the explicit Adapter4 boundary"
      ∷ "The CKM exact witness chain is threaded as a compatibility target, not a promotion"
      ∷ "No electroweak or CKM theorem promotion is claimed from this bridge"
      ∷ []
  }

higgsElectroweakFirstOpenObligation :
  HiggsElectroweakOpenObligation
higgsElectroweakFirstOpenObligation =
  missingBoundaryToken

higgsElectroweakBoundaryUsesCarrierDerivedCKM :
  carrierCKMMatrix canonicalHiggsElectroweakBoundaryReceipt
  ≡
  CKMD.ckmCarrierMatrix
    (ckmCarrierDerivedReceipt canonicalHiggsElectroweakBoundaryReceipt)
higgsElectroweakBoundaryUsesCarrierDerivedCKM =
  refl

higgsElectroweakBoundaryFirstFailClosedBlocker :
  firstFailClosedBlocker canonicalHiggsElectroweakBoundaryReceipt
  ≡
  missingAbsoluteVHiggsW4Authority
higgsElectroweakBoundaryFirstFailClosedBlocker =
  refl
