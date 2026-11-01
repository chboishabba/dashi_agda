module DASHI.Physics.Closure.PressureDepthCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.BalancedTritFieldSemanticsReceipt as Balanced
import DASHI.Physics.Closure.DialecticalAccumulationReceipt as Accumulation
import DASHI.Physics.Closure.DialecticalAtomFrontierReceipt as AtomFrontier
import DASHI.Physics.Closure.IntersectionalPressureAnisotropyReceipt as Anisotropy

------------------------------------------------------------------------
-- Pressure/depth correction receipt.
--
-- This receipt corrects the local bookkeeping vocabulary:
--
-- * pressure is not geometric path length;
-- * depth is integrated braid history / accumulated carry count;
-- * pressure is live unresolved braid complexity: active unresolved thread
--   count, unresolved carries, crossing density, contradiction load, and
--   active deformation.
--
-- The older path-length pressure receipt is consumed only as historical
-- anisotropy bookkeeping.  This module does not promote a Navier-Stokes,
-- runtime, physics, or Clay theorem.

data PressureDepthCorrectionStatus : Set where
  pressureDepthCorrectionRecordedFailClosed :
    PressureDepthCorrectionStatus

data DepthReading : Set where
  integratedBraidHistory :
    DepthReading

  accumulatedCarryCount :
    DepthReading

canonicalDepthReadings :
  List DepthReading
canonicalDepthReadings =
  integratedBraidHistory
  ∷ accumulatedCarryCount
  ∷ []

data PressureReading : Set where
  liveUnresolvedBraidComplexity :
    PressureReading

  activeUnresolvedThreadCount :
    PressureReading

  unresolvedCarries :
    PressureReading

  crossingDensity :
    PressureReading

  contradictionLoad :
    PressureReading

  activeDeformation :
    PressureReading

canonicalPressureReadings :
  List PressureReading
canonicalPressureReadings =
  liveUnresolvedBraidComplexity
  ∷ activeUnresolvedThreadCount
  ∷ unresolvedCarries
  ∷ crossingDensity
  ∷ contradictionLoad
  ∷ activeDeformation
  ∷ []

data CorrectedPressureBoundary : Set where
  pressureNotGeometricPathLength :
    CorrectedPressureBoundary

  olderPathLengthAnisotropyRetainedAsHistoricalBookkeeping :
    CorrectedPressureBoundary

  noPressureRecoveryTheorem :
    CorrectedPressureBoundary

  noNavierStokesTheorem :
    CorrectedPressureBoundary

  noRuntimeTheorem :
    CorrectedPressureBoundary

  noClayPromotion :
    CorrectedPressureBoundary

canonicalCorrectedPressureBoundaries :
  List CorrectedPressureBoundary
canonicalCorrectedPressureBoundaries =
  pressureNotGeometricPathLength
  ∷ olderPathLengthAnisotropyRetainedAsHistoricalBookkeeping
  ∷ noPressureRecoveryTheorem
  ∷ noNavierStokesTheorem
  ∷ noRuntimeTheorem
  ∷ noClayPromotion
  ∷ []

data PressureDepthCorrectionPromotion : Set where

pressureDepthCorrectionPromotionImpossible :
  PressureDepthCorrectionPromotion →
  ⊥
pressureDepthCorrectionPromotionImpossible ()

depthCorrectionStatement :
  String
depthCorrectionStatement =
  "Depth is integrated braid history / accumulated carry count, not instantaneous geometric path length."

pressureCorrectionStatement :
  String
pressureCorrectionStatement =
  "Pressure is live unresolved braid complexity: active unresolved thread count, unresolved carries, crossing density, contradiction load, and active deformation."

pathLengthCorrectionStatement :
  String
pathLengthCorrectionStatement =
  "Pressure is not geometric path length; older path-length pressure surfaces are retained only as anisotropy bookkeeping context."

record PressureDepthCorrectionReceipt : Setω where
  field
    status :
      PressureDepthCorrectionStatus

    statusIsFailClosed :
      status ≡ pressureDepthCorrectionRecordedFailClosed

    balancedTritReceipt :
      Balanced.BalancedTritFieldSemanticsReceipt

    balancedTritCarrierPreserved :
      Balanced.balancedTritCarrierPreserved balancedTritReceipt ≡ true

    balancedTritNoRuntimeCodec :
      Balanced.runtimeCodecClaimed balancedTritReceipt ≡ false

    accumulationReceipt :
      Accumulation.DialecticalAccumulationReceipt

    accumulationCarryDepthIncrease :
      Accumulation.depthIncrease accumulationReceipt ≡ 1

    accumulationPhysicsFalse :
      Accumulation.physicsTheoremClaimed accumulationReceipt ≡ false

    accumulationClayFalse :
      Accumulation.clayClaimMade accumulationReceipt ≡ false

    anisotropyReceipt :
      Anisotropy.IntersectionalPressureAnisotropyReceipt

    olderAnisotropyPressureRecoveryFalse :
      Anisotropy.pressureRecoveryProved anisotropyReceipt ≡ false

    olderAnisotropyNSFalse :
      Anisotropy.navierStokesGate3Proved anisotropyReceipt ≡ false

    olderAnisotropyClayFalse :
      Anisotropy.clayPromotionPromoted anisotropyReceipt ≡ false

    atomFrontierReceipt :
      AtomFrontier.DialecticalAtomFrontierReceipt

    atomFrontierPressureRecoveryFalse :
      AtomFrontier.pressureRecoveryProofPromoted atomFrontierReceipt ≡ false

    atomFrontierNSFalse :
      AtomFrontier.nsGate3ClosurePromoted atomFrontierReceipt ≡ false

    atomFrontierClayFalse :
      AtomFrontier.clayPromotionMade atomFrontierReceipt ≡ false

    depthReadings :
      List DepthReading

    depthReadingsAreCanonical :
      depthReadings ≡ canonicalDepthReadings

    pressureReadings :
      List PressureReading

    pressureReadingsAreCanonical :
      pressureReadings ≡ canonicalPressureReadings

    pressureIsGeometricPathLength :
      Bool

    pressureIsGeometricPathLengthIsFalse :
      pressureIsGeometricPathLength ≡ false

    olderPathLengthReceiptRetainedAsAnisotropyContext :
      Bool

    olderPathLengthReceiptRetainedAsAnisotropyContextIsTrue :
      olderPathLengthReceiptRetainedAsAnisotropyContext ≡ true

    unresolvedThreadCountRecorded :
      Bool

    unresolvedThreadCountRecordedIsTrue :
      unresolvedThreadCountRecorded ≡ true

    unresolvedCarryCountRecorded :
      Bool

    unresolvedCarryCountRecordedIsTrue :
      unresolvedCarryCountRecorded ≡ true

    crossingDensityRecorded :
      Bool

    crossingDensityRecordedIsTrue :
      crossingDensityRecorded ≡ true

    contradictionLoadRecorded :
      Bool

    contradictionLoadRecordedIsTrue :
      contradictionLoadRecorded ≡ true

    activeDeformationRecorded :
      Bool

    activeDeformationRecordedIsTrue :
      activeDeformationRecorded ≡ true

    navierStokesTheoremPromoted :
      Bool

    navierStokesTheoremPromotedIsFalse :
      navierStokesTheoremPromoted ≡ false

    runtimeTheoremPromoted :
      Bool

    runtimeTheoremPromotedIsFalse :
      runtimeTheoremPromoted ≡ false

    clayPromotionMade :
      Bool

    clayPromotionMadeIsFalse :
      clayPromotionMade ≡ false

    boundaries :
      List CorrectedPressureBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalCorrectedPressureBoundaries

    promotionFlags :
      List PressureDepthCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      PressureDepthCorrectionPromotion →
      ⊥

    depthCorrectionReading :
      String

    depthCorrectionReadingIsCanonical :
      depthCorrectionReading ≡ depthCorrectionStatement

    pressureCorrectionReading :
      String

    pressureCorrectionReadingIsCanonical :
      pressureCorrectionReading ≡ pressureCorrectionStatement

    pathLengthCorrectionReading :
      String

    pathLengthCorrectionReadingIsCanonical :
      pathLengthCorrectionReading ≡ pathLengthCorrectionStatement

    receiptBoundary :
      List String

open PressureDepthCorrectionReceipt public

canonicalPressureDepthCorrectionReceipt :
  PressureDepthCorrectionReceipt
canonicalPressureDepthCorrectionReceipt =
  record
    { status =
        pressureDepthCorrectionRecordedFailClosed
    ; statusIsFailClosed =
        refl
    ; balancedTritReceipt =
        Balanced.canonicalBalancedTritFieldSemanticsReceipt
    ; balancedTritCarrierPreserved =
        refl
    ; balancedTritNoRuntimeCodec =
        refl
    ; accumulationReceipt =
        Accumulation.canonicalDialecticalAccumulationReceipt
    ; accumulationCarryDepthIncrease =
        refl
    ; accumulationPhysicsFalse =
        refl
    ; accumulationClayFalse =
        refl
    ; anisotropyReceipt =
        Anisotropy.canonicalIntersectionalPressureAnisotropyReceipt
    ; olderAnisotropyPressureRecoveryFalse =
        refl
    ; olderAnisotropyNSFalse =
        refl
    ; olderAnisotropyClayFalse =
        refl
    ; atomFrontierReceipt =
        AtomFrontier.canonicalDialecticalAtomFrontierReceipt
    ; atomFrontierPressureRecoveryFalse =
        refl
    ; atomFrontierNSFalse =
        refl
    ; atomFrontierClayFalse =
        refl
    ; depthReadings =
        canonicalDepthReadings
    ; depthReadingsAreCanonical =
        refl
    ; pressureReadings =
        canonicalPressureReadings
    ; pressureReadingsAreCanonical =
        refl
    ; pressureIsGeometricPathLength =
        false
    ; pressureIsGeometricPathLengthIsFalse =
        refl
    ; olderPathLengthReceiptRetainedAsAnisotropyContext =
        true
    ; olderPathLengthReceiptRetainedAsAnisotropyContextIsTrue =
        refl
    ; unresolvedThreadCountRecorded =
        true
    ; unresolvedThreadCountRecordedIsTrue =
        refl
    ; unresolvedCarryCountRecorded =
        true
    ; unresolvedCarryCountRecordedIsTrue =
        refl
    ; crossingDensityRecorded =
        true
    ; crossingDensityRecordedIsTrue =
        refl
    ; contradictionLoadRecorded =
        true
    ; contradictionLoadRecordedIsTrue =
        refl
    ; activeDeformationRecorded =
        true
    ; activeDeformationRecordedIsTrue =
        refl
    ; navierStokesTheoremPromoted =
        false
    ; navierStokesTheoremPromotedIsFalse =
        refl
    ; runtimeTheoremPromoted =
        false
    ; runtimeTheoremPromotedIsFalse =
        refl
    ; clayPromotionMade =
        false
    ; clayPromotionMadeIsFalse =
        refl
    ; boundaries =
        canonicalCorrectedPressureBoundaries
    ; boundariesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        pressureDepthCorrectionPromotionImpossible
    ; depthCorrectionReading =
        depthCorrectionStatement
    ; depthCorrectionReadingIsCanonical =
        refl
    ; pressureCorrectionReading =
        pressureCorrectionStatement
    ; pressureCorrectionReadingIsCanonical =
        refl
    ; pathLengthCorrectionReading =
        pathLengthCorrectionStatement
    ; pathLengthCorrectionReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Corrects pressure/depth vocabulary without mutating older receipt surfaces"
        ∷ "Depth is integrated braid history and accumulated carry count"
        ∷ "Pressure is live unresolved braid complexity, not geometric path length"
        ∷ "Pressure components recorded: active unresolved thread count, unresolved carries, crossing density, contradiction load, and active deformation"
        ∷ "IntersectionalPressureAnisotropyReceipt is consumed only as older anisotropy/path-length bookkeeping context"
        ∷ "No Navier-Stokes theorem, runtime theorem, physics theorem, Clay promotion, or terminal promotion is introduced"
        ∷ []
    }

canonicalPressureDepthCorrectionNoNS :
  navierStokesTheoremPromoted canonicalPressureDepthCorrectionReceipt ≡ false
canonicalPressureDepthCorrectionNoNS =
  refl

canonicalPressureDepthCorrectionNoRuntime :
  runtimeTheoremPromoted canonicalPressureDepthCorrectionReceipt ≡ false
canonicalPressureDepthCorrectionNoRuntime =
  refl

canonicalPressureDepthCorrectionNoClay :
  clayPromotionMade canonicalPressureDepthCorrectionReceipt ≡ false
canonicalPressureDepthCorrectionNoClay =
  refl
