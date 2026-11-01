module DASHI.Physics.Closure.NSFilamentFiningRuntimeBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSFastestClayPathReceipt as Fastest
import DASHI.Physics.Closure.NSFilamentFiningCore as Core

------------------------------------------------------------------------
-- Runtime/empirical bridge for sibling ../dashiCFD.
--
-- This receipt separates three claims that were previously easy to conflate:
--
--   * decode parity: CPU and Vulkan implement the same decoder;
--   * codec fidelity: the shared decoder approximates the LES truth field;
--   * physical promotion: the codec says something theorem-level about NS.
--
-- The observed parity-only run closed the first claim at the tested runtime
-- surface.  It did not close the second or third.  In particular, the three
-- files named baseline/lifetime/lifetime_strict were produced by commands with
-- identical policy arguments; filenames alone do not constitute a parameter
-- sweep or evidence for lifetime shaping.

data FilamentRuntimeStatus : Set where
  parityClean_candidateRuntimeBridge_noPromotion : FilamentRuntimeStatus

data FilamentRuntimeOpenGate : Set where
  parameterisedLifetimeSweep : FilamentRuntimeOpenGate
  lifetimeDistributionReadback : FilamentRuntimeOpenGate
  lifetimeEffectOnCodecFidelity : FilamentRuntimeOpenGate
  crossResolutionParity : FilamentRuntimeOpenGate
  coherenceProxyPhysicalValidation : FilamentRuntimeOpenGate
  codecToNSPhysicalBridge : FilamentRuntimeOpenGate

canonicalFilamentRuntimeOpenGates : List FilamentRuntimeOpenGate
canonicalFilamentRuntimeOpenGates =
  parameterisedLifetimeSweep
  ∷ lifetimeDistributionReadback
  ∷ lifetimeEffectOnCodecFidelity
  ∷ crossResolutionParity
  ∷ coherenceProxyPhysicalValidation
  ∷ codecToNSPhysicalBridge
  ∷ []

data FilamentRuntimePromotion : Set where

filamentRuntimePromotionImpossibleHere : FilamentRuntimePromotion → ⊥
filamentRuntimePromotionImpossibleHere ()

parityCommand : String
parityCommand =
  "MPLBACKEND=Agg python run_v4_snapshots.py --backend vulkan --decode-backend vulkan --fft-backend vkfft-vulkan --parity-only --progress-every 200"

runtimeStatement : String
runtimeStatement =
  "The tested dashiCFD parity-only surface reported CPU/Vulkan decoded-field relative L2 0.0000, correlation 1.0000, low-pass relative L2 0.0000, and mask match 1.000 at printed precision for snapshots t=300..3000 after explicit vkFFT inverse-normalisation repair."

runtimeBoundary : String
runtimeBoundary =
  "Printed-precision parity is a candidate runtime receipt, not a universal bitwise theorem.  The baseline/lifetime/lifetime_strict commands shown in the source thread were argument-identical apart from output filenames, so their identical GT traces do not establish a lifetime effect or null effect.  No physical-filament, Navier-Stokes, regularity, or Clay promotion follows."

record NSFilamentFiningRuntimeReceipt : Setω where
  field
    status : FilamentRuntimeStatus
    statusIsCanonical :
      status ≡ parityClean_candidateRuntimeBridge_noPromotion

    coreStatement : String
    coreStatementIsCanonical :
      coreStatement ≡ Core.filamentFiningStatement

    inverseFFTNormalizationExplicit : Bool
    inverseFFTNormalizationExplicitIsTrue :
      inverseFFTNormalizationExplicit ≡ true

    vulkanDecodeActuallyUsed : Bool
    vulkanDecodeActuallyUsedIsTrue :
      vulkanDecodeActuallyUsed ≡ true

    decodedFieldParityAtPrintedPrecision : Bool
    decodedFieldParityAtPrintedPrecisionIsTrue :
      decodedFieldParityAtPrintedPrecision ≡ true

    lowPassParityAtPrintedPrecision : Bool
    lowPassParityAtPrintedPrecisionIsTrue :
      lowPassParityAtPrintedPrecision ≡ true

    maskParityAtPrintedPrecision : Bool
    maskParityAtPrintedPrecisionIsTrue :
      maskParityAtPrintedPrecision ≡ true

    persistentPerCellLifetimeImplemented : Bool
    persistentPerCellLifetimeImplementedIsTrue :
      persistentPerCellLifetimeImplemented ≡ true

    compactAliveKilledMaxMetricsImplemented : Bool
    compactAliveKilledMaxMetricsImplementedIsTrue :
      compactAliveKilledMaxMetricsImplemented ≡ true

    lifetimeShapesAnnihilationAcceptance : Bool
    lifetimeShapesAnnihilationAcceptanceIsTrue :
      lifetimeShapesAnnihilationAcceptance ≡ true

    lifetimeRelaxationFactor : String
    lifetimeRelaxationFactorIsRecorded :
      lifetimeRelaxationFactor ≡ "0.85"

    lifetimeIncrementsPerAnnihilationIteration : Bool
    lifetimeIncrementsPerAnnihilationIterationIsTrue :
      lifetimeIncrementsPerAnnihilationIteration ≡ true

    parityModeSkipsPlotsAndGroundTruth : Bool
    parityModeSkipsPlotsAndGroundTruthIsTrue :
      parityModeSkipsPlotsAndGroundTruth ≡ true

    threeNamedRunsActuallyParameterised : Bool
    threeNamedRunsActuallyParameterisedIsFalse :
      threeNamedRunsActuallyParameterised ≡ false

    lifetimeDistributionMetricsImplemented : Bool
    lifetimeDistributionMetricsImplementedIsFalse :
      lifetimeDistributionMetricsImplemented ≡ false

    physicalCoherenceProxyValidated : Bool
    physicalCoherenceProxyValidatedIsFalse :
      physicalCoherenceProxyValidated ≡ false

    codecToNSPhysicalBridgeProved : Bool
    codecToNSPhysicalBridgeProvedIsFalse :
      codecToNSPhysicalBridgeProved ≡ false

    fastestPathReceipt : Fastest.NSFastestClayPathReceipt
    clayNavierStokesStillNotPromoted :
      Fastest.clayNavierStokesPromoted fastestPathReceipt ≡ false

    openGates : List FilamentRuntimeOpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalFilamentRuntimeOpenGates

    command : String
    commandIsCanonical : command ≡ parityCommand

    statement : String
    statementIsCanonical : statement ≡ runtimeStatement

    boundary : String
    boundaryIsCanonical : boundary ≡ runtimeBoundary

    promotions : List FilamentRuntimePromotion
    promotionsAreEmpty : promotions ≡ []

    noPromotionPossibleHere : FilamentRuntimePromotion → ⊥

open NSFilamentFiningRuntimeReceipt public

canonicalNSFilamentFiningRuntimeReceipt :
  NSFilamentFiningRuntimeReceipt
canonicalNSFilamentFiningRuntimeReceipt =
  record
    { status = parityClean_candidateRuntimeBridge_noPromotion
    ; statusIsCanonical = refl
    ; coreStatement = Core.filamentFiningStatement
    ; coreStatementIsCanonical = refl
    ; inverseFFTNormalizationExplicit = true
    ; inverseFFTNormalizationExplicitIsTrue = refl
    ; vulkanDecodeActuallyUsed = true
    ; vulkanDecodeActuallyUsedIsTrue = refl
    ; decodedFieldParityAtPrintedPrecision = true
    ; decodedFieldParityAtPrintedPrecisionIsTrue = refl
    ; lowPassParityAtPrintedPrecision = true
    ; lowPassParityAtPrintedPrecisionIsTrue = refl
    ; maskParityAtPrintedPrecision = true
    ; maskParityAtPrintedPrecisionIsTrue = refl
    ; persistentPerCellLifetimeImplemented = true
    ; persistentPerCellLifetimeImplementedIsTrue = refl
    ; compactAliveKilledMaxMetricsImplemented = true
    ; compactAliveKilledMaxMetricsImplementedIsTrue = refl
    ; lifetimeShapesAnnihilationAcceptance = true
    ; lifetimeShapesAnnihilationAcceptanceIsTrue = refl
    ; lifetimeRelaxationFactor = "0.85"
    ; lifetimeRelaxationFactorIsRecorded = refl
    ; lifetimeIncrementsPerAnnihilationIteration = true
    ; lifetimeIncrementsPerAnnihilationIterationIsTrue = refl
    ; parityModeSkipsPlotsAndGroundTruth = true
    ; parityModeSkipsPlotsAndGroundTruthIsTrue = refl
    ; threeNamedRunsActuallyParameterised = false
    ; threeNamedRunsActuallyParameterisedIsFalse = refl
    ; lifetimeDistributionMetricsImplemented = false
    ; lifetimeDistributionMetricsImplementedIsFalse = refl
    ; physicalCoherenceProxyValidated = false
    ; physicalCoherenceProxyValidatedIsFalse = refl
    ; codecToNSPhysicalBridgeProved = false
    ; codecToNSPhysicalBridgeProvedIsFalse = refl
    ; fastestPathReceipt = Fastest.canonicalNSFastestClayPathReceipt
    ; clayNavierStokesStillNotPromoted = refl
    ; openGates = canonicalFilamentRuntimeOpenGates
    ; openGatesAreCanonical = refl
    ; command = parityCommand
    ; commandIsCanonical = refl
    ; statement = runtimeStatement
    ; statementIsCanonical = refl
    ; boundary = runtimeBoundary
    ; boundaryIsCanonical = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = filamentRuntimePromotionImpossibleHere
    }

canonicalRuntimeParityClean :
  decodedFieldParityAtPrintedPrecision
    canonicalNSFilamentFiningRuntimeReceipt
  ≡ true
canonicalRuntimeParityClean = refl

canonicalThreeWaySweepNotYetRun :
  threeNamedRunsActuallyParameterised
    canonicalNSFilamentFiningRuntimeReceipt
  ≡ false
canonicalThreeWaySweepNotYetRun = refl

canonicalFilamentRuntimeNoClay :
  Fastest.clayNavierStokesPromoted
    (fastestPathReceipt canonicalNSFilamentFiningRuntimeReceipt)
  ≡ false
canonicalFilamentRuntimeNoClay = refl
