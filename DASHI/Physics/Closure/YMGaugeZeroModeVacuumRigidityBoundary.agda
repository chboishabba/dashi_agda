module DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary where

-- Yang-Mills gauge zero-mode vacuum-rigidity boundary.
--
-- This module records the finite zero-mode classification target sitting
-- between finite gauge/Hodge compatibility and Hamiltonian domination:
--
--   finite contractible BT/tree complex
--   -> gauge/Hodge compatible zero modes
--   -> flat connections
--   -> vacuum modulo gauge
--
-- If a finite model has non-vacuum topological-charge sectors, they must be
-- classified separately and assigned uniformly positive energy; they are not
-- zero-energy gauge-compatible modes.  This file is only a finite boundary
-- target feeding YMHamiltonianDominatesFiniteHodgeDefectBoundary.  It does not
-- construct the gauge quotient carrier, prove flat-to-vacuum rigidity, prove
-- Hamiltonian domination, prove OS/reflection positivity, transfer through the
-- continuum limit, or promote Yang-Mills Clay.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.FiniteGaugeHodgeAdjointCompatibility as Adj
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary as Ham

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Status, stages, rows, and blockers.

data YMGaugeZeroModeVacuumRigidityStatus : Set where
  finiteGaugeHodgeZeroModeVacuumRigidityTargetNamedPromotionBlocked :
    YMGaugeZeroModeVacuumRigidityStatus

data YMGaugeZeroModeRigidityStage : Set where
  finiteContractibleComplexStage :
    YMGaugeZeroModeRigidityStage

  finiteGaugeQuotientCarrierStage :
    YMGaugeZeroModeRigidityStage

  gaugeHodgeCompatibleZeroModeStage :
    YMGaugeZeroModeRigidityStage

  flatConnectionClassificationStage :
    YMGaugeZeroModeRigidityStage

  vacuumModuloGaugeStage :
    YMGaugeZeroModeRigidityStage

  topologicalChargeSectorStage :
    YMGaugeZeroModeRigidityStage

  positiveTopologicalEnergyStage :
    YMGaugeZeroModeRigidityStage

  hamiltonianDominationStage :
    YMGaugeZeroModeRigidityStage

  continuumNoPollutionStage :
    YMGaugeZeroModeRigidityStage

canonicalYMGaugeZeroModeRigidityStages :
  List YMGaugeZeroModeRigidityStage
canonicalYMGaugeZeroModeRigidityStages =
  finiteContractibleComplexStage
  ∷ finiteGaugeQuotientCarrierStage
  ∷ gaugeHodgeCompatibleZeroModeStage
  ∷ flatConnectionClassificationStage
  ∷ vacuumModuloGaugeStage
  ∷ topologicalChargeSectorStage
  ∷ positiveTopologicalEnergyStage
  ∷ hamiltonianDominationStage
  ∷ continuumNoPollutionStage
  ∷ []

data YMGaugeZeroModeRigidityRow : Set where
  finiteGaugeHodgeAdjointCompatibilityConsumedRow :
    YMGaugeZeroModeRigidityRow

  hamiltonianDominationBoundaryConsumedRow :
    YMGaugeZeroModeRigidityRow

  contractibleFiniteBTTreeComplexTargetRow :
    YMGaugeZeroModeRigidityRow

  gaugeCompatibleZeroModeSectorNamedRow :
    YMGaugeZeroModeRigidityRow

  flatConnectionSectorNamedRow :
    YMGaugeZeroModeRigidityRow

  vacuumModuloGaugeSectorNamedRow :
    YMGaugeZeroModeRigidityRow

  topologicalChargeSectorBoundaryNamedRow :
    YMGaugeZeroModeRigidityRow

  positiveTopologicalEnergyTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  zeroModeVacuumRigidityTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  nonVacuumZeroEnergyExcludedTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  finiteGaugeQuotientStillMissingRow :
    YMGaugeZeroModeRigidityRow

  flatConnectionToVacuumProofStillMissingRow :
    YMGaugeZeroModeRigidityRow

  topologicalSectorClassificationStillMissingRow :
    YMGaugeZeroModeRigidityRow

  hamiltonianDominationStillMissingRow :
    YMGaugeZeroModeRigidityRow

  osReflectionPositivityStillMissingRow :
    YMGaugeZeroModeRigidityRow

  continuumNoSpectralPollutionStillMissingRow :
    YMGaugeZeroModeRigidityRow

  clayAndTerminalHeldFalseRow :
    YMGaugeZeroModeRigidityRow

canonicalYMGaugeZeroModeRigidityRows :
  List YMGaugeZeroModeRigidityRow
canonicalYMGaugeZeroModeRigidityRows =
  finiteGaugeHodgeAdjointCompatibilityConsumedRow
  ∷ hamiltonianDominationBoundaryConsumedRow
  ∷ contractibleFiniteBTTreeComplexTargetRow
  ∷ gaugeCompatibleZeroModeSectorNamedRow
  ∷ flatConnectionSectorNamedRow
  ∷ vacuumModuloGaugeSectorNamedRow
  ∷ topologicalChargeSectorBoundaryNamedRow
  ∷ positiveTopologicalEnergyTargetNamedRow
  ∷ zeroModeVacuumRigidityTargetNamedRow
  ∷ nonVacuumZeroEnergyExcludedTargetNamedRow
  ∷ finiteGaugeQuotientStillMissingRow
  ∷ flatConnectionToVacuumProofStillMissingRow
  ∷ topologicalSectorClassificationStillMissingRow
  ∷ hamiltonianDominationStillMissingRow
  ∷ osReflectionPositivityStillMissingRow
  ∷ continuumNoSpectralPollutionStillMissingRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

data YMGaugeZeroModeVacuumRigidityBlocker : Set where
  missingFiniteGaugeQuotientCarrier :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingFlatConnectionToVacuumModuloGaugeProof :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingTopologicalSectorClassification :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingPositiveEnergyForNonVacuumTopologicalSectors :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingHamiltonianDominatesFiniteHodgeDefect :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingReflectionPositivityOSOnGaugeQuotient :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingContinuumTransferNoSpectralPollution :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingClayYangMillsAuthorityToken :
    YMGaugeZeroModeVacuumRigidityBlocker

canonicalYMGaugeZeroModeVacuumRigidityBlockers :
  List YMGaugeZeroModeVacuumRigidityBlocker
canonicalYMGaugeZeroModeVacuumRigidityBlockers =
  missingFiniteGaugeQuotientCarrier
  ∷ missingFlatConnectionToVacuumModuloGaugeProof
  ∷ missingTopologicalSectorClassification
  ∷ missingPositiveEnergyForNonVacuumTopologicalSectors
  ∷ missingHamiltonianDominatesFiniteHodgeDefect
  ∷ missingReflectionPositivityOSOnGaugeQuotient
  ∷ missingContinuumTransferNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

------------------------------------------------------------------------
-- Finite zero-mode classification targets.

data FiniteBTTreeContractibilityWitness : Set where
  finiteBTTreeContractibilityTarget :
    FiniteBTTreeContractibilityWitness

data GaugeCompatibleZeroModeSector : Set where
  gaugeCompatibleZeroModesFromFiniteHodgeDefect :
    Ham.FiniteHodgeGaugeDefectLaplacian →
    GaugeCompatibleZeroModeSector

data FlatConnectionSector : Set where
  flatConnectionsFromGaugeCompatibleZeroModes :
    GaugeCompatibleZeroModeSector →
    FlatConnectionSector

data VacuumModuloGaugeSector : Set where
  vacuumModuloGaugeFromContractibleFlatConnections :
    FiniteBTTreeContractibilityWitness →
    FlatConnectionSector →
    VacuumModuloGaugeSector

data TopologicalChargeSectorBoundary : Set where
  noTopologicalChargeOnContractibleTreeTarget :
    TopologicalChargeSectorBoundary

  nonVacuumTopologicalChargeSectorRequiresSeparateBoundary :
    TopologicalChargeSectorBoundary

data PositiveTopologicalEnergyTarget : Set where
  nonVacuumTopologicalChargeCarriesUniformPositiveEnergy :
    TopologicalChargeSectorBoundary →
    PositiveTopologicalEnergyTarget

data ZeroModeVacuumRigidityTarget : Set where
  compatibleZeroModesAreVacuumModuloGaugeOnContractibleFiniteCarrier :
    GaugeCompatibleZeroModeSector →
    FlatConnectionSector →
    VacuumModuloGaugeSector →
    ZeroModeVacuumRigidityTarget

data NonVacuumZeroEnergyExclusionTarget : Set where
  nonVacuumModesEitherTopologicalPositiveEnergyOrLeakagePositive :
    ZeroModeVacuumRigidityTarget →
    PositiveTopologicalEnergyTarget →
    Ham.HamiltonianDominationInequalityTarget →
    NonVacuumZeroEnergyExclusionTarget

canonicalFiniteBTTreeContractibilityWitness :
  FiniteBTTreeContractibilityWitness
canonicalFiniteBTTreeContractibilityWitness =
  finiteBTTreeContractibilityTarget

canonicalGaugeCompatibleZeroModeSector :
  GaugeCompatibleZeroModeSector
canonicalGaugeCompatibleZeroModeSector =
  gaugeCompatibleZeroModesFromFiniteHodgeDefect
    Ham.canonicalFiniteHodgeGaugeDefectLaplacian

canonicalFlatConnectionSector :
  FlatConnectionSector
canonicalFlatConnectionSector =
  flatConnectionsFromGaugeCompatibleZeroModes
    canonicalGaugeCompatibleZeroModeSector

canonicalVacuumModuloGaugeSector :
  VacuumModuloGaugeSector
canonicalVacuumModuloGaugeSector =
  vacuumModuloGaugeFromContractibleFlatConnections
    canonicalFiniteBTTreeContractibilityWitness
    canonicalFlatConnectionSector

canonicalTopologicalChargeSectorBoundary :
  TopologicalChargeSectorBoundary
canonicalTopologicalChargeSectorBoundary =
  nonVacuumTopologicalChargeSectorRequiresSeparateBoundary

canonicalPositiveTopologicalEnergyTarget :
  PositiveTopologicalEnergyTarget
canonicalPositiveTopologicalEnergyTarget =
  nonVacuumTopologicalChargeCarriesUniformPositiveEnergy
    canonicalTopologicalChargeSectorBoundary

canonicalZeroModeVacuumRigidityTarget :
  ZeroModeVacuumRigidityTarget
canonicalZeroModeVacuumRigidityTarget =
  compatibleZeroModesAreVacuumModuloGaugeOnContractibleFiniteCarrier
    canonicalGaugeCompatibleZeroModeSector
    canonicalFlatConnectionSector
    canonicalVacuumModuloGaugeSector

canonicalNonVacuumZeroEnergyExclusionTarget :
  NonVacuumZeroEnergyExclusionTarget
canonicalNonVacuumZeroEnergyExclusionTarget =
  nonVacuumModesEitherTopologicalPositiveEnergyOrLeakagePositive
    canonicalZeroModeVacuumRigidityTarget
    canonicalPositiveTopologicalEnergyTarget
    Ham.canonicalHamiltonianDominationInequalityTarget

------------------------------------------------------------------------
-- Governance booleans.

finiteBTTreeContractibilityTargetRecorded : Bool
finiteBTTreeContractibilityTargetRecorded =
  true

gaugeCompatibleZeroModeSectorTargetRecorded : Bool
gaugeCompatibleZeroModeSectorTargetRecorded =
  true

flatConnectionSectorTargetRecorded : Bool
flatConnectionSectorTargetRecorded =
  true

vacuumModuloGaugeSectorTargetRecorded : Bool
vacuumModuloGaugeSectorTargetRecorded =
  true

topologicalChargeSectorBoundaryRecorded : Bool
topologicalChargeSectorBoundaryRecorded =
  true

positiveTopologicalEnergyTargetRecorded : Bool
positiveTopologicalEnergyTargetRecorded =
  true

zeroModeVacuumRigidityTargetRecorded : Bool
zeroModeVacuumRigidityTargetRecorded =
  true

finiteGaugeQuotientCarrierConstructed : Bool
finiteGaugeQuotientCarrierConstructed =
  false

flatConnectionToVacuumModuloGaugeProved : Bool
flatConnectionToVacuumModuloGaugeProved =
  false

topologicalSectorClassificationProved : Bool
topologicalSectorClassificationProved =
  false

positiveEnergyForNonVacuumTopologicalSectorsProved : Bool
positiveEnergyForNonVacuumTopologicalSectorsProved =
  false

zeroModeVacuumRigidityProved : Bool
zeroModeVacuumRigidityProved =
  false

nonVacuumZeroEnergyModesExcluded : Bool
nonVacuumZeroEnergyModesExcluded =
  false

hamiltonianDominationImportedAsProof : Bool
hamiltonianDominationImportedAsProof =
  false

reflectionPositivityOSOnGaugeQuotientProved : Bool
reflectionPositivityOSOnGaugeQuotientProved =
  false

continuumTransferNoSpectralPollutionProved : Bool
continuumTransferNoSpectralPollutionProved =
  false

finiteYMMassGapPromoted : Bool
finiteYMMassGapPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

finiteBTTreeContractibilityTargetRecordedIsTrue :
  finiteBTTreeContractibilityTargetRecorded ≡ true
finiteBTTreeContractibilityTargetRecordedIsTrue =
  refl

gaugeCompatibleZeroModeSectorTargetRecordedIsTrue :
  gaugeCompatibleZeroModeSectorTargetRecorded ≡ true
gaugeCompatibleZeroModeSectorTargetRecordedIsTrue =
  refl

flatConnectionSectorTargetRecordedIsTrue :
  flatConnectionSectorTargetRecorded ≡ true
flatConnectionSectorTargetRecordedIsTrue =
  refl

vacuumModuloGaugeSectorTargetRecordedIsTrue :
  vacuumModuloGaugeSectorTargetRecorded ≡ true
vacuumModuloGaugeSectorTargetRecordedIsTrue =
  refl

topologicalChargeSectorBoundaryRecordedIsTrue :
  topologicalChargeSectorBoundaryRecorded ≡ true
topologicalChargeSectorBoundaryRecordedIsTrue =
  refl

positiveTopologicalEnergyTargetRecordedIsTrue :
  positiveTopologicalEnergyTargetRecorded ≡ true
positiveTopologicalEnergyTargetRecordedIsTrue =
  refl

zeroModeVacuumRigidityTargetRecordedIsTrue :
  zeroModeVacuumRigidityTargetRecorded ≡ true
zeroModeVacuumRigidityTargetRecordedIsTrue =
  refl

finiteGaugeQuotientCarrierConstructedIsFalse :
  finiteGaugeQuotientCarrierConstructed ≡ false
finiteGaugeQuotientCarrierConstructedIsFalse =
  refl

flatConnectionToVacuumModuloGaugeProvedIsFalse :
  flatConnectionToVacuumModuloGaugeProved ≡ false
flatConnectionToVacuumModuloGaugeProvedIsFalse =
  refl

topologicalSectorClassificationProvedIsFalse :
  topologicalSectorClassificationProved ≡ false
topologicalSectorClassificationProvedIsFalse =
  refl

positiveEnergyForNonVacuumTopologicalSectorsProvedIsFalse :
  positiveEnergyForNonVacuumTopologicalSectorsProved ≡ false
positiveEnergyForNonVacuumTopologicalSectorsProvedIsFalse =
  refl

zeroModeVacuumRigidityProvedIsFalse :
  zeroModeVacuumRigidityProved ≡ false
zeroModeVacuumRigidityProvedIsFalse =
  refl

nonVacuumZeroEnergyModesExcludedIsFalse :
  nonVacuumZeroEnergyModesExcluded ≡ false
nonVacuumZeroEnergyModesExcludedIsFalse =
  refl

hamiltonianDominationImportedAsProofIsFalse :
  hamiltonianDominationImportedAsProof ≡ false
hamiltonianDominationImportedAsProofIsFalse =
  refl

reflectionPositivityOSOnGaugeQuotientProvedIsFalse :
  reflectionPositivityOSOnGaugeQuotientProved ≡ false
reflectionPositivityOSOnGaugeQuotientProvedIsFalse =
  refl

continuumTransferNoSpectralPollutionProvedIsFalse :
  continuumTransferNoSpectralPollutionProved ≡ false
continuumTransferNoSpectralPollutionProvedIsFalse =
  refl

finiteYMMassGapPromotedIsFalse :
  finiteYMMassGapPromoted ≡ false
finiteYMMassGapPromotedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Boundary receipt.

record YMGaugeZeroModeVacuumRigidityBoundary : Setω where
  field
    status :
      YMGaugeZeroModeVacuumRigidityStatus

    consumedFiniteGaugeHodgeAdjointCompatibility :
      Adj.FiniteGaugeHodgeAdjointCompatibility

    consumedFiniteGaugeHodgeAdjointCompatibilityCanonical :
      Bool

    consumedFiniteGaugeHodgeAdjointCompatibilityCanonicalIsTrue :
      consumedFiniteGaugeHodgeAdjointCompatibilityCanonical ≡ true

    consumedHamiltonianDominationBoundary :
      Ham.YMHamiltonianDominatesFiniteHodgeDefectBoundary

    consumedHamiltonianDominationBoundaryCanonical :
      Bool

    consumedHamiltonianDominationBoundaryCanonicalIsTrue :
      consumedHamiltonianDominationBoundaryCanonical ≡ true

    stages :
      List YMGaugeZeroModeRigidityStage

    stagesAreCanonical :
      stages ≡ canonicalYMGaugeZeroModeRigidityStages

    rows :
      List YMGaugeZeroModeRigidityRow

    rowsAreCanonical :
      rows ≡ canonicalYMGaugeZeroModeRigidityRows

    blockers :
      List YMGaugeZeroModeVacuumRigidityBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMGaugeZeroModeVacuumRigidityBlockers

    finiteBTTreeContractibility :
      FiniteBTTreeContractibilityWitness

    finiteBTTreeContractibilityIsCanonical :
      finiteBTTreeContractibility
      ≡
      canonicalFiniteBTTreeContractibilityWitness

    gaugeCompatibleZeroModeSector :
      GaugeCompatibleZeroModeSector

    gaugeCompatibleZeroModeSectorIsCanonical :
      gaugeCompatibleZeroModeSector
      ≡
      canonicalGaugeCompatibleZeroModeSector

    flatConnectionSector :
      FlatConnectionSector

    flatConnectionSectorIsCanonical :
      flatConnectionSector ≡ canonicalFlatConnectionSector

    vacuumModuloGaugeSector :
      VacuumModuloGaugeSector

    vacuumModuloGaugeSectorIsCanonical :
      vacuumModuloGaugeSector ≡ canonicalVacuumModuloGaugeSector

    topologicalChargeSectorBoundary :
      TopologicalChargeSectorBoundary

    topologicalChargeSectorBoundaryIsCanonical :
      topologicalChargeSectorBoundary
      ≡
      canonicalTopologicalChargeSectorBoundary

    positiveTopologicalEnergyTarget :
      PositiveTopologicalEnergyTarget

    positiveTopologicalEnergyTargetIsCanonical :
      positiveTopologicalEnergyTarget
      ≡
      canonicalPositiveTopologicalEnergyTarget

    zeroModeVacuumRigidityTarget :
      ZeroModeVacuumRigidityTarget

    zeroModeVacuumRigidityTargetIsCanonical :
      zeroModeVacuumRigidityTarget
      ≡
      canonicalZeroModeVacuumRigidityTarget

    nonVacuumZeroEnergyExclusionTarget :
      NonVacuumZeroEnergyExclusionTarget

    nonVacuumZeroEnergyExclusionTargetIsCanonical :
      nonVacuumZeroEnergyExclusionTarget
      ≡
      canonicalNonVacuumZeroEnergyExclusionTarget

    upstreamAdjointCompatibilityDefectZeroStillFalse :
      Adj.compatibilityDefectZeroProved
        consumedFiniteGaugeHodgeAdjointCompatibility
      ≡
      false

    upstreamMetricWeightedAdjointnessStillFalse :
      Adj.metricWeightedAdjointnessPromoted
        consumedFiniteGaugeHodgeAdjointCompatibility
      ≡
      false

    upstreamHamiltonianDominationStillFalse :
      Ham.hamiltonianDominatesFiniteHodgeDefectProvedField
        consumedHamiltonianDominationBoundary
      ≡
      false

    upstreamHamiltonianFiniteQuotientStillFalse :
      Ham.finiteGaugeQuotientCarrierConstructedField
        consumedHamiltonianDominationBoundary
      ≡
      false

    upstreamOSOnGaugeQuotientStillFalse :
      Ham.reflectionPositivityOSOnGaugeQuotientProvedField
        consumedHamiltonianDominationBoundary
      ≡
      false

    upstreamContinuumNoPollutionStillFalse :
      Ham.continuumTransferNoSpectralPollutionProvedField
        consumedHamiltonianDominationBoundary
      ≡
      false

    exactFirstBlocker :
      YMGaugeZeroModeVacuumRigidityBlocker

    exactFirstBlockerIsFiniteGaugeQuotient :
      exactFirstBlocker ≡ missingFiniteGaugeQuotientCarrier

    exactRigidityBlocker :
      YMGaugeZeroModeVacuumRigidityBlocker

    exactRigidityBlockerIsFlatToVacuum :
      exactRigidityBlocker
      ≡
      missingFlatConnectionToVacuumModuloGaugeProof

    stageCount :
      Nat

    stageCountIs9 :
      stageCount ≡ 9

    rowCount :
      Nat

    rowCountIs17 :
      rowCount ≡ 17

    blockerCount :
      Nat

    blockerCountIs8 :
      blockerCount ≡ 8

    finiteBTTreeContractibilityTargetRecordedField :
      Bool

    finiteBTTreeContractibilityTargetRecordedFieldIsTrue :
      finiteBTTreeContractibilityTargetRecordedField ≡ true

    gaugeCompatibleZeroModeSectorTargetRecordedField :
      Bool

    gaugeCompatibleZeroModeSectorTargetRecordedFieldIsTrue :
      gaugeCompatibleZeroModeSectorTargetRecordedField ≡ true

    flatConnectionSectorTargetRecordedField :
      Bool

    flatConnectionSectorTargetRecordedFieldIsTrue :
      flatConnectionSectorTargetRecordedField ≡ true

    vacuumModuloGaugeSectorTargetRecordedField :
      Bool

    vacuumModuloGaugeSectorTargetRecordedFieldIsTrue :
      vacuumModuloGaugeSectorTargetRecordedField ≡ true

    topologicalChargeSectorBoundaryRecordedField :
      Bool

    topologicalChargeSectorBoundaryRecordedFieldIsTrue :
      topologicalChargeSectorBoundaryRecordedField ≡ true

    positiveTopologicalEnergyTargetRecordedField :
      Bool

    positiveTopologicalEnergyTargetRecordedFieldIsTrue :
      positiveTopologicalEnergyTargetRecordedField ≡ true

    zeroModeVacuumRigidityTargetRecordedField :
      Bool

    zeroModeVacuumRigidityTargetRecordedFieldIsTrue :
      zeroModeVacuumRigidityTargetRecordedField ≡ true

    finiteGaugeQuotientCarrierConstructedField :
      Bool

    finiteGaugeQuotientCarrierConstructedFieldIsFalse :
      finiteGaugeQuotientCarrierConstructedField ≡ false

    flatConnectionToVacuumModuloGaugeProvedField :
      Bool

    flatConnectionToVacuumModuloGaugeProvedFieldIsFalse :
      flatConnectionToVacuumModuloGaugeProvedField ≡ false

    topologicalSectorClassificationProvedField :
      Bool

    topologicalSectorClassificationProvedFieldIsFalse :
      topologicalSectorClassificationProvedField ≡ false

    positiveEnergyForNonVacuumTopologicalSectorsProvedField :
      Bool

    positiveEnergyForNonVacuumTopologicalSectorsProvedFieldIsFalse :
      positiveEnergyForNonVacuumTopologicalSectorsProvedField ≡ false

    zeroModeVacuumRigidityProvedField :
      Bool

    zeroModeVacuumRigidityProvedFieldIsFalse :
      zeroModeVacuumRigidityProvedField ≡ false

    nonVacuumZeroEnergyModesExcludedField :
      Bool

    nonVacuumZeroEnergyModesExcludedFieldIsFalse :
      nonVacuumZeroEnergyModesExcludedField ≡ false

    hamiltonianDominationImportedAsProofField :
      Bool

    hamiltonianDominationImportedAsProofFieldIsFalse :
      hamiltonianDominationImportedAsProofField ≡ false

    reflectionPositivityOSOnGaugeQuotientProvedField :
      Bool

    reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse :
      reflectionPositivityOSOnGaugeQuotientProvedField ≡ false

    continuumTransferNoSpectralPollutionProvedField :
      Bool

    continuumTransferNoSpectralPollutionProvedFieldIsFalse :
      continuumTransferNoSpectralPollutionProvedField ≡ false

    finiteYMMassGapPromotedField :
      Bool

    finiteYMMassGapPromotedFieldIsFalse :
      finiteYMMassGapPromotedField ≡ false

    clayYangMillsPromotedField :
      Bool

    clayYangMillsPromotedFieldIsFalse :
      clayYangMillsPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

    boundary :
      List String

open YMGaugeZeroModeVacuumRigidityBoundary public

canonicalYMGaugeZeroModeVacuumRigidityBoundary :
  YMGaugeZeroModeVacuumRigidityBoundary
canonicalYMGaugeZeroModeVacuumRigidityBoundary =
  record
    { status =
        finiteGaugeHodgeZeroModeVacuumRigidityTargetNamedPromotionBlocked
    ; consumedFiniteGaugeHodgeAdjointCompatibility =
        Adj.canonicalFiniteGaugeHodgeAdjointCompatibility
    ; consumedFiniteGaugeHodgeAdjointCompatibilityCanonical =
        true
    ; consumedFiniteGaugeHodgeAdjointCompatibilityCanonicalIsTrue =
        refl
    ; consumedHamiltonianDominationBoundary =
        Ham.canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; consumedHamiltonianDominationBoundaryCanonical =
        true
    ; consumedHamiltonianDominationBoundaryCanonicalIsTrue =
        refl
    ; stages =
        canonicalYMGaugeZeroModeRigidityStages
    ; stagesAreCanonical =
        refl
    ; rows =
        canonicalYMGaugeZeroModeRigidityRows
    ; rowsAreCanonical =
        refl
    ; blockers =
        canonicalYMGaugeZeroModeVacuumRigidityBlockers
    ; blockersAreCanonical =
        refl
    ; finiteBTTreeContractibility =
        canonicalFiniteBTTreeContractibilityWitness
    ; finiteBTTreeContractibilityIsCanonical =
        refl
    ; gaugeCompatibleZeroModeSector =
        canonicalGaugeCompatibleZeroModeSector
    ; gaugeCompatibleZeroModeSectorIsCanonical =
        refl
    ; flatConnectionSector =
        canonicalFlatConnectionSector
    ; flatConnectionSectorIsCanonical =
        refl
    ; vacuumModuloGaugeSector =
        canonicalVacuumModuloGaugeSector
    ; vacuumModuloGaugeSectorIsCanonical =
        refl
    ; topologicalChargeSectorBoundary =
        canonicalTopologicalChargeSectorBoundary
    ; topologicalChargeSectorBoundaryIsCanonical =
        refl
    ; positiveTopologicalEnergyTarget =
        canonicalPositiveTopologicalEnergyTarget
    ; positiveTopologicalEnergyTargetIsCanonical =
        refl
    ; zeroModeVacuumRigidityTarget =
        canonicalZeroModeVacuumRigidityTarget
    ; zeroModeVacuumRigidityTargetIsCanonical =
        refl
    ; nonVacuumZeroEnergyExclusionTarget =
        canonicalNonVacuumZeroEnergyExclusionTarget
    ; nonVacuumZeroEnergyExclusionTargetIsCanonical =
        refl
    ; upstreamAdjointCompatibilityDefectZeroStillFalse =
        refl
    ; upstreamMetricWeightedAdjointnessStillFalse =
        refl
    ; upstreamHamiltonianDominationStillFalse =
        Ham.canonicalYMHamiltonianDominationProvedFalse
    ; upstreamHamiltonianFiniteQuotientStillFalse =
        refl
    ; upstreamOSOnGaugeQuotientStillFalse =
        refl
    ; upstreamContinuumNoPollutionStillFalse =
        refl
    ; exactFirstBlocker =
        missingFiniteGaugeQuotientCarrier
    ; exactFirstBlockerIsFiniteGaugeQuotient =
        refl
    ; exactRigidityBlocker =
        missingFlatConnectionToVacuumModuloGaugeProof
    ; exactRigidityBlockerIsFlatToVacuum =
        refl
    ; stageCount =
        9
    ; stageCountIs9 =
        refl
    ; rowCount =
        17
    ; rowCountIs17 =
        refl
    ; blockerCount =
        8
    ; blockerCountIs8 =
        refl
    ; finiteBTTreeContractibilityTargetRecordedField =
        finiteBTTreeContractibilityTargetRecorded
    ; finiteBTTreeContractibilityTargetRecordedFieldIsTrue =
        refl
    ; gaugeCompatibleZeroModeSectorTargetRecordedField =
        gaugeCompatibleZeroModeSectorTargetRecorded
    ; gaugeCompatibleZeroModeSectorTargetRecordedFieldIsTrue =
        refl
    ; flatConnectionSectorTargetRecordedField =
        flatConnectionSectorTargetRecorded
    ; flatConnectionSectorTargetRecordedFieldIsTrue =
        refl
    ; vacuumModuloGaugeSectorTargetRecordedField =
        vacuumModuloGaugeSectorTargetRecorded
    ; vacuumModuloGaugeSectorTargetRecordedFieldIsTrue =
        refl
    ; topologicalChargeSectorBoundaryRecordedField =
        topologicalChargeSectorBoundaryRecorded
    ; topologicalChargeSectorBoundaryRecordedFieldIsTrue =
        refl
    ; positiveTopologicalEnergyTargetRecordedField =
        positiveTopologicalEnergyTargetRecorded
    ; positiveTopologicalEnergyTargetRecordedFieldIsTrue =
        refl
    ; zeroModeVacuumRigidityTargetRecordedField =
        zeroModeVacuumRigidityTargetRecorded
    ; zeroModeVacuumRigidityTargetRecordedFieldIsTrue =
        refl
    ; finiteGaugeQuotientCarrierConstructedField =
        finiteGaugeQuotientCarrierConstructed
    ; finiteGaugeQuotientCarrierConstructedFieldIsFalse =
        refl
    ; flatConnectionToVacuumModuloGaugeProvedField =
        flatConnectionToVacuumModuloGaugeProved
    ; flatConnectionToVacuumModuloGaugeProvedFieldIsFalse =
        refl
    ; topologicalSectorClassificationProvedField =
        topologicalSectorClassificationProved
    ; topologicalSectorClassificationProvedFieldIsFalse =
        refl
    ; positiveEnergyForNonVacuumTopologicalSectorsProvedField =
        positiveEnergyForNonVacuumTopologicalSectorsProved
    ; positiveEnergyForNonVacuumTopologicalSectorsProvedFieldIsFalse =
        refl
    ; zeroModeVacuumRigidityProvedField =
        zeroModeVacuumRigidityProved
    ; zeroModeVacuumRigidityProvedFieldIsFalse =
        refl
    ; nonVacuumZeroEnergyModesExcludedField =
        nonVacuumZeroEnergyModesExcluded
    ; nonVacuumZeroEnergyModesExcludedFieldIsFalse =
        refl
    ; hamiltonianDominationImportedAsProofField =
        hamiltonianDominationImportedAsProof
    ; hamiltonianDominationImportedAsProofFieldIsFalse =
        refl
    ; reflectionPositivityOSOnGaugeQuotientProvedField =
        reflectionPositivityOSOnGaugeQuotientProved
    ; reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse =
        refl
    ; continuumTransferNoSpectralPollutionProvedField =
        continuumTransferNoSpectralPollutionProved
    ; continuumTransferNoSpectralPollutionProvedFieldIsFalse =
        refl
    ; finiteYMMassGapPromotedField =
        finiteYMMassGapPromoted
    ; finiteYMMassGapPromotedFieldIsFalse =
        refl
    ; clayYangMillsPromotedField =
        clayYangMillsPromoted
    ; clayYangMillsPromotedFieldIsFalse =
        refl
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        refl
    ; boundary =
        "Consumes finite gauge/Hodge adjoint compatibility and the Hamiltonian-domination boundary"
        ∷ "Names the finite contractible BT/tree target where flat gauge-compatible zero modes should be vacuum modulo gauge"
        ∷ "Separates non-vacuum topological-charge sectors from zero-energy modes; such sectors must carry uniformly positive energy"
        ∷ "Feeds the Hamiltonian domination theorem target rather than importing domination as proof"
        ∷ "Finite gauge quotient, flat-to-vacuum proof, topological sector classification, OS/reflection positivity, continuum no-pollution transfer, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMGaugeZeroModeRigidityStageCountIs9 :
  listCount canonicalYMGaugeZeroModeRigidityStages ≡ 9
canonicalYMGaugeZeroModeRigidityStageCountIs9 =
  refl

canonicalYMGaugeZeroModeRigidityRowCountIs17 :
  listCount canonicalYMGaugeZeroModeRigidityRows ≡ 17
canonicalYMGaugeZeroModeRigidityRowCountIs17 =
  refl

canonicalYMGaugeZeroModeVacuumRigidityBlockerCountIs8 :
  listCount canonicalYMGaugeZeroModeVacuumRigidityBlockers ≡ 8
canonicalYMGaugeZeroModeVacuumRigidityBlockerCountIs8 =
  refl

canonicalYMGaugeZeroModeVacuumRigidityFirstBlocker :
  exactFirstBlocker canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  missingFiniteGaugeQuotientCarrier
canonicalYMGaugeZeroModeVacuumRigidityFirstBlocker =
  refl

canonicalYMGaugeZeroModeVacuumRigidityTargetRecorded :
  zeroModeVacuumRigidityTargetRecordedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  true
canonicalYMGaugeZeroModeVacuumRigidityTargetRecorded =
  refl

canonicalYMGaugeZeroModeVacuumRigidityStillFalse :
  zeroModeVacuumRigidityProvedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  false
canonicalYMGaugeZeroModeVacuumRigidityStillFalse =
  refl

canonicalYMGaugeZeroModeVacuumRigidityNoClayPromotion :
  clayYangMillsPromotedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  false
canonicalYMGaugeZeroModeVacuumRigidityNoClayPromotion =
  refl

canonicalYMGaugeZeroModeVacuumRigidityNoTerminalPromotion :
  terminalPromotionField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  false
canonicalYMGaugeZeroModeVacuumRigidityNoTerminalPromotion =
  refl
