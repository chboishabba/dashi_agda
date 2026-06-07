module DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary where

-- Yang-Mills gauge zero-mode sheaf-rigidity boundary.
--
-- This module records the finite zero-mode classification target sitting
-- between finite gauge/Hodge compatibility and Hamiltonian domination:
--
--   finite BT/building patches
--   -> local gauge/Hodge zero-mode sheaf
--   -> cocycle-compatible gluing
--   -> global sections are either vacuum/flat trivial or holonomy/topological
--      sectors with a uniformly positive action target
--
-- If a finite model has non-vacuum topological-charge sectors, they must be
-- classified separately and assigned uniformly positive energy; they are not
-- zero-energy gauge-compatible modes.  This file is only a finite boundary
-- target feeding YMHamiltonianDominatesFiniteHodgeDefectBoundary.  Level-zero,
-- cuspidal, and BT-cohomology inputs are recorded as external-boundary rows,
-- not as proof.  This module does not construct the gauge quotient carrier,
-- prove sheaf rigidity, prove Hamiltonian domination, prove OS/reflection
-- positivity, transfer through the continuum limit, or promote Yang-Mills Clay.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
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

  gaugeZeroModeSheafRigidityTargetNamedPromotionBlocked :
    YMGaugeZeroModeVacuumRigidityStatus

data YMGaugeZeroModeRigidityStage : Set where
  finiteContractibleComplexStage :
    YMGaugeZeroModeRigidityStage

  finiteBTBuildingPatchSiteStage :
    YMGaugeZeroModeRigidityStage

  finiteGaugeQuotientCarrierStage :
    YMGaugeZeroModeRigidityStage

  gaugeHodgeCompatibleZeroModeStage :
    YMGaugeZeroModeRigidityStage

  localGaugeHodgeZeroModeSheafStage :
    YMGaugeZeroModeRigidityStage

  gluingCocycleCompatibilityStage :
    YMGaugeZeroModeRigidityStage

  flatConnectionClassificationStage :
    YMGaugeZeroModeRigidityStage

  vacuumModuloGaugeStage :
    YMGaugeZeroModeRigidityStage

  holonomyClassificationStage :
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
  ∷ finiteBTBuildingPatchSiteStage
  ∷ finiteGaugeQuotientCarrierStage
  ∷ gaugeHodgeCompatibleZeroModeStage
  ∷ localGaugeHodgeZeroModeSheafStage
  ∷ gluingCocycleCompatibilityStage
  ∷ flatConnectionClassificationStage
  ∷ vacuumModuloGaugeStage
  ∷ holonomyClassificationStage
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

  localGaugeHodgeZeroModeSheafNamedRow :
    YMGaugeZeroModeRigidityRow

  gluingCocycleGijGjkGkiNamedRow :
    YMGaugeZeroModeRigidityRow

  flatConnectionSectorNamedRow :
    YMGaugeZeroModeRigidityRow

  vacuumModuloGaugeSectorNamedRow :
    YMGaugeZeroModeRigidityRow

  gaugeVacuumOrFlatTrivialGlobalSectionNamedRow :
    YMGaugeZeroModeRigidityRow

  holonomyClassificationTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  topologicalChargeSectorBoundaryNamedRow :
    YMGaugeZeroModeRigidityRow

  positiveTopologicalEnergyTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  uniformPositiveHolonomyActionTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  levelZeroCuspidalExternalBoundaryRow :
    YMGaugeZeroModeRigidityRow

  bTCohomologyExternalBoundaryRow :
    YMGaugeZeroModeRigidityRow

  zeroModeVacuumRigidityTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  gaugeZeroModeSheafRigidityTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  nonVacuumZeroEnergyExcludedTargetNamedRow :
    YMGaugeZeroModeRigidityRow

  finiteGaugeQuotientStillMissingRow :
    YMGaugeZeroModeRigidityRow

  flatConnectionToVacuumProofStillMissingRow :
    YMGaugeZeroModeRigidityRow

  topologicalSectorClassificationStillMissingRow :
    YMGaugeZeroModeRigidityRow

  gaugeZeroModeSheafRigidityStillMissingRow :
    YMGaugeZeroModeRigidityRow

  holonomyClassificationProofStillMissingRow :
    YMGaugeZeroModeRigidityRow

  uniformPositiveHolonomyActionProofStillMissingRow :
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
  ∷ localGaugeHodgeZeroModeSheafNamedRow
  ∷ gluingCocycleGijGjkGkiNamedRow
  ∷ flatConnectionSectorNamedRow
  ∷ vacuumModuloGaugeSectorNamedRow
  ∷ gaugeVacuumOrFlatTrivialGlobalSectionNamedRow
  ∷ holonomyClassificationTargetNamedRow
  ∷ topologicalChargeSectorBoundaryNamedRow
  ∷ positiveTopologicalEnergyTargetNamedRow
  ∷ uniformPositiveHolonomyActionTargetNamedRow
  ∷ levelZeroCuspidalExternalBoundaryRow
  ∷ bTCohomologyExternalBoundaryRow
  ∷ zeroModeVacuumRigidityTargetNamedRow
  ∷ gaugeZeroModeSheafRigidityTargetNamedRow
  ∷ nonVacuumZeroEnergyExcludedTargetNamedRow
  ∷ finiteGaugeQuotientStillMissingRow
  ∷ flatConnectionToVacuumProofStillMissingRow
  ∷ topologicalSectorClassificationStillMissingRow
  ∷ gaugeZeroModeSheafRigidityStillMissingRow
  ∷ holonomyClassificationProofStillMissingRow
  ∷ uniformPositiveHolonomyActionProofStillMissingRow
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

  missingGaugeZeroModeSheafRigidityProof :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingHolonomyClassificationProof :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingPositiveEnergyForNonVacuumTopologicalSectors :
    YMGaugeZeroModeVacuumRigidityBlocker

  missingUniformPositiveHolonomyActionProof :
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
  ∷ missingGaugeZeroModeSheafRigidityProof
  ∷ missingHolonomyClassificationProof
  ∷ missingPositiveEnergyForNonVacuumTopologicalSectors
  ∷ missingUniformPositiveHolonomyActionProof
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

data FiniteBTBuildingPatchSite : Set where
  finiteBTBuildingPatchSiteTarget :
    FiniteBTBuildingPatchSite

data GaugeCompatibleZeroModeSector : Set where
  gaugeCompatibleZeroModesFromFiniteHodgeDefect :
    Ham.FiniteHodgeGaugeDefectLaplacian →
    GaugeCompatibleZeroModeSector

data LocalGaugeHodgeZeroModeSheaf : Set where
  localGaugeHodgeZeroModeSheafOverFiniteBTPatches :
    FiniteBTBuildingPatchSite →
    GaugeCompatibleZeroModeSector →
    LocalGaugeHodgeZeroModeSheaf

data GaugeTransitionCocycleBoundary : Set where
  gluingCocycleGijGjkGkiEqualsIdentityTarget :
    LocalGaugeHodgeZeroModeSheaf →
    GaugeTransitionCocycleBoundary

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

data HolonomyClassificationTarget : Set where
  globalSectionsVacuumOrHolonomyTopologicalSector :
    LocalGaugeHodgeZeroModeSheaf →
    GaugeTransitionCocycleBoundary →
    VacuumModuloGaugeSector →
    TopologicalChargeSectorBoundary →
    HolonomyClassificationTarget

data PositiveTopologicalEnergyTarget : Set where
  nonVacuumTopologicalChargeCarriesUniformPositiveEnergy :
    TopologicalChargeSectorBoundary →
    PositiveTopologicalEnergyTarget

data UniformPositiveHolonomyActionTarget : Set where
  nonVacuumHolonomySectorCarriesUniformPositiveAction :
    HolonomyClassificationTarget →
    PositiveTopologicalEnergyTarget →
    UniformPositiveHolonomyActionTarget

data LevelZeroCuspidalExternalBoundary : Set where
  levelZeroCuspidalRepresentationCohomologyExternalInput :
    LevelZeroCuspidalExternalBoundary

data BTCohomologyExternalBoundary : Set where
  bruhatTitsBuildingCohomologyClassificationExternalInput :
    LevelZeroCuspidalExternalBoundary →
    BTCohomologyExternalBoundary

data ZeroModeVacuumRigidityTarget : Set where
  compatibleZeroModesAreVacuumModuloGaugeOnContractibleFiniteCarrier :
    GaugeCompatibleZeroModeSector →
    FlatConnectionSector →
    VacuumModuloGaugeSector →
    ZeroModeVacuumRigidityTarget

data GaugeZeroModeSheafRigidityTarget : Set where
  globalGaugeZeroModeSheafSectionsAreVacuumOrPositiveHolonomy :
    LocalGaugeHodgeZeroModeSheaf →
    GaugeTransitionCocycleBoundary →
    HolonomyClassificationTarget →
    UniformPositiveHolonomyActionTarget →
    GaugeZeroModeSheafRigidityTarget

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

canonicalFiniteBTBuildingPatchSite :
  FiniteBTBuildingPatchSite
canonicalFiniteBTBuildingPatchSite =
  finiteBTBuildingPatchSiteTarget

canonicalGaugeCompatibleZeroModeSector :
  GaugeCompatibleZeroModeSector
canonicalGaugeCompatibleZeroModeSector =
  gaugeCompatibleZeroModesFromFiniteHodgeDefect
    Ham.canonicalFiniteHodgeGaugeDefectLaplacian

canonicalLocalGaugeHodgeZeroModeSheaf :
  LocalGaugeHodgeZeroModeSheaf
canonicalLocalGaugeHodgeZeroModeSheaf =
  localGaugeHodgeZeroModeSheafOverFiniteBTPatches
    canonicalFiniteBTBuildingPatchSite
    canonicalGaugeCompatibleZeroModeSector

canonicalGaugeTransitionCocycleBoundary :
  GaugeTransitionCocycleBoundary
canonicalGaugeTransitionCocycleBoundary =
  gluingCocycleGijGjkGkiEqualsIdentityTarget
    canonicalLocalGaugeHodgeZeroModeSheaf

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

canonicalHolonomyClassificationTarget :
  HolonomyClassificationTarget
canonicalHolonomyClassificationTarget =
  globalSectionsVacuumOrHolonomyTopologicalSector
    canonicalLocalGaugeHodgeZeroModeSheaf
    canonicalGaugeTransitionCocycleBoundary
    canonicalVacuumModuloGaugeSector
    canonicalTopologicalChargeSectorBoundary

canonicalPositiveTopologicalEnergyTarget :
  PositiveTopologicalEnergyTarget
canonicalPositiveTopologicalEnergyTarget =
  nonVacuumTopologicalChargeCarriesUniformPositiveEnergy
    canonicalTopologicalChargeSectorBoundary

canonicalUniformPositiveHolonomyActionTarget :
  UniformPositiveHolonomyActionTarget
canonicalUniformPositiveHolonomyActionTarget =
  nonVacuumHolonomySectorCarriesUniformPositiveAction
    canonicalHolonomyClassificationTarget
    canonicalPositiveTopologicalEnergyTarget

canonicalLevelZeroCuspidalExternalBoundary :
  LevelZeroCuspidalExternalBoundary
canonicalLevelZeroCuspidalExternalBoundary =
  levelZeroCuspidalRepresentationCohomologyExternalInput

canonicalBTCohomologyExternalBoundary :
  BTCohomologyExternalBoundary
canonicalBTCohomologyExternalBoundary =
  bruhatTitsBuildingCohomologyClassificationExternalInput
    canonicalLevelZeroCuspidalExternalBoundary

canonicalZeroModeVacuumRigidityTarget :
  ZeroModeVacuumRigidityTarget
canonicalZeroModeVacuumRigidityTarget =
  compatibleZeroModesAreVacuumModuloGaugeOnContractibleFiniteCarrier
    canonicalGaugeCompatibleZeroModeSector
    canonicalFlatConnectionSector
    canonicalVacuumModuloGaugeSector

canonicalGaugeZeroModeSheafRigidityTarget :
  GaugeZeroModeSheafRigidityTarget
canonicalGaugeZeroModeSheafRigidityTarget =
  globalGaugeZeroModeSheafSectionsAreVacuumOrPositiveHolonomy
    canonicalLocalGaugeHodgeZeroModeSheaf
    canonicalGaugeTransitionCocycleBoundary
    canonicalHolonomyClassificationTarget
    canonicalUniformPositiveHolonomyActionTarget

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

gaugeZeroModeSheafRecorded : Bool
gaugeZeroModeSheafRecorded =
  true

gluingCocycleBoundaryRecorded : Bool
gluingCocycleBoundaryRecorded =
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

holonomyClassificationTargetRecorded : Bool
holonomyClassificationTargetRecorded =
  true

uniformPositiveHolonomyActionTargetRecorded : Bool
uniformPositiveHolonomyActionTargetRecorded =
  true

levelZeroCuspidalExternalBoundaryRecorded : Bool
levelZeroCuspidalExternalBoundaryRecorded =
  true

bTCohomologyExternalBoundaryRecorded : Bool
bTCohomologyExternalBoundaryRecorded =
  true

zeroModeVacuumRigidityTargetRecorded : Bool
zeroModeVacuumRigidityTargetRecorded =
  true

gaugeZeroModeSheafRigidityTargetRecorded : Bool
gaugeZeroModeSheafRigidityTargetRecorded =
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

gaugeZeroModeSheafRigidityProved : Bool
gaugeZeroModeSheafRigidityProved =
  false

holonomyClassificationProved : Bool
holonomyClassificationProved =
  false

positiveEnergyForNonVacuumTopologicalSectorsProved : Bool
positiveEnergyForNonVacuumTopologicalSectorsProved =
  false

uniformPositiveHolonomyActionProved : Bool
uniformPositiveHolonomyActionProved =
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

hamiltonianDominationProved : Bool
hamiltonianDominationProved =
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

gaugeZeroModeSheafRecordedIsTrue :
  gaugeZeroModeSheafRecorded ≡ true
gaugeZeroModeSheafRecordedIsTrue =
  refl

gluingCocycleBoundaryRecordedIsTrue :
  gluingCocycleBoundaryRecorded ≡ true
gluingCocycleBoundaryRecordedIsTrue =
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

holonomyClassificationTargetRecordedIsTrue :
  holonomyClassificationTargetRecorded ≡ true
holonomyClassificationTargetRecordedIsTrue =
  refl

uniformPositiveHolonomyActionTargetRecordedIsTrue :
  uniformPositiveHolonomyActionTargetRecorded ≡ true
uniformPositiveHolonomyActionTargetRecordedIsTrue =
  refl

levelZeroCuspidalExternalBoundaryRecordedIsTrue :
  levelZeroCuspidalExternalBoundaryRecorded ≡ true
levelZeroCuspidalExternalBoundaryRecordedIsTrue =
  refl

bTCohomologyExternalBoundaryRecordedIsTrue :
  bTCohomologyExternalBoundaryRecorded ≡ true
bTCohomologyExternalBoundaryRecordedIsTrue =
  refl

zeroModeVacuumRigidityTargetRecordedIsTrue :
  zeroModeVacuumRigidityTargetRecorded ≡ true
zeroModeVacuumRigidityTargetRecordedIsTrue =
  refl

gaugeZeroModeSheafRigidityTargetRecordedIsTrue :
  gaugeZeroModeSheafRigidityTargetRecorded ≡ true
gaugeZeroModeSheafRigidityTargetRecordedIsTrue =
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

gaugeZeroModeSheafRigidityProvedIsFalse :
  gaugeZeroModeSheafRigidityProved ≡ false
gaugeZeroModeSheafRigidityProvedIsFalse =
  refl

holonomyClassificationProvedIsFalse :
  holonomyClassificationProved ≡ false
holonomyClassificationProvedIsFalse =
  refl

positiveEnergyForNonVacuumTopologicalSectorsProvedIsFalse :
  positiveEnergyForNonVacuumTopologicalSectorsProved ≡ false
positiveEnergyForNonVacuumTopologicalSectorsProvedIsFalse =
  refl

uniformPositiveHolonomyActionProvedIsFalse :
  uniformPositiveHolonomyActionProved ≡ false
uniformPositiveHolonomyActionProvedIsFalse =
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

hamiltonianDominationProvedIsFalse :
  hamiltonianDominationProved ≡ false
hamiltonianDominationProvedIsFalse =
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

    finiteBTBuildingPatchSite :
      FiniteBTBuildingPatchSite

    finiteBTBuildingPatchSiteIsCanonical :
      finiteBTBuildingPatchSite
      ≡
      canonicalFiniteBTBuildingPatchSite

    localGaugeHodgeZeroModeSheaf :
      LocalGaugeHodgeZeroModeSheaf

    localGaugeHodgeZeroModeSheafIsCanonical :
      localGaugeHodgeZeroModeSheaf
      ≡
      canonicalLocalGaugeHodgeZeroModeSheaf

    gaugeTransitionCocycleBoundary :
      GaugeTransitionCocycleBoundary

    gaugeTransitionCocycleBoundaryIsCanonical :
      gaugeTransitionCocycleBoundary
      ≡
      canonicalGaugeTransitionCocycleBoundary

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

    holonomyClassificationTarget :
      HolonomyClassificationTarget

    holonomyClassificationTargetIsCanonical :
      holonomyClassificationTarget
      ≡
      canonicalHolonomyClassificationTarget

    uniformPositiveHolonomyActionTarget :
      UniformPositiveHolonomyActionTarget

    uniformPositiveHolonomyActionTargetIsCanonical :
      uniformPositiveHolonomyActionTarget
      ≡
      canonicalUniformPositiveHolonomyActionTarget

    levelZeroCuspidalExternalBoundary :
      LevelZeroCuspidalExternalBoundary

    levelZeroCuspidalExternalBoundaryIsCanonical :
      levelZeroCuspidalExternalBoundary
      ≡
      canonicalLevelZeroCuspidalExternalBoundary

    bTCohomologyExternalBoundary :
      BTCohomologyExternalBoundary

    bTCohomologyExternalBoundaryIsCanonical :
      bTCohomologyExternalBoundary
      ≡
      canonicalBTCohomologyExternalBoundary

    zeroModeVacuumRigidityTarget :
      ZeroModeVacuumRigidityTarget

    zeroModeVacuumRigidityTargetIsCanonical :
      zeroModeVacuumRigidityTarget
      ≡
      canonicalZeroModeVacuumRigidityTarget

    gaugeZeroModeSheafRigidityTarget :
      GaugeZeroModeSheafRigidityTarget

    gaugeZeroModeSheafRigidityTargetIsCanonical :
      gaugeZeroModeSheafRigidityTarget
      ≡
      canonicalGaugeZeroModeSheafRigidityTarget

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

    stageCountIs13 :
      stageCount ≡ 13

    rowCount :
      Nat

    rowCountIs28 :
      rowCount ≡ 28

    blockerCount :
      Nat

    blockerCountIs11 :
      blockerCount ≡ 11

    finiteBTTreeContractibilityTargetRecordedField :
      Bool

    finiteBTTreeContractibilityTargetRecordedFieldIsTrue :
      finiteBTTreeContractibilityTargetRecordedField ≡ true

    gaugeCompatibleZeroModeSectorTargetRecordedField :
      Bool

    gaugeCompatibleZeroModeSectorTargetRecordedFieldIsTrue :
      gaugeCompatibleZeroModeSectorTargetRecordedField ≡ true

    gaugeZeroModeSheafRecordedField :
      Bool

    gaugeZeroModeSheafRecordedFieldIsTrue :
      gaugeZeroModeSheafRecordedField ≡ true

    gluingCocycleBoundaryRecordedField :
      Bool

    gluingCocycleBoundaryRecordedFieldIsTrue :
      gluingCocycleBoundaryRecordedField ≡ true

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

    holonomyClassificationTargetRecordedField :
      Bool

    holonomyClassificationTargetRecordedFieldIsTrue :
      holonomyClassificationTargetRecordedField ≡ true

    uniformPositiveHolonomyActionTargetRecordedField :
      Bool

    uniformPositiveHolonomyActionTargetRecordedFieldIsTrue :
      uniformPositiveHolonomyActionTargetRecordedField ≡ true

    levelZeroCuspidalExternalBoundaryRecordedField :
      Bool

    levelZeroCuspidalExternalBoundaryRecordedFieldIsTrue :
      levelZeroCuspidalExternalBoundaryRecordedField ≡ true

    bTCohomologyExternalBoundaryRecordedField :
      Bool

    bTCohomologyExternalBoundaryRecordedFieldIsTrue :
      bTCohomologyExternalBoundaryRecordedField ≡ true

    zeroModeVacuumRigidityTargetRecordedField :
      Bool

    zeroModeVacuumRigidityTargetRecordedFieldIsTrue :
      zeroModeVacuumRigidityTargetRecordedField ≡ true

    gaugeZeroModeSheafRigidityTargetRecordedField :
      Bool

    gaugeZeroModeSheafRigidityTargetRecordedFieldIsTrue :
      gaugeZeroModeSheafRigidityTargetRecordedField ≡ true

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

    gaugeZeroModeSheafRigidityProvedField :
      Bool

    gaugeZeroModeSheafRigidityProvedFieldIsFalse :
      gaugeZeroModeSheafRigidityProvedField ≡ false

    holonomyClassificationProvedField :
      Bool

    holonomyClassificationProvedFieldIsFalse :
      holonomyClassificationProvedField ≡ false

    positiveEnergyForNonVacuumTopologicalSectorsProvedField :
      Bool

    positiveEnergyForNonVacuumTopologicalSectorsProvedFieldIsFalse :
      positiveEnergyForNonVacuumTopologicalSectorsProvedField ≡ false

    uniformPositiveHolonomyActionProvedField :
      Bool

    uniformPositiveHolonomyActionProvedFieldIsFalse :
      uniformPositiveHolonomyActionProvedField ≡ false

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

    hamiltonianDominationProvedField :
      Bool

    hamiltonianDominationProvedFieldIsFalse :
      hamiltonianDominationProvedField ≡ false

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
        gaugeZeroModeSheafRigidityTargetNamedPromotionBlocked
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
    ; finiteBTBuildingPatchSite =
        canonicalFiniteBTBuildingPatchSite
    ; finiteBTBuildingPatchSiteIsCanonical =
        refl
    ; localGaugeHodgeZeroModeSheaf =
        canonicalLocalGaugeHodgeZeroModeSheaf
    ; localGaugeHodgeZeroModeSheafIsCanonical =
        refl
    ; gaugeTransitionCocycleBoundary =
        canonicalGaugeTransitionCocycleBoundary
    ; gaugeTransitionCocycleBoundaryIsCanonical =
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
    ; holonomyClassificationTarget =
        canonicalHolonomyClassificationTarget
    ; holonomyClassificationTargetIsCanonical =
        refl
    ; uniformPositiveHolonomyActionTarget =
        canonicalUniformPositiveHolonomyActionTarget
    ; uniformPositiveHolonomyActionTargetIsCanonical =
        refl
    ; levelZeroCuspidalExternalBoundary =
        canonicalLevelZeroCuspidalExternalBoundary
    ; levelZeroCuspidalExternalBoundaryIsCanonical =
        refl
    ; bTCohomologyExternalBoundary =
        canonicalBTCohomologyExternalBoundary
    ; bTCohomologyExternalBoundaryIsCanonical =
        refl
    ; zeroModeVacuumRigidityTarget =
        canonicalZeroModeVacuumRigidityTarget
    ; zeroModeVacuumRigidityTargetIsCanonical =
        refl
    ; gaugeZeroModeSheafRigidityTarget =
        canonicalGaugeZeroModeSheafRigidityTarget
    ; gaugeZeroModeSheafRigidityTargetIsCanonical =
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
        13
    ; stageCountIs13 =
        refl
    ; rowCount =
        28
    ; rowCountIs28 =
        refl
    ; blockerCount =
        11
    ; blockerCountIs11 =
        refl
    ; finiteBTTreeContractibilityTargetRecordedField =
        finiteBTTreeContractibilityTargetRecorded
    ; finiteBTTreeContractibilityTargetRecordedFieldIsTrue =
        refl
    ; gaugeCompatibleZeroModeSectorTargetRecordedField =
        gaugeCompatibleZeroModeSectorTargetRecorded
    ; gaugeCompatibleZeroModeSectorTargetRecordedFieldIsTrue =
        refl
    ; gaugeZeroModeSheafRecordedField =
        gaugeZeroModeSheafRecorded
    ; gaugeZeroModeSheafRecordedFieldIsTrue =
        refl
    ; gluingCocycleBoundaryRecordedField =
        gluingCocycleBoundaryRecorded
    ; gluingCocycleBoundaryRecordedFieldIsTrue =
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
    ; holonomyClassificationTargetRecordedField =
        holonomyClassificationTargetRecorded
    ; holonomyClassificationTargetRecordedFieldIsTrue =
        refl
    ; uniformPositiveHolonomyActionTargetRecordedField =
        uniformPositiveHolonomyActionTargetRecorded
    ; uniformPositiveHolonomyActionTargetRecordedFieldIsTrue =
        refl
    ; levelZeroCuspidalExternalBoundaryRecordedField =
        levelZeroCuspidalExternalBoundaryRecorded
    ; levelZeroCuspidalExternalBoundaryRecordedFieldIsTrue =
        refl
    ; bTCohomologyExternalBoundaryRecordedField =
        bTCohomologyExternalBoundaryRecorded
    ; bTCohomologyExternalBoundaryRecordedFieldIsTrue =
        refl
    ; zeroModeVacuumRigidityTargetRecordedField =
        zeroModeVacuumRigidityTargetRecorded
    ; zeroModeVacuumRigidityTargetRecordedFieldIsTrue =
        refl
    ; gaugeZeroModeSheafRigidityTargetRecordedField =
        gaugeZeroModeSheafRigidityTargetRecorded
    ; gaugeZeroModeSheafRigidityTargetRecordedFieldIsTrue =
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
    ; gaugeZeroModeSheafRigidityProvedField =
        gaugeZeroModeSheafRigidityProved
    ; gaugeZeroModeSheafRigidityProvedFieldIsFalse =
        refl
    ; holonomyClassificationProvedField =
        holonomyClassificationProved
    ; holonomyClassificationProvedFieldIsFalse =
        refl
    ; positiveEnergyForNonVacuumTopologicalSectorsProvedField =
        positiveEnergyForNonVacuumTopologicalSectorsProved
    ; positiveEnergyForNonVacuumTopologicalSectorsProvedFieldIsFalse =
        refl
    ; uniformPositiveHolonomyActionProvedField =
        uniformPositiveHolonomyActionProved
    ; uniformPositiveHolonomyActionProvedFieldIsFalse =
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
    ; hamiltonianDominationProvedField =
        hamiltonianDominationProved
    ; hamiltonianDominationProvedFieldIsFalse =
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
        ∷ "Names the local gauge/Hodge zero-mode sheaf over finite BT/building patches and the gluing cocycle g_ij g_jk g_ki boundary"
        ∷ "Classifies the target global sections as gauge vacuum or flat trivial sector, or holonomy/topological sector with uniformly positive action"
        ∷ "Records level-zero cuspidal and BT-building cohomology rows as external boundaries only"
        ∷ "Feeds the Hamiltonian domination theorem target rather than importing domination as proof"
        ∷ "Finite gauge quotient, sheaf rigidity proof, holonomy classification proof, Hamiltonian domination, OS/reflection positivity, continuum no-pollution transfer, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMGaugeZeroModeRigidityStageCountIs13 :
  listCount canonicalYMGaugeZeroModeRigidityStages ≡ 13
canonicalYMGaugeZeroModeRigidityStageCountIs13 =
  refl

canonicalYMGaugeZeroModeRigidityRowCountIs28 :
  listCount canonicalYMGaugeZeroModeRigidityRows ≡ 28
canonicalYMGaugeZeroModeRigidityRowCountIs28 =
  refl

canonicalYMGaugeZeroModeVacuumRigidityBlockerCountIs11 :
  listCount canonicalYMGaugeZeroModeVacuumRigidityBlockers ≡ 11
canonicalYMGaugeZeroModeVacuumRigidityBlockerCountIs11 =
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

canonicalYMGaugeZeroModeSheafRecorded :
  gaugeZeroModeSheafRecordedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  true
canonicalYMGaugeZeroModeSheafRecorded =
  refl

canonicalYMHolonomyClassificationTargetRecorded :
  holonomyClassificationTargetRecordedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  true
canonicalYMHolonomyClassificationTargetRecorded =
  refl

canonicalYMGaugeZeroModeSheafRigidityStillFalse :
  gaugeZeroModeSheafRigidityProvedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  false
canonicalYMGaugeZeroModeSheafRigidityStillFalse =
  refl

canonicalYMHolonomyClassificationStillFalse :
  holonomyClassificationProvedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  false
canonicalYMHolonomyClassificationStillFalse =
  refl

canonicalYMHamiltonianDominationStillFalse :
  hamiltonianDominationProvedField
    canonicalYMGaugeZeroModeVacuumRigidityBoundary
  ≡
  false
canonicalYMHamiltonianDominationStillFalse =
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

------------------------------------------------------------------------
-- Fail-closed substantial receipt.

data YMGaugeZeroModeVacuumRigidityPromotionToken : Set where

yMGaugeZeroModeVacuumRigidityPromotionTokenImpossibleHere :
  YMGaugeZeroModeVacuumRigidityPromotionToken →
  ⊥
yMGaugeZeroModeVacuumRigidityPromotionTokenImpossibleHere ()

canonicalYMGaugeZeroModeVacuumRigidityFailClosedFindings :
  List String
canonicalYMGaugeZeroModeVacuumRigidityFailClosedFindings =
  "Typed target only: local gauge/Hodge zero-mode sheaf, gluing cocycle, vacuum/flat sector, and holonomy/topological sector are named for finite BT/building patches"
  ∷ "Fail-closed first blocker: the finite gauge quotient carrier is still missing"
  ∷ "Rigidity blocker: no GaugeZeroModeSheafRigidity proof or holonomy classification proof is constructed here"
  ∷ "External-boundary rows: level-zero/cuspidal representation and BT-building cohomology inputs are recorded, not proved"
  ∷ "Topological blocker: non-vacuum holonomy or charge sectors require uniformly positive action before zero-energy exclusion"
  ∷ "Hamiltonian input is consumed through its fail-closed domination boundary; domination is not imported or proved here"
  ∷ "OS/reflection positivity, continuum no-pollution transfer, finite YM mass-gap, Clay Yang-Mills, and terminal promotion remain false"
  ∷ []

canonicalYMGaugeZeroModeVacuumRigidityFailClosedNonPromotions :
  List YMGaugeZeroModeVacuumRigidityBlocker
canonicalYMGaugeZeroModeVacuumRigidityFailClosedNonPromotions =
  missingFiniteGaugeQuotientCarrier
  ∷ missingFlatConnectionToVacuumModuloGaugeProof
  ∷ missingTopologicalSectorClassification
  ∷ missingGaugeZeroModeSheafRigidityProof
  ∷ missingHolonomyClassificationProof
  ∷ missingPositiveEnergyForNonVacuumTopologicalSectors
  ∷ missingUniformPositiveHolonomyActionProof
  ∷ missingHamiltonianDominatesFiniteHodgeDefect
  ∷ missingReflectionPositivityOSOnGaugeQuotient
  ∷ missingContinuumTransferNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record YMGaugeZeroModeVacuumRigidityFailClosedReceipt : Setω where
  field
    theoremBoundary :
      YMGaugeZeroModeVacuumRigidityBoundary

    theoremBoundaryCanonical :
      Bool

    theoremBoundaryCanonicalIsTrue :
      theoremBoundaryCanonical ≡ true

    consumedHamiltonianFailClosedReceipt :
      Ham.YMHamiltonianDominationFailClosedReceipt

    consumedHamiltonianFailClosedReceiptCanonical :
      Bool

    consumedHamiltonianFailClosedReceiptCanonicalIsTrue :
      consumedHamiltonianFailClosedReceiptCanonical ≡ true

    target :
      ZeroModeVacuumRigidityTarget

    targetIsCanonical :
      target ≡ canonicalZeroModeVacuumRigidityTarget

    sheafRigidityTarget :
      GaugeZeroModeSheafRigidityTarget

    sheafRigidityTargetIsCanonical :
      sheafRigidityTarget
      ≡
      canonicalGaugeZeroModeSheafRigidityTarget

    nonVacuumExclusionTarget :
      NonVacuumZeroEnergyExclusionTarget

    nonVacuumExclusionTargetIsCanonical :
      nonVacuumExclusionTarget
      ≡
      canonicalNonVacuumZeroEnergyExclusionTarget

    targetRecorded :
      zeroModeVacuumRigidityTargetRecordedField theoremBoundary ≡ true

    theoremStillMissing :
      zeroModeVacuumRigidityProvedField theoremBoundary ≡ false

    gaugeZeroModeSheafRecordedInBoundary :
      gaugeZeroModeSheafRecordedField theoremBoundary ≡ true

    holonomyClassificationTargetRecordedInBoundary :
      holonomyClassificationTargetRecordedField theoremBoundary ≡ true

    sheafRigidityStillMissing :
      gaugeZeroModeSheafRigidityProvedField theoremBoundary ≡ false

    holonomyClassificationStillMissing :
      holonomyClassificationProvedField theoremBoundary ≡ false

    nonVacuumZeroEnergyExclusionStillMissing :
      nonVacuumZeroEnergyModesExcludedField theoremBoundary ≡ false

    finiteGaugeQuotientStillMissing :
      finiteGaugeQuotientCarrierConstructedField theoremBoundary ≡ false

    flatToVacuumProofStillMissing :
      flatConnectionToVacuumModuloGaugeProvedField theoremBoundary ≡ false

    topologicalClassificationStillMissing :
      topologicalSectorClassificationProvedField theoremBoundary ≡ false

    positiveTopologicalEnergyStillMissing :
      positiveEnergyForNonVacuumTopologicalSectorsProvedField theoremBoundary
      ≡
      false

    uniformPositiveHolonomyActionStillMissing :
      uniformPositiveHolonomyActionProvedField theoremBoundary ≡ false

    hamiltonianDominationStillMissing :
      hamiltonianDominationImportedAsProofField theoremBoundary ≡ false

    hamiltonianDominationProvedStillFalse :
      hamiltonianDominationProvedField theoremBoundary ≡ false

    hamiltonianFailClosedReceiptConsumed :
      Bool

    hamiltonianFailClosedReceiptConsumedIsTrue :
      hamiltonianFailClosedReceiptConsumed ≡ true

    osOnGaugeQuotientStillMissing :
      reflectionPositivityOSOnGaugeQuotientProvedField theoremBoundary
      ≡
      false

    continuumNoPollutionStillMissing :
      continuumTransferNoSpectralPollutionProvedField theoremBoundary
      ≡
      false

    finiteYMMassGapStillFalse :
      finiteYMMassGapPromotedField theoremBoundary ≡ false

    clayPromotionStillFalse :
      clayYangMillsPromotedField theoremBoundary ≡ false

    terminalPromotionStillFalse :
      terminalPromotionField theoremBoundary ≡ false

    blockerLedger :
      List YMGaugeZeroModeVacuumRigidityBlocker

    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalYMGaugeZeroModeVacuumRigidityBlockers

    exactFailClosedNonPromotions :
      List YMGaugeZeroModeVacuumRigidityBlocker

    exactFailClosedNonPromotionsAreCanonical :
      exactFailClosedNonPromotions
      ≡
      canonicalYMGaugeZeroModeVacuumRigidityFailClosedNonPromotions

    firstFailClosedBlocker :
      YMGaugeZeroModeVacuumRigidityBlocker

    firstFailClosedBlockerIsFiniteGaugeQuotient :
      firstFailClosedBlocker ≡ missingFiniteGaugeQuotientCarrier

    rigidityFailClosedBlocker :
      YMGaugeZeroModeVacuumRigidityBlocker

    rigidityFailClosedBlockerIsFlatToVacuum :
      rigidityFailClosedBlocker
      ≡
      missingFlatConnectionToVacuumModuloGaugeProof

    noPromotionTokenEliminator :
      YMGaugeZeroModeVacuumRigidityPromotionToken →
      ⊥

    findings :
      List String

    findingsAreCanonical :
      findings
      ≡
      canonicalYMGaugeZeroModeVacuumRigidityFailClosedFindings

open YMGaugeZeroModeVacuumRigidityFailClosedReceipt public

canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt :
  YMGaugeZeroModeVacuumRigidityFailClosedReceipt
canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt =
  record
    { theoremBoundary =
        canonicalYMGaugeZeroModeVacuumRigidityBoundary
    ; theoremBoundaryCanonical =
        true
    ; theoremBoundaryCanonicalIsTrue =
        refl
    ; consumedHamiltonianFailClosedReceipt =
        Ham.canonicalYMHamiltonianDominationFailClosedReceipt
    ; consumedHamiltonianFailClosedReceiptCanonical =
        true
    ; consumedHamiltonianFailClosedReceiptCanonicalIsTrue =
        refl
    ; target =
        canonicalZeroModeVacuumRigidityTarget
    ; targetIsCanonical =
        refl
    ; sheafRigidityTarget =
        canonicalGaugeZeroModeSheafRigidityTarget
    ; sheafRigidityTargetIsCanonical =
        refl
    ; nonVacuumExclusionTarget =
        canonicalNonVacuumZeroEnergyExclusionTarget
    ; nonVacuumExclusionTargetIsCanonical =
        refl
    ; targetRecorded =
        refl
    ; theoremStillMissing =
        refl
    ; gaugeZeroModeSheafRecordedInBoundary =
        refl
    ; holonomyClassificationTargetRecordedInBoundary =
        refl
    ; sheafRigidityStillMissing =
        refl
    ; holonomyClassificationStillMissing =
        refl
    ; nonVacuumZeroEnergyExclusionStillMissing =
        refl
    ; finiteGaugeQuotientStillMissing =
        refl
    ; flatToVacuumProofStillMissing =
        refl
    ; topologicalClassificationStillMissing =
        refl
    ; positiveTopologicalEnergyStillMissing =
        refl
    ; uniformPositiveHolonomyActionStillMissing =
        refl
    ; hamiltonianDominationStillMissing =
        refl
    ; hamiltonianDominationProvedStillFalse =
        refl
    ; hamiltonianFailClosedReceiptConsumed =
        true
    ; hamiltonianFailClosedReceiptConsumedIsTrue =
        refl
    ; osOnGaugeQuotientStillMissing =
        refl
    ; continuumNoPollutionStillMissing =
        refl
    ; finiteYMMassGapStillFalse =
        refl
    ; clayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    ; blockerLedger =
        canonicalYMGaugeZeroModeVacuumRigidityBlockers
    ; blockerLedgerIsCanonical =
        refl
    ; exactFailClosedNonPromotions =
        canonicalYMGaugeZeroModeVacuumRigidityFailClosedNonPromotions
    ; exactFailClosedNonPromotionsAreCanonical =
        refl
    ; firstFailClosedBlocker =
        missingFiniteGaugeQuotientCarrier
    ; firstFailClosedBlockerIsFiniteGaugeQuotient =
        refl
    ; rigidityFailClosedBlocker =
        missingFlatConnectionToVacuumModuloGaugeProof
    ; rigidityFailClosedBlockerIsFlatToVacuum =
        refl
    ; noPromotionTokenEliminator =
        yMGaugeZeroModeVacuumRigidityPromotionTokenImpossibleHere
    ; findings =
        canonicalYMGaugeZeroModeVacuumRigidityFailClosedFindings
    ; findingsAreCanonical =
        refl
    }

canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsTheoremFalse :
  theoremStillMissing
    canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt
  ≡
  refl
canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsTheoremFalse =
  refl

canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsExclusionFalse :
  nonVacuumZeroEnergyExclusionStillMissing
    canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt
  ≡
  refl
canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsExclusionFalse =
  refl

canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsClayFalse :
  clayPromotionStillFalse
    canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt
  ≡
  refl
canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsClayFalse =
  refl

canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsTerminalFalse :
  terminalPromotionStillFalse
    canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt
  ≡
  refl
canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceiptKeepsTerminalFalse =
  refl
