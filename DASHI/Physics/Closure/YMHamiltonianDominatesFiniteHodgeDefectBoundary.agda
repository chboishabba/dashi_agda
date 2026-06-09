module DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary where

-- Yang-Mills Hamiltonian domination boundary.
--
-- The finite BT/Hodge lane now has selected finite Hodge algebra, selected
-- variation pairing, finite metric/gauge kappa targets, and finite kappa
-- sample arithmetic.  The next physical theorem is stronger than another
-- local kappa receipt:
--
--   on the finite gauge quotient, the transfer-matrix Hamiltonian dominates
--   the finite Hodge/gauge defect Laplacian plus the holonomy/topological
--   sector cost up to controlled errors.
--
-- Symbolically this target is:
--
--   H_d | Omega^\perp  >=  c * Delta_YM,d + c' * Hol_d - E_d.
--
-- This file records the exact theorem boundary and its blockers.  It does not
-- construct the quotient Hamiltonian, does not prove OS/reflection positivity
-- on the quotient, does not import a finite-a strong-coupling gap as an
-- accepted Clay authority, and keeps spectral-gap, continuum-transfer,
-- Clay Yang-Mills, and terminal promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary as Kappa
import DASHI.Physics.Closure.YMWeightedBTAdjointKappaCalculation as Weighted
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientGapBoundary as Gap
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientRequirementNormalizer as Normalizer

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Route status, stages, rows, and blockers.

data YMHamiltonianDominationStatus : Set where
  finiteHodgeDefectSupportPresentHamiltonianDominationStillMissing :
    YMHamiltonianDominationStatus

data YMHamiltonianDominationStage : Set where
  finiteHodgeGaugeDefectLaplacianStage :
    YMHamiltonianDominationStage

  finiteGaugeQuotientCarrierStage :
    YMHamiltonianDominationStage

  transferMatrixHamiltonianStage :
    YMHamiltonianDominationStage

  reflectionPositivityOSStage :
    YMHamiltonianDominationStage

  dominationInequalityStage :
    YMHamiltonianDominationStage

  holonomyCostCarrierStage :
    YMHamiltonianDominationStage

  topologicalSectorPositiveActionStage :
    YMHamiltonianDominationStage

  finiteAStrongCouplingGapSourceStage :
    YMHamiltonianDominationStage

  finiteKappaSupportStage :
    YMHamiltonianDominationStage

  continuumTransferStage :
    YMHamiltonianDominationStage

canonicalYMHamiltonianDominationStages :
  List YMHamiltonianDominationStage
canonicalYMHamiltonianDominationStages =
  finiteHodgeGaugeDefectLaplacianStage
  ∷ finiteGaugeQuotientCarrierStage
  ∷ transferMatrixHamiltonianStage
  ∷ reflectionPositivityOSStage
  ∷ dominationInequalityStage
  ∷ holonomyCostCarrierStage
  ∷ topologicalSectorPositiveActionStage
  ∷ finiteAStrongCouplingGapSourceStage
  ∷ finiteKappaSupportStage
  ∷ continuumTransferStage
  ∷ []

data YMHamiltonianDominationRow : Set where
  selfAdjointQuotientGapBoundaryConsumedRow :
    YMHamiltonianDominationRow

  weightedBTAdjointKappaCalculationConsumedRow :
    YMHamiltonianDominationRow

  selfAdjointRequirementNormalizerConsumedRow :
    YMHamiltonianDominationRow

  btFiniteMetricGaugeKappaBoundaryConsumedRow :
    YMHamiltonianDominationRow

  transferMatrixTargetRow :
    YMHamiltonianDominationRow

  osReflectionPositivityTargetRow :
    YMHamiltonianDominationRow

  gaugeQuotientTargetRow :
    YMHamiltonianDominationRow

  finiteHodgeDefectLaplacianTargetRow :
    YMHamiltonianDominationRow

  dominationInequalityTargetRow :
    YMHamiltonianDominationRow

  dominationPlusHolonomyTargetRow :
    YMHamiltonianDominationRow

  holonomyCostCarrierTargetRow :
    YMHamiltonianDominationRow

  topologicalSectorPositiveActionTargetRow :
    YMHamiltonianDominationRow

  controlledErrorTermTargetRow :
    YMHamiltonianDominationRow

  finiteAStrongCouplingGapSourceBoundaryRow :
    YMHamiltonianDominationRow

  finiteKappaSupportFromWeightedCalculationRow :
    YMHamiltonianDominationRow

  finiteKappaSupportFromBTMetricBoundaryRow :
    YMHamiltonianDominationRow

  uniformKappaSourceStillOpenRow :
    YMHamiltonianDominationRow

  selfAdjointQuotientStillOpenRow :
    YMHamiltonianDominationRow

  spectralLiftStillOpenRow :
    YMHamiltonianDominationRow

  continuumTransferStillOpenRow :
    YMHamiltonianDominationRow

  clayAndTerminalHeldFalseRow :
    YMHamiltonianDominationRow

canonicalYMHamiltonianDominationRows :
  List YMHamiltonianDominationRow
canonicalYMHamiltonianDominationRows =
  selfAdjointQuotientGapBoundaryConsumedRow
  ∷ weightedBTAdjointKappaCalculationConsumedRow
  ∷ selfAdjointRequirementNormalizerConsumedRow
  ∷ btFiniteMetricGaugeKappaBoundaryConsumedRow
  ∷ transferMatrixTargetRow
  ∷ osReflectionPositivityTargetRow
  ∷ gaugeQuotientTargetRow
  ∷ finiteHodgeDefectLaplacianTargetRow
  ∷ dominationInequalityTargetRow
  ∷ dominationPlusHolonomyTargetRow
  ∷ holonomyCostCarrierTargetRow
  ∷ topologicalSectorPositiveActionTargetRow
  ∷ controlledErrorTermTargetRow
  ∷ finiteAStrongCouplingGapSourceBoundaryRow
  ∷ finiteKappaSupportFromWeightedCalculationRow
  ∷ finiteKappaSupportFromBTMetricBoundaryRow
  ∷ uniformKappaSourceStillOpenRow
  ∷ selfAdjointQuotientStillOpenRow
  ∷ spectralLiftStillOpenRow
  ∷ continuumTransferStillOpenRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

data YMHamiltonianDominationBlocker : Set where
  missingFiniteGaugeQuotientCarrier :
    YMHamiltonianDominationBlocker

  missingTransferMatrixPhysicalHamiltonianIdentification :
    YMHamiltonianDominationBlocker

  missingReflectionPositivityOSOnGaugeQuotient :
    YMHamiltonianDominationBlocker

  missingFiniteHodgeDefectLaplacianOperator :
    YMHamiltonianDominationBlocker

  missingHamiltonianDominatesFiniteHodgeDefectInequality :
    YMHamiltonianDominationBlocker

  missingHamiltonianDominatesDefectPlusHolonomyInequality :
    YMHamiltonianDominationBlocker

  missingHolonomyCostCarrierConstruction :
    YMHamiltonianDominationBlocker

  missingPositiveActionForTopologicalSectors :
    YMHamiltonianDominationBlocker

  missingControlledErrorAbsorption :
    YMHamiltonianDominationBlocker

  missingAcceptedFiniteAStrongCouplingGapSource :
    YMHamiltonianDominationBlocker

  missingUniformKappaInfimumPositive :
    YMHamiltonianDominationBlocker

  missingSelfAdjointSpectralGapLift :
    YMHamiltonianDominationBlocker

  missingContinuumTransferNoSpectralPollution :
    YMHamiltonianDominationBlocker

  missingClayYangMillsAuthorityToken :
    YMHamiltonianDominationBlocker

canonicalYMHamiltonianDominationBlockers :
  List YMHamiltonianDominationBlocker
canonicalYMHamiltonianDominationBlockers =
  missingFiniteGaugeQuotientCarrier
  ∷ missingTransferMatrixPhysicalHamiltonianIdentification
  ∷ missingReflectionPositivityOSOnGaugeQuotient
  ∷ missingFiniteHodgeDefectLaplacianOperator
  ∷ missingHamiltonianDominatesFiniteHodgeDefectInequality
  ∷ missingHamiltonianDominatesDefectPlusHolonomyInequality
  ∷ missingHolonomyCostCarrierConstruction
  ∷ missingPositiveActionForTopologicalSectors
  ∷ missingControlledErrorAbsorption
  ∷ missingAcceptedFiniteAStrongCouplingGapSource
  ∷ missingUniformKappaInfimumPositive
  ∷ missingSelfAdjointSpectralGapLift
  ∷ missingContinuumTransferNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

------------------------------------------------------------------------
-- The exact theorem target and its finite-a source boundary.

data FiniteGaugeQuotientSector : Set where
  omegaOrthogonalGaugeQuotientSector :
    FiniteGaugeQuotientSector

data FiniteHodgeGaugeDefectLaplacian : Set where
  deltaYMDFromGaugeHodgeDefect :
    FiniteHodgeGaugeDefectLaplacian

data TransferMatrixHamiltonian : Set where
  logTransferMatrixHamiltonianOnGaugeQuotient :
    TransferMatrixHamiltonian

data ControlledDominationError : Set where
  finiteDepthControlledErrorTerm :
    ControlledDominationError

data HolonomyCostCarrier : Set where
  finiteDepthHolonomyTopologicalCost :
    HolonomyCostCarrier

data TopologicalSectorPositiveActionTarget : Set where
  nonVacuumTopologicalSectorsHavePositiveActionTarget :
    HolonomyCostCarrier →
    TopologicalSectorPositiveActionTarget

data HamiltonianDominationInequalityTarget : Set where
  hamiltonianDominatesFiniteHodgeDefectTarget :
    FiniteGaugeQuotientSector →
    TransferMatrixHamiltonian →
    FiniteHodgeGaugeDefectLaplacian →
    ControlledDominationError →
    HamiltonianDominationInequalityTarget

  hamiltonianDominatesDefectPlusHolonomyTarget :
    FiniteGaugeQuotientSector →
    TransferMatrixHamiltonian →
    FiniteHodgeGaugeDefectLaplacian →
    HolonomyCostCarrier →
    ControlledDominationError →
    HamiltonianDominationInequalityTarget

data FiniteAGapSourceBoundary : Set where
  finiteAStrongCouplingGapSourceNotAcceptedAsClayAuthority :
    FiniteAGapSourceBoundary

canonicalFiniteGaugeQuotientSector :
  FiniteGaugeQuotientSector
canonicalFiniteGaugeQuotientSector =
  omegaOrthogonalGaugeQuotientSector

canonicalFiniteHodgeGaugeDefectLaplacian :
  FiniteHodgeGaugeDefectLaplacian
canonicalFiniteHodgeGaugeDefectLaplacian =
  deltaYMDFromGaugeHodgeDefect

canonicalTransferMatrixHamiltonian :
  TransferMatrixHamiltonian
canonicalTransferMatrixHamiltonian =
  logTransferMatrixHamiltonianOnGaugeQuotient

canonicalControlledDominationError :
  ControlledDominationError
canonicalControlledDominationError =
  finiteDepthControlledErrorTerm

canonicalHolonomyCostCarrier :
  HolonomyCostCarrier
canonicalHolonomyCostCarrier =
  finiteDepthHolonomyTopologicalCost

canonicalTopologicalSectorPositiveActionTarget :
  TopologicalSectorPositiveActionTarget
canonicalTopologicalSectorPositiveActionTarget =
  nonVacuumTopologicalSectorsHavePositiveActionTarget
    canonicalHolonomyCostCarrier

canonicalHamiltonianDominationInequalityTarget :
  HamiltonianDominationInequalityTarget
canonicalHamiltonianDominationInequalityTarget =
  hamiltonianDominatesDefectPlusHolonomyTarget
    canonicalFiniteGaugeQuotientSector
    canonicalTransferMatrixHamiltonian
    canonicalFiniteHodgeGaugeDefectLaplacian
    canonicalHolonomyCostCarrier
    canonicalControlledDominationError

canonicalFiniteAGapSourceBoundary :
  FiniteAGapSourceBoundary
canonicalFiniteAGapSourceBoundary =
  finiteAStrongCouplingGapSourceNotAcceptedAsClayAuthority

------------------------------------------------------------------------
-- Governance booleans.  True means "target/source boundary recorded";
-- false means no physical theorem or promotion is constructed here.

finiteHodgeDefectLaplacianTargetRecorded : Bool
finiteHodgeDefectLaplacianTargetRecorded =
  true

transferMatrixHamiltonianTargetRecorded : Bool
transferMatrixHamiltonianTargetRecorded =
  true

gaugeQuotientSectorTargetRecorded : Bool
gaugeQuotientSectorTargetRecorded =
  true

reflectionPositivityOSTargetRecorded : Bool
reflectionPositivityOSTargetRecorded =
  true

dominationInequalityTargetRecorded : Bool
dominationInequalityTargetRecorded =
  true

defectPlusHolonomyTargetRecorded : Bool
defectPlusHolonomyTargetRecorded =
  true

holonomyCostRecorded : Bool
holonomyCostRecorded =
  true

topologicalSectorPositiveActionTargetRecorded : Bool
topologicalSectorPositiveActionTargetRecorded =
  true

finiteKappaSupportRecorded : Bool
finiteKappaSupportRecorded =
  true

finiteAStrongCouplingGapSourceBoundaryRecorded : Bool
finiteAStrongCouplingGapSourceBoundaryRecorded =
  true

finiteGaugeQuotientCarrierConstructed : Bool
finiteGaugeQuotientCarrierConstructed =
  false

transferMatrixIdentifiedWithPhysicalHamiltonian : Bool
transferMatrixIdentifiedWithPhysicalHamiltonian =
  false

reflectionPositivityOSOnGaugeQuotientProved : Bool
reflectionPositivityOSOnGaugeQuotientProved =
  false

finiteHodgeDefectLaplacianConstructed : Bool
finiteHodgeDefectLaplacianConstructed =
  false

hamiltonianDominatesFiniteHodgeDefectProved : Bool
hamiltonianDominatesFiniteHodgeDefectProved =
  false

dominationPlusHolonomyProved : Bool
dominationPlusHolonomyProved =
  false

holonomyCostCarrierConstructed : Bool
holonomyCostCarrierConstructed =
  false

positiveActionForTopologicalSectorsProved : Bool
positiveActionForTopologicalSectorsProved =
  false

controlledErrorAbsorbed : Bool
controlledErrorAbsorbed =
  false

finiteAStrongCouplingGapAcceptedAsClayAuthority : Bool
finiteAStrongCouplingGapAcceptedAsClayAuthority =
  false

selfAdjointSpectralGapLiftProved : Bool
selfAdjointSpectralGapLiftProved =
  false

continuumTransferNoSpectralPollutionProved : Bool
continuumTransferNoSpectralPollutionProved =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

finiteHodgeDefectLaplacianTargetRecordedIsTrue :
  finiteHodgeDefectLaplacianTargetRecorded ≡ true
finiteHodgeDefectLaplacianTargetRecordedIsTrue =
  refl

transferMatrixHamiltonianTargetRecordedIsTrue :
  transferMatrixHamiltonianTargetRecorded ≡ true
transferMatrixHamiltonianTargetRecordedIsTrue =
  refl

gaugeQuotientSectorTargetRecordedIsTrue :
  gaugeQuotientSectorTargetRecorded ≡ true
gaugeQuotientSectorTargetRecordedIsTrue =
  refl

reflectionPositivityOSTargetRecordedIsTrue :
  reflectionPositivityOSTargetRecorded ≡ true
reflectionPositivityOSTargetRecordedIsTrue =
  refl

dominationInequalityTargetRecordedIsTrue :
  dominationInequalityTargetRecorded ≡ true
dominationInequalityTargetRecordedIsTrue =
  refl

defectPlusHolonomyTargetRecordedIsTrue :
  defectPlusHolonomyTargetRecorded ≡ true
defectPlusHolonomyTargetRecordedIsTrue =
  refl

holonomyCostRecordedIsTrue :
  holonomyCostRecorded ≡ true
holonomyCostRecordedIsTrue =
  refl

topologicalSectorPositiveActionTargetRecordedIsTrue :
  topologicalSectorPositiveActionTargetRecorded ≡ true
topologicalSectorPositiveActionTargetRecordedIsTrue =
  refl

finiteKappaSupportRecordedIsTrue :
  finiteKappaSupportRecorded ≡ true
finiteKappaSupportRecordedIsTrue =
  refl

finiteAStrongCouplingGapSourceBoundaryRecordedIsTrue :
  finiteAStrongCouplingGapSourceBoundaryRecorded ≡ true
finiteAStrongCouplingGapSourceBoundaryRecordedIsTrue =
  refl

finiteGaugeQuotientCarrierConstructedIsFalse :
  finiteGaugeQuotientCarrierConstructed ≡ false
finiteGaugeQuotientCarrierConstructedIsFalse =
  refl

transferMatrixIdentifiedWithPhysicalHamiltonianIsFalse :
  transferMatrixIdentifiedWithPhysicalHamiltonian ≡ false
transferMatrixIdentifiedWithPhysicalHamiltonianIsFalse =
  refl

reflectionPositivityOSOnGaugeQuotientProvedIsFalse :
  reflectionPositivityOSOnGaugeQuotientProved ≡ false
reflectionPositivityOSOnGaugeQuotientProvedIsFalse =
  refl

finiteHodgeDefectLaplacianConstructedIsFalse :
  finiteHodgeDefectLaplacianConstructed ≡ false
finiteHodgeDefectLaplacianConstructedIsFalse =
  refl

hamiltonianDominatesFiniteHodgeDefectProvedIsFalse :
  hamiltonianDominatesFiniteHodgeDefectProved ≡ false
hamiltonianDominatesFiniteHodgeDefectProvedIsFalse =
  refl

dominationPlusHolonomyProvedIsFalse :
  dominationPlusHolonomyProved ≡ false
dominationPlusHolonomyProvedIsFalse =
  refl

holonomyCostCarrierConstructedIsFalse :
  holonomyCostCarrierConstructed ≡ false
holonomyCostCarrierConstructedIsFalse =
  refl

positiveActionForTopologicalSectorsProvedIsFalse :
  positiveActionForTopologicalSectorsProved ≡ false
positiveActionForTopologicalSectorsProvedIsFalse =
  refl

controlledErrorAbsorbedIsFalse :
  controlledErrorAbsorbed ≡ false
controlledErrorAbsorbedIsFalse =
  refl

finiteAStrongCouplingGapAcceptedAsClayAuthorityIsFalse :
  finiteAStrongCouplingGapAcceptedAsClayAuthority ≡ false
finiteAStrongCouplingGapAcceptedAsClayAuthorityIsFalse =
  refl

selfAdjointSpectralGapLiftProvedIsFalse :
  selfAdjointSpectralGapLiftProved ≡ false
selfAdjointSpectralGapLiftProvedIsFalse =
  refl

continuumTransferNoSpectralPollutionProvedIsFalse :
  continuumTransferNoSpectralPollutionProved ≡ false
continuumTransferNoSpectralPollutionProvedIsFalse =
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

record YMHamiltonianDominatesFiniteHodgeDefectBoundary : Setω where
  field
    status :
      YMHamiltonianDominationStatus

    consumedSelfAdjointHamiltonianQuotientGapBoundary :
      Gap.YMSelfAdjointHamiltonianQuotientGapBoundary

    consumedSelfAdjointHamiltonianQuotientGapBoundaryCanonical :
      Bool

    consumedSelfAdjointHamiltonianQuotientGapBoundaryCanonicalIsTrue :
      consumedSelfAdjointHamiltonianQuotientGapBoundaryCanonical ≡ true

    consumedWeightedBTAdjointKappaCalculation :
      Weighted.YMWeightedBTAdjointKappaCalculation

    consumedWeightedBTAdjointKappaCalculationCanonical :
      Bool

    consumedWeightedBTAdjointKappaCalculationCanonicalIsTrue :
      consumedWeightedBTAdjointKappaCalculationCanonical ≡ true

    consumedSelfAdjointRequirementNormalizer :
      Normalizer.YMSelfAdjointHamiltonianQuotientRequirementNormalizer

    consumedSelfAdjointRequirementNormalizerCanonical :
      Bool

    consumedSelfAdjointRequirementNormalizerCanonicalIsTrue :
      consumedSelfAdjointRequirementNormalizerCanonical ≡ true

    consumedBTFiniteMetricGaugeKappaBoundary :
      Kappa.BTFiniteMetricGaugeCompatibilityKappaBoundary

    consumedBTFiniteMetricGaugeKappaBoundaryCanonical :
      Bool

    consumedBTFiniteMetricGaugeKappaBoundaryCanonicalIsTrue :
      consumedBTFiniteMetricGaugeKappaBoundaryCanonical ≡ true

    stages :
      List YMHamiltonianDominationStage

    stagesAreCanonical :
      stages ≡ canonicalYMHamiltonianDominationStages

    rows :
      List YMHamiltonianDominationRow

    rowsAreCanonical :
      rows ≡ canonicalYMHamiltonianDominationRows

    blockers :
      List YMHamiltonianDominationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMHamiltonianDominationBlockers

    finiteGaugeQuotientSector :
      FiniteGaugeQuotientSector

    finiteGaugeQuotientSectorIsCanonical :
      finiteGaugeQuotientSector ≡ canonicalFiniteGaugeQuotientSector

    finiteHodgeGaugeDefectLaplacian :
      FiniteHodgeGaugeDefectLaplacian

    finiteHodgeGaugeDefectLaplacianIsCanonical :
      finiteHodgeGaugeDefectLaplacian
      ≡
      canonicalFiniteHodgeGaugeDefectLaplacian

    transferMatrixHamiltonian :
      TransferMatrixHamiltonian

    transferMatrixHamiltonianIsCanonical :
      transferMatrixHamiltonian ≡ canonicalTransferMatrixHamiltonian

    controlledDominationError :
      ControlledDominationError

    controlledDominationErrorIsCanonical :
      controlledDominationError ≡ canonicalControlledDominationError

    holonomyCostCarrier :
      HolonomyCostCarrier

    holonomyCostCarrierIsCanonical :
      holonomyCostCarrier ≡ canonicalHolonomyCostCarrier

    topologicalSectorPositiveActionTarget :
      TopologicalSectorPositiveActionTarget

    topologicalSectorPositiveActionTargetIsCanonical :
      topologicalSectorPositiveActionTarget
      ≡
      canonicalTopologicalSectorPositiveActionTarget

    dominationInequalityTarget :
      HamiltonianDominationInequalityTarget

    dominationInequalityTargetIsCanonical :
      dominationInequalityTarget
      ≡
      canonicalHamiltonianDominationInequalityTarget

    finiteAGapSourceBoundary :
      FiniteAGapSourceBoundary

    finiteAGapSourceBoundaryIsCanonical :
      finiteAGapSourceBoundary ≡ canonicalFiniteAGapSourceBoundary

    upstreamTransferMatrixTargetRecorded :
      Gap.transferMatrixTargetRecorded
      ≡
      true

    upstreamOSStageTargetRecorded :
      Gap.reflectionPositivityOSCompatibilityTargetRecorded
      ≡
      true

    upstreamSelfAdjointDomainStillFalse :
      Gap.selfAdjointHamiltonianDomainConstructedField
        consumedSelfAdjointHamiltonianQuotientGapBoundary
      ≡
      false

    upstreamSpectralGapLiftStillFalse :
      Gap.spectralGapLiftThroughQuotientProvedField
        consumedSelfAdjointHamiltonianQuotientGapBoundary
      ≡
      false

    upstreamWeightedKappaUniformInfimumStillFalse :
      Weighted.uniformInfimumKappaPositiveProvedFlag
        consumedWeightedBTAdjointKappaCalculation
      ≡
      false

    upstreamWeightedSelfAdjointQuotientStillFalse :
      Weighted.selfAdjointHamiltonianQuotientProvedFlag
        consumedWeightedBTAdjointKappaCalculation
      ≡
      false

    upstreamNormalizerRealQuotientStillFalse :
      Normalizer.realYMCarrierQuotientConstructed
        consumedSelfAdjointRequirementNormalizer
      ≡
      false

    upstreamNormalizerSelfAdjointHamiltonianStillFalse :
      Normalizer.selfAdjointYangMillsHamiltonianConstructed
        consumedSelfAdjointRequirementNormalizer
      ≡
      false

    upstreamKappaUniformInfimumStillFalse :
      Kappa.uniformInfimumKappaPositive
        consumedBTFiniteMetricGaugeKappaBoundary
      ≡
      false

    upstreamKappaContinuumTransferStillFalse :
      Kappa.continuumTransferFromKappaFamily
        consumedBTFiniteMetricGaugeKappaBoundary
      ≡
      false

    exactFirstBlocker :
      YMHamiltonianDominationBlocker

    exactFirstBlockerIsHamiltonianDomination :
      exactFirstBlocker
      ≡
      missingHamiltonianDominatesDefectPlusHolonomyInequality

    exactFiniteASourceBlocker :
      YMHamiltonianDominationBlocker

    exactFiniteASourceBlockerIsAcceptedSource :
      exactFiniteASourceBlocker
      ≡
      missingAcceptedFiniteAStrongCouplingGapSource

    stageCount :
      Nat

    stageCountIs10 :
      stageCount ≡ 10

    rowCount :
      Nat

    rowCountIs21 :
      rowCount ≡ 21

    blockerCount :
      Nat

    blockerCountIs14 :
      blockerCount ≡ 14

    finiteHodgeDefectLaplacianTargetRecordedField :
      Bool

    finiteHodgeDefectLaplacianTargetRecordedFieldIsTrue :
      finiteHodgeDefectLaplacianTargetRecordedField ≡ true

    transferMatrixHamiltonianTargetRecordedField :
      Bool

    transferMatrixHamiltonianTargetRecordedFieldIsTrue :
      transferMatrixHamiltonianTargetRecordedField ≡ true

    gaugeQuotientSectorTargetRecordedField :
      Bool

    gaugeQuotientSectorTargetRecordedFieldIsTrue :
      gaugeQuotientSectorTargetRecordedField ≡ true

    reflectionPositivityOSTargetRecordedField :
      Bool

    reflectionPositivityOSTargetRecordedFieldIsTrue :
      reflectionPositivityOSTargetRecordedField ≡ true

    dominationInequalityTargetRecordedField :
      Bool

    dominationInequalityTargetRecordedFieldIsTrue :
      dominationInequalityTargetRecordedField ≡ true

    defectPlusHolonomyTargetRecordedField :
      Bool

    defectPlusHolonomyTargetRecordedFieldIsTrue :
      defectPlusHolonomyTargetRecordedField ≡ true

    holonomyCostRecordedField :
      Bool

    holonomyCostRecordedFieldIsTrue :
      holonomyCostRecordedField ≡ true

    topologicalSectorPositiveActionTargetRecordedField :
      Bool

    topologicalSectorPositiveActionTargetRecordedFieldIsTrue :
      topologicalSectorPositiveActionTargetRecordedField ≡ true

    finiteKappaSupportRecordedField :
      Bool

    finiteKappaSupportRecordedFieldIsTrue :
      finiteKappaSupportRecordedField ≡ true

    finiteAStrongCouplingGapSourceBoundaryRecordedField :
      Bool

    finiteAStrongCouplingGapSourceBoundaryRecordedFieldIsTrue :
      finiteAStrongCouplingGapSourceBoundaryRecordedField ≡ true

    finiteGaugeQuotientCarrierConstructedField :
      Bool

    finiteGaugeQuotientCarrierConstructedFieldIsFalse :
      finiteGaugeQuotientCarrierConstructedField ≡ false

    transferMatrixIdentifiedWithPhysicalHamiltonianField :
      Bool

    transferMatrixIdentifiedWithPhysicalHamiltonianFieldIsFalse :
      transferMatrixIdentifiedWithPhysicalHamiltonianField ≡ false

    reflectionPositivityOSOnGaugeQuotientProvedField :
      Bool

    reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse :
      reflectionPositivityOSOnGaugeQuotientProvedField ≡ false

    finiteHodgeDefectLaplacianConstructedField :
      Bool

    finiteHodgeDefectLaplacianConstructedFieldIsFalse :
      finiteHodgeDefectLaplacianConstructedField ≡ false

    hamiltonianDominatesFiniteHodgeDefectProvedField :
      Bool

    hamiltonianDominatesFiniteHodgeDefectProvedFieldIsFalse :
      hamiltonianDominatesFiniteHodgeDefectProvedField ≡ false

    dominationPlusHolonomyProvedField :
      Bool

    dominationPlusHolonomyProvedFieldIsFalse :
      dominationPlusHolonomyProvedField ≡ false

    holonomyCostCarrierConstructedField :
      Bool

    holonomyCostCarrierConstructedFieldIsFalse :
      holonomyCostCarrierConstructedField ≡ false

    positiveActionForTopologicalSectorsProvedField :
      Bool

    positiveActionForTopologicalSectorsProvedFieldIsFalse :
      positiveActionForTopologicalSectorsProvedField ≡ false

    controlledErrorAbsorbedField :
      Bool

    controlledErrorAbsorbedFieldIsFalse :
      controlledErrorAbsorbedField ≡ false

    finiteAStrongCouplingGapAcceptedAsClayAuthorityField :
      Bool

    finiteAStrongCouplingGapAcceptedAsClayAuthorityFieldIsFalse :
      finiteAStrongCouplingGapAcceptedAsClayAuthorityField ≡ false

    selfAdjointSpectralGapLiftProvedField :
      Bool

    selfAdjointSpectralGapLiftProvedFieldIsFalse :
      selfAdjointSpectralGapLiftProvedField ≡ false

    continuumTransferNoSpectralPollutionProvedField :
      Bool

    continuumTransferNoSpectralPollutionProvedFieldIsFalse :
      continuumTransferNoSpectralPollutionProvedField ≡ false

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

open YMHamiltonianDominatesFiniteHodgeDefectBoundary public

canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary :
  YMHamiltonianDominatesFiniteHodgeDefectBoundary
canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary =
  record
    { status =
        finiteHodgeDefectSupportPresentHamiltonianDominationStillMissing
    ; consumedSelfAdjointHamiltonianQuotientGapBoundary =
        Gap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; consumedSelfAdjointHamiltonianQuotientGapBoundaryCanonical =
        true
    ; consumedSelfAdjointHamiltonianQuotientGapBoundaryCanonicalIsTrue =
        refl
    ; consumedWeightedBTAdjointKappaCalculation =
        Weighted.canonicalYMWeightedBTAdjointKappaCalculation
    ; consumedWeightedBTAdjointKappaCalculationCanonical =
        true
    ; consumedWeightedBTAdjointKappaCalculationCanonicalIsTrue =
        refl
    ; consumedSelfAdjointRequirementNormalizer =
        Normalizer.canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
    ; consumedSelfAdjointRequirementNormalizerCanonical =
        true
    ; consumedSelfAdjointRequirementNormalizerCanonicalIsTrue =
        refl
    ; consumedBTFiniteMetricGaugeKappaBoundary =
        Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
    ; consumedBTFiniteMetricGaugeKappaBoundaryCanonical =
        true
    ; consumedBTFiniteMetricGaugeKappaBoundaryCanonicalIsTrue =
        refl
    ; stages =
        canonicalYMHamiltonianDominationStages
    ; stagesAreCanonical =
        refl
    ; rows =
        canonicalYMHamiltonianDominationRows
    ; rowsAreCanonical =
        refl
    ; blockers =
        canonicalYMHamiltonianDominationBlockers
    ; blockersAreCanonical =
        refl
    ; finiteGaugeQuotientSector =
        canonicalFiniteGaugeQuotientSector
    ; finiteGaugeQuotientSectorIsCanonical =
        refl
    ; finiteHodgeGaugeDefectLaplacian =
        canonicalFiniteHodgeGaugeDefectLaplacian
    ; finiteHodgeGaugeDefectLaplacianIsCanonical =
        refl
    ; transferMatrixHamiltonian =
        canonicalTransferMatrixHamiltonian
    ; transferMatrixHamiltonianIsCanonical =
        refl
    ; controlledDominationError =
        canonicalControlledDominationError
    ; controlledDominationErrorIsCanonical =
        refl
    ; holonomyCostCarrier =
        canonicalHolonomyCostCarrier
    ; holonomyCostCarrierIsCanonical =
        refl
    ; topologicalSectorPositiveActionTarget =
        canonicalTopologicalSectorPositiveActionTarget
    ; topologicalSectorPositiveActionTargetIsCanonical =
        refl
    ; dominationInequalityTarget =
        canonicalHamiltonianDominationInequalityTarget
    ; dominationInequalityTargetIsCanonical =
        refl
    ; finiteAGapSourceBoundary =
        canonicalFiniteAGapSourceBoundary
    ; finiteAGapSourceBoundaryIsCanonical =
        refl
    ; upstreamTransferMatrixTargetRecorded =
        Gap.transferMatrixTargetRecordedIsTrue
    ; upstreamOSStageTargetRecorded =
        Gap.reflectionPositivityOSCompatibilityTargetRecordedIsTrue
    ; upstreamSelfAdjointDomainStillFalse =
        Gap.canonicalYMHamiltonianQuotientGapSelfAdjointDomainFalse
    ; upstreamSpectralGapLiftStillFalse =
        Gap.spectralGapLiftThroughQuotientProvedFieldIsFalse
          Gap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; upstreamWeightedKappaUniformInfimumStillFalse =
        Weighted.canonicalYMWeightedBTAdjointKappaUniformInfimumFalse
    ; upstreamWeightedSelfAdjointQuotientStillFalse =
        Weighted.YMWeightedBTAdjointKappaCalculation.selfAdjointHamiltonianQuotientProvedFlagIsFalse
          Weighted.canonicalYMWeightedBTAdjointKappaCalculation
    ; upstreamNormalizerRealQuotientStillFalse =
        Normalizer.canonicalYMSelfAdjointHamiltonianNormalizerRealQuotientFalse
    ; upstreamNormalizerSelfAdjointHamiltonianStillFalse =
        Normalizer.canonicalYMSelfAdjointHamiltonianNormalizerSelfAdjointHamiltonianFalse
    ; upstreamKappaUniformInfimumStillFalse =
        Kappa.canonicalBTKappaUniformInfimumFalse
    ; upstreamKappaContinuumTransferStillFalse =
        Kappa.canonicalBTKappaContinuumTransferFalse
    ; exactFirstBlocker =
        missingHamiltonianDominatesDefectPlusHolonomyInequality
    ; exactFirstBlockerIsHamiltonianDomination =
        refl
    ; exactFiniteASourceBlocker =
        missingAcceptedFiniteAStrongCouplingGapSource
    ; exactFiniteASourceBlockerIsAcceptedSource =
        refl
    ; stageCount =
        10
    ; stageCountIs10 =
        refl
    ; rowCount =
        21
    ; rowCountIs21 =
        refl
    ; blockerCount =
        14
    ; blockerCountIs14 =
        refl
    ; finiteHodgeDefectLaplacianTargetRecordedField =
        finiteHodgeDefectLaplacianTargetRecorded
    ; finiteHodgeDefectLaplacianTargetRecordedFieldIsTrue =
        refl
    ; transferMatrixHamiltonianTargetRecordedField =
        transferMatrixHamiltonianTargetRecorded
    ; transferMatrixHamiltonianTargetRecordedFieldIsTrue =
        refl
    ; gaugeQuotientSectorTargetRecordedField =
        gaugeQuotientSectorTargetRecorded
    ; gaugeQuotientSectorTargetRecordedFieldIsTrue =
        refl
    ; reflectionPositivityOSTargetRecordedField =
        reflectionPositivityOSTargetRecorded
    ; reflectionPositivityOSTargetRecordedFieldIsTrue =
        refl
    ; dominationInequalityTargetRecordedField =
        dominationInequalityTargetRecorded
    ; dominationInequalityTargetRecordedFieldIsTrue =
        refl
    ; defectPlusHolonomyTargetRecordedField =
        defectPlusHolonomyTargetRecorded
    ; defectPlusHolonomyTargetRecordedFieldIsTrue =
        refl
    ; holonomyCostRecordedField =
        holonomyCostRecorded
    ; holonomyCostRecordedFieldIsTrue =
        refl
    ; topologicalSectorPositiveActionTargetRecordedField =
        topologicalSectorPositiveActionTargetRecorded
    ; topologicalSectorPositiveActionTargetRecordedFieldIsTrue =
        refl
    ; finiteKappaSupportRecordedField =
        finiteKappaSupportRecorded
    ; finiteKappaSupportRecordedFieldIsTrue =
        refl
    ; finiteAStrongCouplingGapSourceBoundaryRecordedField =
        finiteAStrongCouplingGapSourceBoundaryRecorded
    ; finiteAStrongCouplingGapSourceBoundaryRecordedFieldIsTrue =
        refl
    ; finiteGaugeQuotientCarrierConstructedField =
        finiteGaugeQuotientCarrierConstructed
    ; finiteGaugeQuotientCarrierConstructedFieldIsFalse =
        refl
    ; transferMatrixIdentifiedWithPhysicalHamiltonianField =
        transferMatrixIdentifiedWithPhysicalHamiltonian
    ; transferMatrixIdentifiedWithPhysicalHamiltonianFieldIsFalse =
        refl
    ; reflectionPositivityOSOnGaugeQuotientProvedField =
        reflectionPositivityOSOnGaugeQuotientProved
    ; reflectionPositivityOSOnGaugeQuotientProvedFieldIsFalse =
        refl
    ; finiteHodgeDefectLaplacianConstructedField =
        finiteHodgeDefectLaplacianConstructed
    ; finiteHodgeDefectLaplacianConstructedFieldIsFalse =
        refl
    ; hamiltonianDominatesFiniteHodgeDefectProvedField =
        hamiltonianDominatesFiniteHodgeDefectProved
    ; hamiltonianDominatesFiniteHodgeDefectProvedFieldIsFalse =
        refl
    ; dominationPlusHolonomyProvedField =
        dominationPlusHolonomyProved
    ; dominationPlusHolonomyProvedFieldIsFalse =
        refl
    ; holonomyCostCarrierConstructedField =
        holonomyCostCarrierConstructed
    ; holonomyCostCarrierConstructedFieldIsFalse =
        refl
    ; positiveActionForTopologicalSectorsProvedField =
        positiveActionForTopologicalSectorsProved
    ; positiveActionForTopologicalSectorsProvedFieldIsFalse =
        refl
    ; controlledErrorAbsorbedField =
        controlledErrorAbsorbed
    ; controlledErrorAbsorbedFieldIsFalse =
        refl
    ; finiteAStrongCouplingGapAcceptedAsClayAuthorityField =
        finiteAStrongCouplingGapAcceptedAsClayAuthority
    ; finiteAStrongCouplingGapAcceptedAsClayAuthorityFieldIsFalse =
        refl
    ; selfAdjointSpectralGapLiftProvedField =
        selfAdjointSpectralGapLiftProved
    ; selfAdjointSpectralGapLiftProvedFieldIsFalse =
        refl
    ; continuumTransferNoSpectralPollutionProvedField =
        continuumTransferNoSpectralPollutionProved
    ; continuumTransferNoSpectralPollutionProvedFieldIsFalse =
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
        "Consumes the self-adjoint quotient gap boundary, weighted BT adjoint/kappa calculation, requirement normalizer, and BT kappa boundary"
        ∷ "Names the finite gauge-quotient sector Omega-perp, the finite Hodge/gauge defect Laplacian Delta_YM,d, the holonomy/topological cost Hol_d, and the transfer-matrix Hamiltonian H_d"
        ∷ "The next theorem target is H_d on the gauge quotient dominates c * Delta_YM,d plus c' * Hol_d up to a controlled finite-depth error"
        ∷ "Topological-sector positive action and finite kappa support are recorded only as target/source rows"
        ∷ "Transfer matrix and OS/reflection positivity are recorded as target/source stages, but quotient-level OS compatibility is not proved"
        ∷ "The finite-a strong-coupling gap source is recorded only as a boundary; it is not accepted here as Clay authority"
        ∷ "Self-adjoint quotient construction, uniform kappa positivity, spectral lift through the quotient, continuum no-pollution transfer, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMHamiltonianDominationStageCountIs10 :
  listCount canonicalYMHamiltonianDominationStages ≡ 10
canonicalYMHamiltonianDominationStageCountIs10 =
  refl

canonicalYMHamiltonianDominationRowCountIs21 :
  listCount canonicalYMHamiltonianDominationRows ≡ 21
canonicalYMHamiltonianDominationRowCountIs21 =
  refl

canonicalYMHamiltonianDominationBlockerCountIs14 :
  listCount canonicalYMHamiltonianDominationBlockers ≡ 14
canonicalYMHamiltonianDominationBlockerCountIs14 =
  refl

canonicalYMHamiltonianDominationExactFirstBlocker :
  exactFirstBlocker canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  missingHamiltonianDominatesDefectPlusHolonomyInequality
canonicalYMHamiltonianDominationExactFirstBlocker =
  refl

canonicalYMHamiltonianDominationFiniteASourceBlocker :
  exactFiniteASourceBlocker
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  missingAcceptedFiniteAStrongCouplingGapSource
canonicalYMHamiltonianDominationFiniteASourceBlocker =
  refl

canonicalYMHamiltonianDominationTargetRecorded :
  dominationInequalityTargetRecordedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  true
canonicalYMHamiltonianDominationTargetRecorded =
  refl

canonicalYMHamiltonianDominationDefectPlusHolonomyTargetRecorded :
  defectPlusHolonomyTargetRecordedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  true
canonicalYMHamiltonianDominationDefectPlusHolonomyTargetRecorded =
  refl

canonicalYMHamiltonianDominationHolonomyCostRecorded :
  holonomyCostRecordedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  true
canonicalYMHamiltonianDominationHolonomyCostRecorded =
  refl

canonicalYMHamiltonianDominationProvedFalse :
  hamiltonianDominatesFiniteHodgeDefectProvedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  false
canonicalYMHamiltonianDominationProvedFalse =
  refl

canonicalYMHamiltonianDominationPlusHolonomyProvedFalse :
  dominationPlusHolonomyProvedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  false
canonicalYMHamiltonianDominationPlusHolonomyProvedFalse =
  refl

canonicalYMHamiltonianDominationClayFalse :
  clayYangMillsPromotedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  false
canonicalYMHamiltonianDominationClayFalse =
  refl

canonicalYMHamiltonianDominationTerminalFalse :
  terminalPromotionField canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  false
canonicalYMHamiltonianDominationTerminalFalse =
  refl

------------------------------------------------------------------------
-- Fail-closed substantial receipt.

data YMHamiltonianDominationPromotionToken : Set where

yMHamiltonianDominationPromotionTokenImpossibleHere :
  YMHamiltonianDominationPromotionToken →
  ⊥
yMHamiltonianDominationPromotionTokenImpossibleHere ()

canonicalYMHamiltonianDominationFailClosedFindings :
  List String
canonicalYMHamiltonianDominationFailClosedFindings =
  "Typed target only: the finite quotient, transfer-matrix Hamiltonian, Hodge/gauge defect Laplacian, holonomy cost, domination inequality, and controlled error are named but not proved as a physical theorem"
  ∷ "Fail-closed first blocker: the actual domination inequality H_d >= c * Delta_YM,d + c' * Hol_d - E_d is still missing"
  ∷ "Holonomy cost carrier, topological-sector positive action, and finite kappa support are recorded as boundary rows only"
  ∷ "Finite-a source blocker: strong-coupling input is recorded as a source boundary but is not accepted as Clay authority"
  ∷ "Upstream self-adjoint quotient, OS/reflection positivity, uniform kappa infimum, spectral lift, and continuum no-pollution gates remain false"
  ∷ "No spectral-gap, continuum Yang-Mills, Clay Yang-Mills, or terminal promotion token is constructed"
  ∷ []

canonicalYMHamiltonianDominationFailClosedNonPromotions :
  List YMHamiltonianDominationBlocker
canonicalYMHamiltonianDominationFailClosedNonPromotions =
  missingHamiltonianDominatesDefectPlusHolonomyInequality
  ∷ missingHolonomyCostCarrierConstruction
  ∷ missingPositiveActionForTopologicalSectors
  ∷ missingControlledErrorAbsorption
  ∷ missingAcceptedFiniteAStrongCouplingGapSource
  ∷ missingUniformKappaInfimumPositive
  ∷ missingSelfAdjointSpectralGapLift
  ∷ missingContinuumTransferNoSpectralPollution
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record YMHamiltonianDominationFailClosedReceipt : Setω where
  field
    theoremBoundary :
      YMHamiltonianDominatesFiniteHodgeDefectBoundary

    theoremBoundaryIsCanonical :
      Bool

    theoremBoundaryIsCanonicalIsTrue :
      theoremBoundaryIsCanonical ≡ true

    target :
      HamiltonianDominationInequalityTarget

    targetIsCanonical :
      target ≡ canonicalHamiltonianDominationInequalityTarget

    targetRecorded :
      dominationInequalityTargetRecordedField theoremBoundary ≡ true

    failClosedDefectPlusHolonomyTargetRecorded :
      defectPlusHolonomyTargetRecordedField theoremBoundary ≡ true

    holonomyCostTargetRecorded :
      holonomyCostRecordedField theoremBoundary ≡ true

    theoremStillMissing :
      hamiltonianDominatesFiniteHodgeDefectProvedField theoremBoundary
      ≡
      false

    theoremPlusHolonomyStillMissing :
      dominationPlusHolonomyProvedField theoremBoundary
      ≡
      false

    holonomyCostCarrierStillMissing :
      holonomyCostCarrierConstructedField theoremBoundary ≡ false

    positiveTopologicalActionStillMissing :
      positiveActionForTopologicalSectorsProvedField theoremBoundary
      ≡
      false

    quotientStillMissing :
      finiteGaugeQuotientCarrierConstructedField theoremBoundary ≡ false

    transferMatrixPhysicalIdentificationStillMissing :
      transferMatrixIdentifiedWithPhysicalHamiltonianField theoremBoundary
      ≡
      false

    osOnGaugeQuotientStillMissing :
      reflectionPositivityOSOnGaugeQuotientProvedField theoremBoundary
      ≡
      false

    finiteHodgeDefectOperatorStillMissing :
      finiteHodgeDefectLaplacianConstructedField theoremBoundary ≡ false

    controlledErrorAbsorptionStillMissing :
      controlledErrorAbsorbedField theoremBoundary ≡ false

    finiteASourceNotClayAuthority :
      finiteAStrongCouplingGapAcceptedAsClayAuthorityField theoremBoundary
      ≡
      false

    selfAdjointSpectralLiftStillMissing :
      selfAdjointSpectralGapLiftProvedField theoremBoundary ≡ false

    continuumNoPollutionStillMissing :
      continuumTransferNoSpectralPollutionProvedField theoremBoundary
      ≡
      false

    clayPromotionStillFalse :
      clayYangMillsPromotedField theoremBoundary ≡ false

    terminalPromotionStillFalse :
      terminalPromotionField theoremBoundary ≡ false

    blockerLedger :
      List YMHamiltonianDominationBlocker

    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalYMHamiltonianDominationBlockers

    exactFailClosedNonPromotions :
      List YMHamiltonianDominationBlocker

    exactFailClosedNonPromotionsAreCanonical :
      exactFailClosedNonPromotions
      ≡
      canonicalYMHamiltonianDominationFailClosedNonPromotions

    firstFailClosedBlocker :
      YMHamiltonianDominationBlocker

    firstFailClosedBlockerIsDominationInequality :
      firstFailClosedBlocker
      ≡
      missingHamiltonianDominatesDefectPlusHolonomyInequality

    finiteASourceFailClosedBlocker :
      YMHamiltonianDominationBlocker

    finiteASourceFailClosedBlockerIsAuthority :
      finiteASourceFailClosedBlocker
      ≡
      missingAcceptedFiniteAStrongCouplingGapSource

    noPromotionTokenEliminator :
      YMHamiltonianDominationPromotionToken →
      ⊥

    findings :
      List String

    findingsAreCanonical :
      findings
      ≡
      canonicalYMHamiltonianDominationFailClosedFindings

open YMHamiltonianDominationFailClosedReceipt public

canonicalYMHamiltonianDominationFailClosedReceipt :
  YMHamiltonianDominationFailClosedReceipt
canonicalYMHamiltonianDominationFailClosedReceipt =
  record
    { theoremBoundary =
        canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
    ; theoremBoundaryIsCanonical =
        true
    ; theoremBoundaryIsCanonicalIsTrue =
        refl
    ; target =
        canonicalHamiltonianDominationInequalityTarget
    ; targetIsCanonical =
        refl
    ; targetRecorded =
        refl
    ; failClosedDefectPlusHolonomyTargetRecorded =
        refl
    ; holonomyCostTargetRecorded =
        refl
    ; theoremStillMissing =
        refl
    ; theoremPlusHolonomyStillMissing =
        refl
    ; holonomyCostCarrierStillMissing =
        refl
    ; positiveTopologicalActionStillMissing =
        refl
    ; quotientStillMissing =
        refl
    ; transferMatrixPhysicalIdentificationStillMissing =
        refl
    ; osOnGaugeQuotientStillMissing =
        refl
    ; finiteHodgeDefectOperatorStillMissing =
        refl
    ; controlledErrorAbsorptionStillMissing =
        refl
    ; finiteASourceNotClayAuthority =
        refl
    ; selfAdjointSpectralLiftStillMissing =
        refl
    ; continuumNoPollutionStillMissing =
        refl
    ; clayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    ; blockerLedger =
        canonicalYMHamiltonianDominationBlockers
    ; blockerLedgerIsCanonical =
        refl
    ; exactFailClosedNonPromotions =
        canonicalYMHamiltonianDominationFailClosedNonPromotions
    ; exactFailClosedNonPromotionsAreCanonical =
        refl
    ; firstFailClosedBlocker =
        missingHamiltonianDominatesDefectPlusHolonomyInequality
    ; firstFailClosedBlockerIsDominationInequality =
        refl
    ; finiteASourceFailClosedBlocker =
        missingAcceptedFiniteAStrongCouplingGapSource
    ; finiteASourceFailClosedBlockerIsAuthority =
        refl
    ; noPromotionTokenEliminator =
        yMHamiltonianDominationPromotionTokenImpossibleHere
    ; findings =
        canonicalYMHamiltonianDominationFailClosedFindings
    ; findingsAreCanonical =
        refl
    }

canonicalYMHamiltonianDominationFailClosedReceiptKeepsTheoremFalse :
  theoremStillMissing canonicalYMHamiltonianDominationFailClosedReceipt
  ≡
  refl
canonicalYMHamiltonianDominationFailClosedReceiptKeepsTheoremFalse =
  refl

canonicalYMHamiltonianDominationFailClosedReceiptKeepsClayFalse :
  clayPromotionStillFalse canonicalYMHamiltonianDominationFailClosedReceipt
  ≡
  refl
canonicalYMHamiltonianDominationFailClosedReceiptKeepsClayFalse =
  refl

canonicalYMHamiltonianDominationFailClosedReceiptKeepsTerminalFalse :
  terminalPromotionStillFalse canonicalYMHamiltonianDominationFailClosedReceipt
  ≡
  refl
canonicalYMHamiltonianDominationFailClosedReceiptKeepsTerminalFalse =
  refl
