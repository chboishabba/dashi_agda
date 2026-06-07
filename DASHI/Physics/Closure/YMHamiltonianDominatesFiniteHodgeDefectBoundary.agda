module DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary where

-- Yang-Mills Hamiltonian domination boundary.
--
-- The finite BT/Hodge lane now has selected finite Hodge algebra, selected
-- variation pairing, finite metric/gauge kappa targets, and finite kappa
-- sample arithmetic.  The next physical theorem is stronger than another
-- local kappa receipt:
--
--   on the finite gauge quotient, the transfer-matrix Hamiltonian dominates
--   the finite Hodge/gauge defect Laplacian up to controlled errors.
--
-- Symbolically this target is:
--
--   H_d | Omega^\perp  >=  c * Delta_YM,d - E_d.
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

  finiteAStrongCouplingGapSourceStage :
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
  ∷ finiteAStrongCouplingGapSourceStage
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

  controlledErrorTermTargetRow :
    YMHamiltonianDominationRow

  finiteAStrongCouplingGapSourceBoundaryRow :
    YMHamiltonianDominationRow

  uniformKappaSourceStillOpenRow :
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
  ∷ controlledErrorTermTargetRow
  ∷ finiteAStrongCouplingGapSourceBoundaryRow
  ∷ uniformKappaSourceStillOpenRow
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

data HamiltonianDominationInequalityTarget : Set where
  hamiltonianDominatesFiniteHodgeDefectTarget :
    FiniteGaugeQuotientSector →
    TransferMatrixHamiltonian →
    FiniteHodgeGaugeDefectLaplacian →
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

canonicalHamiltonianDominationInequalityTarget :
  HamiltonianDominationInequalityTarget
canonicalHamiltonianDominationInequalityTarget =
  hamiltonianDominatesFiniteHodgeDefectTarget
    canonicalFiniteGaugeQuotientSector
    canonicalTransferMatrixHamiltonian
    canonicalFiniteHodgeGaugeDefectLaplacian
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
      missingHamiltonianDominatesFiniteHodgeDefectInequality

    exactFiniteASourceBlocker :
      YMHamiltonianDominationBlocker

    exactFiniteASourceBlockerIsAcceptedSource :
      exactFiniteASourceBlocker
      ≡
      missingAcceptedFiniteAStrongCouplingGapSource

    stageCount :
      Nat

    stageCountIs7 :
      stageCount ≡ 7

    rowCount :
      Nat

    rowCountIs15 :
      rowCount ≡ 15

    blockerCount :
      Nat

    blockerCountIs11 :
      blockerCount ≡ 11

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
        missingHamiltonianDominatesFiniteHodgeDefectInequality
    ; exactFirstBlockerIsHamiltonianDomination =
        refl
    ; exactFiniteASourceBlocker =
        missingAcceptedFiniteAStrongCouplingGapSource
    ; exactFiniteASourceBlockerIsAcceptedSource =
        refl
    ; stageCount =
        7
    ; stageCountIs7 =
        refl
    ; rowCount =
        15
    ; rowCountIs15 =
        refl
    ; blockerCount =
        11
    ; blockerCountIs11 =
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
        ∷ "Names the finite gauge-quotient sector Omega-perp, the finite Hodge/gauge defect Laplacian Delta_YM,d, and the transfer-matrix Hamiltonian H_d"
        ∷ "The next theorem target is H_d on the gauge quotient dominates c * Delta_YM,d up to a controlled finite-depth error"
        ∷ "Transfer matrix and OS/reflection positivity are recorded as target/source stages, but quotient-level OS compatibility is not proved"
        ∷ "The finite-a strong-coupling gap source is recorded only as a boundary; it is not accepted here as Clay authority"
        ∷ "Uniform kappa positivity, spectral lift through the self-adjoint quotient, continuum no-pollution transfer, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMHamiltonianDominationStageCountIs7 :
  listCount canonicalYMHamiltonianDominationStages ≡ 7
canonicalYMHamiltonianDominationStageCountIs7 =
  refl

canonicalYMHamiltonianDominationRowCountIs15 :
  listCount canonicalYMHamiltonianDominationRows ≡ 15
canonicalYMHamiltonianDominationRowCountIs15 =
  refl

canonicalYMHamiltonianDominationBlockerCountIs11 :
  listCount canonicalYMHamiltonianDominationBlockers ≡ 11
canonicalYMHamiltonianDominationBlockerCountIs11 =
  refl

canonicalYMHamiltonianDominationExactFirstBlocker :
  exactFirstBlocker canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  missingHamiltonianDominatesFiniteHodgeDefectInequality
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

canonicalYMHamiltonianDominationProvedFalse :
  hamiltonianDominatesFiniteHodgeDefectProvedField
    canonicalYMHamiltonianDominatesFiniteHodgeDefectBoundary
  ≡
  false
canonicalYMHamiltonianDominationProvedFalse =
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
