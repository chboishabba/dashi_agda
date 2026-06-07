module DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientGapBoundary where

-- Yang-Mills self-adjoint Hamiltonian quotient gap boundary.
--
-- The finite selected-Hodge/kappa lane now supplies substantial finite-stage
-- structure: sourced finite D * F = J wiring, selected finite pairing, BT
-- finite-building transfer context, and a named depth-indexed kappa target.
-- The remaining analytic gap is not another finite Hodge receipt.  It is the
-- operator-theoretic lift:
--
--   transfer matrix
--   -> gauge-quotient Hilbert carrier
--   -> reflection positivity / OS compatibility
--   -> self-adjoint Hamiltonian with dense domain
--   -> finite spectral gap lift through the quotient
--   -> continuum transfer.
--
-- This module records that exact boundary.  It does not construct the
-- physical Yang-Mills Hamiltonian, does not prove OS compatibility on the
-- quotient, does not transport the finite selected lower bound to continuum
-- Yang-Mills, and keeps spectral-gap, Clay YM, and terminal promotion false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BTFiniteBuildingYMGapTransferBoundary as BTGap
import DASHI.Physics.Closure.BTFiniteMetricGaugeCompatibilityKappaBoundary as Kappa
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientRequirementNormalizer as Normalizer
import DASHI.Physics.Closure.YMSourcedEquationToHamiltonianQuotientBoundary as Sourced

------------------------------------------------------------------------
-- Small local counting utility, matching neighbouring boundary receipts.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Exact route components.

data YMHamiltonianQuotientGapStatus : Set where
  finiteHodgeKappaSupportPresentSelfAdjointQuotientGapStillMissing :
    YMHamiltonianQuotientGapStatus

data YMHamiltonianQuotientGapStage : Set where
  finiteSelectedSourcedEquationStage :
    YMHamiltonianQuotientGapStage

  finiteBTTransferMatrixStage :
    YMHamiltonianQuotientGapStage

  reflectionPositivityOSCompatibilityStage :
    YMHamiltonianQuotientGapStage

  gaugeQuotientHilbertCarrierStage :
    YMHamiltonianQuotientGapStage

  denseSelfAdjointHamiltonianDomainStage :
    YMHamiltonianQuotientGapStage

  spectralGapLiftThroughQuotientStage :
    YMHamiltonianQuotientGapStage

  continuumTransferStage :
    YMHamiltonianQuotientGapStage

canonicalYMHamiltonianQuotientGapStages :
  List YMHamiltonianQuotientGapStage
canonicalYMHamiltonianQuotientGapStages =
  finiteSelectedSourcedEquationStage
  ∷ finiteBTTransferMatrixStage
  ∷ reflectionPositivityOSCompatibilityStage
  ∷ gaugeQuotientHilbertCarrierStage
  ∷ denseSelfAdjointHamiltonianDomainStage
  ∷ spectralGapLiftThroughQuotientStage
  ∷ continuumTransferStage
  ∷ []

data YMHamiltonianQuotientGapRow : Set where
  sourcedEquationHamiltonianBoundaryConsumedRow :
    YMHamiltonianQuotientGapRow

  hamiltonianRequirementNormalizerConsumedRow :
    YMHamiltonianQuotientGapRow

  btFiniteBuildingGapTransferBoundaryConsumedRow :
    YMHamiltonianQuotientGapRow

  finiteMetricGaugeKappaBoundaryConsumedRow :
    YMHamiltonianQuotientGapRow

  finiteSelectedSourcedEquationAvailableRow :
    YMHamiltonianQuotientGapRow

  transferMatrixRecordedButNotPhysicalHamiltonianRow :
    YMHamiltonianQuotientGapRow

  reflectionPositivityOSCompatibilityTargetRow :
    YMHamiltonianQuotientGapRow

  gaugeQuotientHilbertCarrierTargetRow :
    YMHamiltonianQuotientGapRow

  selfAdjointHamiltonianDomainTargetRow :
    YMHamiltonianQuotientGapRow

  finiteSelectedKappaSupportRecordedRow :
    YMHamiltonianQuotientGapRow

  uniformKappaInfimumStillMissingRow :
    YMHamiltonianQuotientGapRow

  spectralGapLiftThroughQuotientTargetRow :
    YMHamiltonianQuotientGapRow

  continuumTransferTargetRow :
    YMHamiltonianQuotientGapRow

  clayAndTerminalHeldFalseRow :
    YMHamiltonianQuotientGapRow

canonicalYMHamiltonianQuotientGapRows :
  List YMHamiltonianQuotientGapRow
canonicalYMHamiltonianQuotientGapRows =
  sourcedEquationHamiltonianBoundaryConsumedRow
  ∷ hamiltonianRequirementNormalizerConsumedRow
  ∷ btFiniteBuildingGapTransferBoundaryConsumedRow
  ∷ finiteMetricGaugeKappaBoundaryConsumedRow
  ∷ finiteSelectedSourcedEquationAvailableRow
  ∷ transferMatrixRecordedButNotPhysicalHamiltonianRow
  ∷ reflectionPositivityOSCompatibilityTargetRow
  ∷ gaugeQuotientHilbertCarrierTargetRow
  ∷ selfAdjointHamiltonianDomainTargetRow
  ∷ finiteSelectedKappaSupportRecordedRow
  ∷ uniformKappaInfimumStillMissingRow
  ∷ spectralGapLiftThroughQuotientTargetRow
  ∷ continuumTransferTargetRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

data YMHamiltonianQuotientGapBlocker : Set where
  missingTransferMatrixToOSCompatibleQuotient :
    YMHamiltonianQuotientGapBlocker

  missingGaugeQuotientHilbertCarrier :
    YMHamiltonianQuotientGapBlocker

  missingReflectionPositivityOnGaugeQuotient :
    YMHamiltonianQuotientGapBlocker

  missingDenseSelfAdjointHamiltonianDomain :
    YMHamiltonianQuotientGapBlocker

  missingUniformKappaInfimumPositive :
    YMHamiltonianQuotientGapBlocker

  missingSpectralGapLiftThroughSelfAdjointQuotient :
    YMHamiltonianQuotientGapBlocker

  missingContinuumTransferFromQuotientGap :
    YMHamiltonianQuotientGapBlocker

  missingClayYangMillsAuthorityToken :
    YMHamiltonianQuotientGapBlocker

canonicalYMHamiltonianQuotientGapBlockers :
  List YMHamiltonianQuotientGapBlocker
canonicalYMHamiltonianQuotientGapBlockers =
  missingTransferMatrixToOSCompatibleQuotient
  ∷ missingGaugeQuotientHilbertCarrier
  ∷ missingReflectionPositivityOnGaugeQuotient
  ∷ missingDenseSelfAdjointHamiltonianDomain
  ∷ missingUniformKappaInfimumPositive
  ∷ missingSpectralGapLiftThroughSelfAdjointQuotient
  ∷ missingContinuumTransferFromQuotientGap
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

data TransferMatrixQuotientTarget : Set where
  finiteTransferMatrixToOSQuotientTarget :
    TransferMatrixQuotientTarget

data GaugeQuotientHilbertCarrierTarget : Set where
  gaugeEquivalenceClassesWithPositiveInnerProductTarget :
    GaugeQuotientHilbertCarrierTarget

data SelfAdjointHamiltonianDomainTarget : Set where
  denseGaugeInvariantDomainAndSelfAdjointClosureTarget :
    SelfAdjointHamiltonianDomainTarget

data SpectralGapLiftTarget : Set where
  finiteSelectedGapLiftedThroughSelfAdjointQuotientTarget :
    SpectralGapLiftTarget

data ContinuumTransferTarget : Set where
  quotientHamiltonianGapSurvivesContinuumLimitTarget :
    ContinuumTransferTarget

canonicalTransferMatrixQuotientTarget :
  TransferMatrixQuotientTarget
canonicalTransferMatrixQuotientTarget =
  finiteTransferMatrixToOSQuotientTarget

canonicalGaugeQuotientHilbertCarrierTarget :
  GaugeQuotientHilbertCarrierTarget
canonicalGaugeQuotientHilbertCarrierTarget =
  gaugeEquivalenceClassesWithPositiveInnerProductTarget

canonicalSelfAdjointHamiltonianDomainTarget :
  SelfAdjointHamiltonianDomainTarget
canonicalSelfAdjointHamiltonianDomainTarget =
  denseGaugeInvariantDomainAndSelfAdjointClosureTarget

canonicalSpectralGapLiftTarget :
  SpectralGapLiftTarget
canonicalSpectralGapLiftTarget =
  finiteSelectedGapLiftedThroughSelfAdjointQuotientTarget

canonicalContinuumTransferTarget :
  ContinuumTransferTarget
canonicalContinuumTransferTarget =
  quotientHamiltonianGapSurvivesContinuumLimitTarget

------------------------------------------------------------------------
-- Canonical booleans.  True means "the target is named/normalized here";
-- false means the analytic theorem is not constructed.

transferMatrixTargetRecorded : Bool
transferMatrixTargetRecorded = true

gaugeQuotientHilbertCarrierTargetRecorded : Bool
gaugeQuotientHilbertCarrierTargetRecorded = true

reflectionPositivityOSCompatibilityTargetRecorded : Bool
reflectionPositivityOSCompatibilityTargetRecorded = true

selfAdjointHamiltonianDomainTargetRecorded : Bool
selfAdjointHamiltonianDomainTargetRecorded = true

spectralGapLiftTargetRecorded : Bool
spectralGapLiftTargetRecorded = true

continuumTransferTargetRecorded : Bool
continuumTransferTargetRecorded = true

transferMatrixPromotedToPhysicalHamiltonian : Bool
transferMatrixPromotedToPhysicalHamiltonian = false

gaugeQuotientHilbertCarrierConstructed : Bool
gaugeQuotientHilbertCarrierConstructed = false

reflectionPositivityOSCompatibilityProved : Bool
reflectionPositivityOSCompatibilityProved = false

selfAdjointHamiltonianDomainConstructed : Bool
selfAdjointHamiltonianDomainConstructed = false

spectralGapLiftThroughQuotientProved : Bool
spectralGapLiftThroughQuotientProved = false

continuumTransferFromQuotientGapProved : Bool
continuumTransferFromQuotientGapProved = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

terminalPromotion : Bool
terminalPromotion = false

transferMatrixTargetRecordedIsTrue :
  transferMatrixTargetRecorded ≡ true
transferMatrixTargetRecordedIsTrue =
  refl

gaugeQuotientHilbertCarrierTargetRecordedIsTrue :
  gaugeQuotientHilbertCarrierTargetRecorded ≡ true
gaugeQuotientHilbertCarrierTargetRecordedIsTrue =
  refl

reflectionPositivityOSCompatibilityTargetRecordedIsTrue :
  reflectionPositivityOSCompatibilityTargetRecorded ≡ true
reflectionPositivityOSCompatibilityTargetRecordedIsTrue =
  refl

selfAdjointHamiltonianDomainTargetRecordedIsTrue :
  selfAdjointHamiltonianDomainTargetRecorded ≡ true
selfAdjointHamiltonianDomainTargetRecordedIsTrue =
  refl

spectralGapLiftTargetRecordedIsTrue :
  spectralGapLiftTargetRecorded ≡ true
spectralGapLiftTargetRecordedIsTrue =
  refl

continuumTransferTargetRecordedIsTrue :
  continuumTransferTargetRecorded ≡ true
continuumTransferTargetRecordedIsTrue =
  refl

transferMatrixPromotedToPhysicalHamiltonianIsFalse :
  transferMatrixPromotedToPhysicalHamiltonian ≡ false
transferMatrixPromotedToPhysicalHamiltonianIsFalse =
  refl

gaugeQuotientHilbertCarrierConstructedIsFalse :
  gaugeQuotientHilbertCarrierConstructed ≡ false
gaugeQuotientHilbertCarrierConstructedIsFalse =
  refl

reflectionPositivityOSCompatibilityProvedIsFalse :
  reflectionPositivityOSCompatibilityProved ≡ false
reflectionPositivityOSCompatibilityProvedIsFalse =
  refl

selfAdjointHamiltonianDomainConstructedIsFalse :
  selfAdjointHamiltonianDomainConstructed ≡ false
selfAdjointHamiltonianDomainConstructedIsFalse =
  refl

spectralGapLiftThroughQuotientProvedIsFalse :
  spectralGapLiftThroughQuotientProved ≡ false
spectralGapLiftThroughQuotientProvedIsFalse =
  refl

continuumTransferFromQuotientGapProvedIsFalse :
  continuumTransferFromQuotientGapProved ≡ false
continuumTransferFromQuotientGapProvedIsFalse =
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

record YMSelfAdjointHamiltonianQuotientGapBoundary : Setω where
  field
    status :
      YMHamiltonianQuotientGapStatus

    sourcedEquationBoundary :
      Sourced.YMSourcedEquationToHamiltonianQuotientBoundary

    sourcedEquationBoundaryIsCanonical :
      sourcedEquationBoundary
      ≡
      Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary

    hamiltonianRequirementNormalizer :
      Normalizer.YMSelfAdjointHamiltonianQuotientRequirementNormalizer

    hamiltonianRequirementNormalizerIsCanonical :
      hamiltonianRequirementNormalizer
      ≡
      Normalizer.canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer

    finiteBuildingGapTransferBoundary :
      BTGap.BTFiniteBuildingYMGapTransferBoundary

    finiteBuildingGapTransferBoundaryIsCanonical :
      finiteBuildingGapTransferBoundary
      ≡
      BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary

    finiteMetricGaugeKappaBoundary :
      Kappa.BTFiniteMetricGaugeCompatibilityKappaBoundary

    finiteMetricGaugeKappaBoundaryIsCanonical :
      finiteMetricGaugeKappaBoundary
      ≡
      Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary

    stages :
      List YMHamiltonianQuotientGapStage

    stagesAreCanonical :
      stages ≡ canonicalYMHamiltonianQuotientGapStages

    rows :
      List YMHamiltonianQuotientGapRow

    rowsAreCanonical :
      rows ≡ canonicalYMHamiltonianQuotientGapRows

    blockers :
      List YMHamiltonianQuotientGapBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMHamiltonianQuotientGapBlockers

    transferMatrixQuotientTarget :
      TransferMatrixQuotientTarget

    transferMatrixQuotientTargetIsCanonical :
      transferMatrixQuotientTarget
      ≡
      canonicalTransferMatrixQuotientTarget

    gaugeQuotientHilbertCarrierTarget :
      GaugeQuotientHilbertCarrierTarget

    gaugeQuotientHilbertCarrierTargetIsCanonical :
      gaugeQuotientHilbertCarrierTarget
      ≡
      canonicalGaugeQuotientHilbertCarrierTarget

    selfAdjointHamiltonianDomainTarget :
      SelfAdjointHamiltonianDomainTarget

    selfAdjointHamiltonianDomainTargetIsCanonical :
      selfAdjointHamiltonianDomainTarget
      ≡
      canonicalSelfAdjointHamiltonianDomainTarget

    spectralGapLiftTarget :
      SpectralGapLiftTarget

    spectralGapLiftTargetIsCanonical :
      spectralGapLiftTarget
      ≡
      canonicalSpectralGapLiftTarget

    continuumTransferTarget :
      ContinuumTransferTarget

    continuumTransferTargetIsCanonical :
      continuumTransferTarget
      ≡
      canonicalContinuumTransferTarget

    selectedFiniteSourcedEquationAvailable :
      Sourced.selectedFiniteSourcedEquationAvailable sourcedEquationBoundary
      ≡
      true

    sourcedEquationHamiltonianTheoremStillFalse :
      Sourced.hamiltonianTheoremPromoted sourcedEquationBoundary
      ≡
      false

    normalizerRealQuotientStillFalse :
      Normalizer.realYMCarrierQuotientConstructed hamiltonianRequirementNormalizer
      ≡
      false

    normalizerSelfAdjointHamiltonianStillFalse :
      Normalizer.selfAdjointYangMillsHamiltonianConstructed
        hamiltonianRequirementNormalizer
      ≡
      false

    normalizerStonePhysicalHamiltonianStillFalse :
      Normalizer.stoneGeneratorIdentifiedWithPhysicalYMHamiltonian
        hamiltonianRequirementNormalizer
      ≡
      false

    finiteBuildingTransferMatrixStageRecorded :
      BTGap.transferMatrixStageRecorded finiteBuildingGapTransferBoundary
      ≡
      true

    finiteBuildingReflectionPositivityStageRecorded :
      BTGap.reflectionPositivityStageRecorded finiteBuildingGapTransferBoundary
      ≡
      true

    finiteBuildingGaugeHilbertCarrierStillFalse :
      BTGap.gaugeInvariantHilbertSpaceConstructed
        finiteBuildingGapTransferBoundary
      ≡
      false

    finiteBuildingUniformGapStillFalse :
      BTGap.uniformFiniteBuildingLowerBoundProved
        finiteBuildingGapTransferBoundary
      ≡
      false

    finiteBuildingContinuumTransferStillFalse :
      BTGap.continuumTransferFromFiniteBTBuildingProved
        finiteBuildingGapTransferBoundary
      ≡
      false

    kappaFiniteMetricGaugeRecorded :
      Kappa.FiniteMetricGaugeCompatibilityRecorded ≡ true

    kappaDepthIndexedFamilyRecorded :
      Kappa.DepthIndexedKappaFamilyTargetRecorded ≡ true

    kappaUniformInfimumStillFalse :
      Kappa.UniformInfimumKappaPositiveProved ≡ false

    exactFirstBlocker :
      YMHamiltonianQuotientGapBlocker

    exactFirstBlockerIsDenseSelfAdjointHamiltonianDomain :
      exactFirstBlocker
      ≡
      missingDenseSelfAdjointHamiltonianDomain

    exactKappaBlocker :
      YMHamiltonianQuotientGapBlocker

    exactKappaBlockerIsUniformKappaInfimum :
      exactKappaBlocker
      ≡
      missingUniformKappaInfimumPositive

    stageCount :
      Nat

    stageCountIs7 :
      stageCount ≡ 7

    rowCount :
      Nat

    rowCountIs14 :
      rowCount ≡ 14

    blockerCount :
      Nat

    blockerCountIs8 :
      blockerCount ≡ 8

    transferMatrixPromotedToPhysicalHamiltonianField :
      Bool

    transferMatrixPromotedToPhysicalHamiltonianFieldIsFalse :
      transferMatrixPromotedToPhysicalHamiltonianField ≡ false

    gaugeQuotientHilbertCarrierConstructedField :
      Bool

    gaugeQuotientHilbertCarrierConstructedFieldIsFalse :
      gaugeQuotientHilbertCarrierConstructedField ≡ false

    reflectionPositivityOSCompatibilityProvedField :
      Bool

    reflectionPositivityOSCompatibilityProvedFieldIsFalse :
      reflectionPositivityOSCompatibilityProvedField ≡ false

    selfAdjointHamiltonianDomainConstructedField :
      Bool

    selfAdjointHamiltonianDomainConstructedFieldIsFalse :
      selfAdjointHamiltonianDomainConstructedField ≡ false

    spectralGapLiftThroughQuotientProvedField :
      Bool

    spectralGapLiftThroughQuotientProvedFieldIsFalse :
      spectralGapLiftThroughQuotientProvedField ≡ false

    continuumTransferFromQuotientGapProvedField :
      Bool

    continuumTransferFromQuotientGapProvedFieldIsFalse :
      continuumTransferFromQuotientGapProvedField ≡ false

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

open YMSelfAdjointHamiltonianQuotientGapBoundary public

canonicalYMSelfAdjointHamiltonianQuotientGapBoundary :
  YMSelfAdjointHamiltonianQuotientGapBoundary
canonicalYMSelfAdjointHamiltonianQuotientGapBoundary =
  record
    { status =
        finiteHodgeKappaSupportPresentSelfAdjointQuotientGapStillMissing
    ; sourcedEquationBoundary =
        Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary
    ; sourcedEquationBoundaryIsCanonical =
        refl
    ; hamiltonianRequirementNormalizer =
        Normalizer.canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
    ; hamiltonianRequirementNormalizerIsCanonical =
        refl
    ; finiteBuildingGapTransferBoundary =
        BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
    ; finiteBuildingGapTransferBoundaryIsCanonical =
        refl
    ; finiteMetricGaugeKappaBoundary =
        Kappa.canonicalBTFiniteMetricGaugeCompatibilityKappaBoundary
    ; finiteMetricGaugeKappaBoundaryIsCanonical =
        refl
    ; stages =
        canonicalYMHamiltonianQuotientGapStages
    ; stagesAreCanonical =
        refl
    ; rows =
        canonicalYMHamiltonianQuotientGapRows
    ; rowsAreCanonical =
        refl
    ; blockers =
        canonicalYMHamiltonianQuotientGapBlockers
    ; blockersAreCanonical =
        refl
    ; transferMatrixQuotientTarget =
        canonicalTransferMatrixQuotientTarget
    ; transferMatrixQuotientTargetIsCanonical =
        refl
    ; gaugeQuotientHilbertCarrierTarget =
        canonicalGaugeQuotientHilbertCarrierTarget
    ; gaugeQuotientHilbertCarrierTargetIsCanonical =
        refl
    ; selfAdjointHamiltonianDomainTarget =
        canonicalSelfAdjointHamiltonianDomainTarget
    ; selfAdjointHamiltonianDomainTargetIsCanonical =
        refl
    ; spectralGapLiftTarget =
        canonicalSpectralGapLiftTarget
    ; spectralGapLiftTargetIsCanonical =
        refl
    ; continuumTransferTarget =
        canonicalContinuumTransferTarget
    ; continuumTransferTargetIsCanonical =
        refl
    ; selectedFiniteSourcedEquationAvailable =
        Sourced.canonicalYMSourcedEquationToHamiltonianFiniteSourceAvailable
    ; sourcedEquationHamiltonianTheoremStillFalse =
        Sourced.canonicalYMSourcedEquationToHamiltonianHamiltonianTheoremFalse
    ; normalizerRealQuotientStillFalse =
        Normalizer.canonicalYMSelfAdjointHamiltonianNormalizerRealQuotientFalse
    ; normalizerSelfAdjointHamiltonianStillFalse =
        Normalizer.canonicalYMSelfAdjointHamiltonianNormalizerSelfAdjointHamiltonianFalse
    ; normalizerStonePhysicalHamiltonianStillFalse =
        Normalizer.YMSelfAdjointHamiltonianQuotientRequirementNormalizer.stoneGeneratorIdentifiedWithPhysicalYMHamiltonianIsFalse
          Normalizer.canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
    ; finiteBuildingTransferMatrixStageRecorded =
        BTGap.BTFiniteBuildingYMGapTransferBoundary.transferMatrixStageRecordedIsTrue
          BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
    ; finiteBuildingReflectionPositivityStageRecorded =
        BTGap.BTFiniteBuildingYMGapTransferBoundary.reflectionPositivityStageRecordedIsTrue
          BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
    ; finiteBuildingGaugeHilbertCarrierStillFalse =
        BTGap.BTFiniteBuildingYMGapTransferBoundary.gaugeInvariantHilbertSpaceConstructedIsFalse
          BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
    ; finiteBuildingUniformGapStillFalse =
        BTGap.BTFiniteBuildingYMGapTransferBoundary.uniformFiniteBuildingLowerBoundProvedIsFalse
          BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
    ; finiteBuildingContinuumTransferStillFalse =
        BTGap.BTFiniteBuildingYMGapTransferBoundary.continuumTransferFromFiniteBTBuildingProvedIsFalse
          BTGap.canonicalBTFiniteBuildingYMGapTransferBoundary
    ; kappaFiniteMetricGaugeRecorded =
        Kappa.finiteMetricGaugeCompatibilityRecordedIsTrue
    ; kappaDepthIndexedFamilyRecorded =
        Kappa.depthIndexedKappaFamilyTargetRecordedIsTrue
    ; kappaUniformInfimumStillFalse =
        Kappa.uniformInfimumKappaPositiveProvedIsFalse
    ; exactFirstBlocker =
        missingDenseSelfAdjointHamiltonianDomain
    ; exactFirstBlockerIsDenseSelfAdjointHamiltonianDomain =
        refl
    ; exactKappaBlocker =
        missingUniformKappaInfimumPositive
    ; exactKappaBlockerIsUniformKappaInfimum =
        refl
    ; stageCount =
        7
    ; stageCountIs7 =
        refl
    ; rowCount =
        14
    ; rowCountIs14 =
        refl
    ; blockerCount =
        8
    ; blockerCountIs8 =
        refl
    ; transferMatrixPromotedToPhysicalHamiltonianField =
        false
    ; transferMatrixPromotedToPhysicalHamiltonianFieldIsFalse =
        refl
    ; gaugeQuotientHilbertCarrierConstructedField =
        false
    ; gaugeQuotientHilbertCarrierConstructedFieldIsFalse =
        refl
    ; reflectionPositivityOSCompatibilityProvedField =
        false
    ; reflectionPositivityOSCompatibilityProvedFieldIsFalse =
        refl
    ; selfAdjointHamiltonianDomainConstructedField =
        false
    ; selfAdjointHamiltonianDomainConstructedFieldIsFalse =
        refl
    ; spectralGapLiftThroughQuotientProvedField =
        false
    ; spectralGapLiftThroughQuotientProvedFieldIsFalse =
        refl
    ; continuumTransferFromQuotientGapProvedField =
        false
    ; continuumTransferFromQuotientGapProvedFieldIsFalse =
        refl
    ; clayYangMillsPromotedField =
        false
    ; clayYangMillsPromotedFieldIsFalse =
        refl
    ; terminalPromotionField =
        false
    ; terminalPromotionFieldIsFalse =
        refl
    ; boundary =
        "Finite selected sourced-equation and finite selected Hodge/kappa support are consumed as upstream evidence"
        ∷ "The finite BT transfer-matrix and reflection-positivity stages are recorded, but the transfer matrix is not identified with the physical Yang-Mills Hamiltonian"
        ∷ "The gauge-quotient Hilbert carrier remains a target: gauge equivalence classes, positive inner product, completion, and quotient domain are not constructed here"
        ∷ "OS compatibility must be proved after quotienting, not only on a finite unquotiented transfer-matrix receipt"
        ∷ "The first local analytic blocker here is missingDenseSelfAdjointHamiltonianDomain"
        ∷ "The finite selected kappa route is recorded, but the uniform positive infimum remains false upstream"
        ∷ "A spectral gap lift requires the self-adjoint quotient Hamiltonian plus the uniform kappa/finite-building lower bound"
        ∷ "Continuum transfer, Clay Yang-Mills, and terminal promotion remain false"
        ∷ []
    }

canonicalYMHamiltonianQuotientGapStageCountIs7 :
  listCount canonicalYMHamiltonianQuotientGapStages ≡ 7
canonicalYMHamiltonianQuotientGapStageCountIs7 =
  refl

canonicalYMHamiltonianQuotientGapRowCountIs14 :
  listCount canonicalYMHamiltonianQuotientGapRows ≡ 14
canonicalYMHamiltonianQuotientGapRowCountIs14 =
  refl

canonicalYMHamiltonianQuotientGapBlockerCountIs8 :
  listCount canonicalYMHamiltonianQuotientGapBlockers ≡ 8
canonicalYMHamiltonianQuotientGapBlockerCountIs8 =
  refl

canonicalYMHamiltonianQuotientGapFirstBlocker :
  exactFirstBlocker canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
  ≡
  missingDenseSelfAdjointHamiltonianDomain
canonicalYMHamiltonianQuotientGapFirstBlocker =
  refl

canonicalYMHamiltonianQuotientGapKappaBlocker :
  exactKappaBlocker canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
  ≡
  missingUniformKappaInfimumPositive
canonicalYMHamiltonianQuotientGapKappaBlocker =
  refl

canonicalYMHamiltonianQuotientGapFiniteSourceAvailable :
  Sourced.selectedFiniteSourcedEquationAvailable
    (sourcedEquationBoundary
      canonicalYMSelfAdjointHamiltonianQuotientGapBoundary)
  ≡
  true
canonicalYMHamiltonianQuotientGapFiniteSourceAvailable =
  refl

canonicalYMHamiltonianQuotientGapSelfAdjointDomainFalse :
  selfAdjointHamiltonianDomainConstructedField
    canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
  ≡
  false
canonicalYMHamiltonianQuotientGapSelfAdjointDomainFalse =
  refl

canonicalYMHamiltonianQuotientGapClayFalse :
  clayYangMillsPromotedField
    canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
  ≡
  false
canonicalYMHamiltonianQuotientGapClayFalse =
  refl

canonicalYMHamiltonianQuotientGapTerminalFalse :
  terminalPromotionField
    canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
  ≡
  false
canonicalYMHamiltonianQuotientGapTerminalFalse =
  refl
