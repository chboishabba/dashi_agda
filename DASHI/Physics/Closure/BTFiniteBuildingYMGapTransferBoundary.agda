module DASHI.Physics.Closure.BTFiniteBuildingYMGapTransferBoundary where

-- Finite-building Yang-Mills gap-transfer boundary.
--
-- This module packages the Bruhat-Tits finite-building route as a checked
-- boundary only:
--
--   finite-depth BT-building gauge model
--   -> transfer matrix
--   -> reflection positivity
--   -> gauge-invariant Hilbert space target
--   -> finite gap m_d
--   -> uniform lower bound inf_d m_d > 0
--   -> continuum transfer
--
-- Existing receipts provide finite/product-tree, reflection-positive, finite
-- transfer-matrix, selected-carrier lower-bound, and Hamiltonian-normalizer
-- surfaces.  This file does not prove a uniform finite-building lower bound,
-- does not construct the real self-adjoint Yang-Mills Hamiltonian on the
-- quotient carrier, and does not promote the spectral-gap, continuum, Clay
-- Yang-Mills, or terminal claims.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.BruhatTitsProductTreeReceipt as BTProduct
import DASHI.Physics.Closure.LatticeMassGapFromTransferMatrixReceipt as LatticeGap
import DASHI.Physics.Closure.PressureBelow15SpectralTheoremObstruction as S8
import DASHI.Physics.Closure.SelfAdjointYangMillsHamiltonianOnCarrierQuotient as Hamiltonian
import DASHI.Physics.Closure.YMBruhatTitsPathCountingKPThresholdReceipt as BTPath
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientRequirementNormalizer as Normalizer
import DASHI.Physics.Closure.YMSourcedEquationToHamiltonianQuotientBoundary as Sourced
import DASHI.Physics.Closure.YMSprint87TransferReflectionPositivityAuthorityReceipt as RPTransfer
import DASHI.Physics.Closure.YMSprint129SpectralGapTransportClosure as Sprint129

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

data BTFiniteBuildingYMGapTransferStatus : Set where
  finiteBuildingGapTransferBoundaryUniformDepthLowerBoundMissing :
    BTFiniteBuildingYMGapTransferStatus

data BTFiniteBuildingYMGapTransferRow : Set where
  finiteDepthBTProductBuildingConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  bruhatTitsPathCountingThresholdConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  transferReflectionPositivityAuthorityConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  finiteTransferMatrixGapConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  sourcedEquationHamiltonianBoundaryConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  hamiltonianRequirementNormalizerConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  selectedCarrierLowerBoundConsumedRow :
    BTFiniteBuildingYMGapTransferRow

  sprint129TransportContextReferencedRow :
    BTFiniteBuildingYMGapTransferRow

  gaugeInvariantHilbertSpaceTargetNamedRow :
    BTFiniteBuildingYMGapTransferRow

  finiteDepthGapMDTargetNamedRow :
    BTFiniteBuildingYMGapTransferRow

  uniformInfimumLowerBoundMissingRow :
    BTFiniteBuildingYMGapTransferRow

  continuumTransferHeldFalseRow :
    BTFiniteBuildingYMGapTransferRow

  clayAndTerminalHeldFalseRow :
    BTFiniteBuildingYMGapTransferRow

canonicalBTFiniteBuildingYMGapTransferRows :
  List BTFiniteBuildingYMGapTransferRow
canonicalBTFiniteBuildingYMGapTransferRows =
  finiteDepthBTProductBuildingConsumedRow
  ∷ bruhatTitsPathCountingThresholdConsumedRow
  ∷ transferReflectionPositivityAuthorityConsumedRow
  ∷ finiteTransferMatrixGapConsumedRow
  ∷ sourcedEquationHamiltonianBoundaryConsumedRow
  ∷ hamiltonianRequirementNormalizerConsumedRow
  ∷ selectedCarrierLowerBoundConsumedRow
  ∷ sprint129TransportContextReferencedRow
  ∷ gaugeInvariantHilbertSpaceTargetNamedRow
  ∷ finiteDepthGapMDTargetNamedRow
  ∷ uniformInfimumLowerBoundMissingRow
  ∷ continuumTransferHeldFalseRow
  ∷ clayAndTerminalHeldFalseRow
  ∷ []

data BTFiniteBuildingYMGapTransferStage : Set where
  finiteDepthBTBuildingGaugeModelStage :
    BTFiniteBuildingYMGapTransferStage

  transferMatrixStage :
    BTFiniteBuildingYMGapTransferStage

  reflectionPositivityStage :
    BTFiniteBuildingYMGapTransferStage

  gaugeInvariantHilbertSpaceStage :
    BTFiniteBuildingYMGapTransferStage

  finiteDepthSpectralGapMDStage :
    BTFiniteBuildingYMGapTransferStage

  uniformDepthLowerBoundStage :
    BTFiniteBuildingYMGapTransferStage

  continuumTransferStage :
    BTFiniteBuildingYMGapTransferStage

canonicalBTFiniteBuildingYMGapTransferStages :
  List BTFiniteBuildingYMGapTransferStage
canonicalBTFiniteBuildingYMGapTransferStages =
  finiteDepthBTBuildingGaugeModelStage
  ∷ transferMatrixStage
  ∷ reflectionPositivityStage
  ∷ gaugeInvariantHilbertSpaceStage
  ∷ finiteDepthSpectralGapMDStage
  ∷ uniformDepthLowerBoundStage
  ∷ continuumTransferStage
  ∷ []

data BTFiniteBuildingYMGapTransferHardBlocker : Set where
  missingGaugeInvariantHilbertSpaceOnFiniteBTBuilding :
    BTFiniteBuildingYMGapTransferHardBlocker

  missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient :
    BTFiniteBuildingYMGapTransferHardBlocker

  missingUniformFiniteBuildingMassGapLowerBound :
    BTFiniteBuildingYMGapTransferHardBlocker

  missingContinuumTransferFromFiniteBTBuilding :
    BTFiniteBuildingYMGapTransferHardBlocker

  missingClayYangMillsAuthorityToken :
    BTFiniteBuildingYMGapTransferHardBlocker

canonicalBTFiniteBuildingYMGapTransferHardBlockers :
  List BTFiniteBuildingYMGapTransferHardBlocker
canonicalBTFiniteBuildingYMGapTransferHardBlockers =
  missingGaugeInvariantHilbertSpaceOnFiniteBTBuilding
  ∷ missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
  ∷ missingUniformFiniteBuildingMassGapLowerBound
  ∷ missingContinuumTransferFromFiniteBTBuilding
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

record BTFiniteBuildingYMGapTransferBoundary : Setω where
  field
    status :
      BTFiniteBuildingYMGapTransferStatus

    bruhatTitsProductTree :
      BTProduct.BruhatTitsProductTreeReceipt

    bruhatTitsProductTreeCanonical :
      Bool

    bruhatTitsProductTreeCanonicalIsTrue :
      bruhatTitsProductTreeCanonical ≡ true

    productTreeWilsonActionInhabitable :
      BTProduct.BruhatTitsProductTreeReceipt.wilsonActionOnProductTreeInhabitable
        bruhatTitsProductTree
      ≡
      true

    productTreeReflectionPositivityInhabitable :
      BTProduct.BruhatTitsProductTreeReceipt.reflectionPositivityInhabitable
        bruhatTitsProductTree
      ≡
      true

    bruhatTitsPathCounting :
      BTPath.YMBruhatTitsPathCountingKPThresholdReceipt

    bruhatTitsPathCountingCanonical :
      Bool

    bruhatTitsPathCountingCanonicalIsTrue :
      bruhatTitsPathCountingCanonical ≡ true

    transferReflectionPositivityAuthority :
      RPTransfer.YMSprint87TransferReflectionPositivityAuthorityReceipt

    transferReflectionPositivityAuthorityCanonical :
      Bool

    transferReflectionPositivityAuthorityCanonicalIsTrue :
      transferReflectionPositivityAuthorityCanonical ≡ true

    latticeMassGapFromTransferMatrix :
      LatticeGap.LatticeMassGapFromTransferMatrixReceipt

    finiteTransferMatrixDefined :
      LatticeGap.LatticeMassGapFromTransferMatrixReceipt.transferMatrixDefined
        latticeMassGapFromTransferMatrix
      ≡
      true

    finiteTransferMatrixGapPositive :
      LatticeGap.LatticeMassGapFromTransferMatrixReceipt.finiteLatticeGapPositive
        latticeMassGapFromTransferMatrix
      ≡
      true

    latticeUniformContinuumGapStillFalse :
      LatticeGap.LatticeMassGapFromTransferMatrixReceipt.uniformContinuumGapProved
        latticeMassGapFromTransferMatrix
      ≡
      false

    sourcedEquationHamiltonianBoundary :
      Sourced.YMSourcedEquationToHamiltonianQuotientBoundary

    sourcedEquationHamiltonianBoundaryCanonical :
      Bool

    sourcedEquationHamiltonianBoundaryCanonicalIsTrue :
      sourcedEquationHamiltonianBoundaryCanonical ≡ true

    hamiltonianRequirementNormalizer :
      Normalizer.YMSelfAdjointHamiltonianQuotientRequirementNormalizer

    hamiltonianRequirementNormalizerCanonical :
      Bool

    hamiltonianRequirementNormalizerCanonicalIsTrue :
      hamiltonianRequirementNormalizerCanonical ≡ true

    selectedCarrierLowerBound :
      Hamiltonian.SelectedCarrierSpectralLowerBoundReceipt

    selectedCarrierLowerBoundCanonical :
      Bool

    selectedCarrierLowerBoundCanonicalIsTrue :
      selectedCarrierLowerBoundCanonical ≡ true

    selectedFiniteCarrierLowerBoundAvailable :
      Hamiltonian.SelectedCarrierSpectralLowerBoundReceipt.finiteCarrierLowerBoundAvailable
        selectedCarrierLowerBound
      ≡
      true

    selectedCarrierLowerBoundNotTransportedToRealYM :
      Hamiltonian.SelectedCarrierSpectralLowerBoundReceipt.lowerBoundTransportedToRealYM
        selectedCarrierLowerBound
      ≡
      false

    sprint129TransportContext :
      Sprint129.YMSprint129SpectralGapTransportClosureReceipt

    sprint129TransportContextCanonical :
      Bool

    sprint129TransportContextCanonicalIsTrue :
      sprint129TransportContextCanonical ≡ true

    finiteDepthBTBuildingGaugeModelRecorded :
      Bool

    finiteDepthBTBuildingGaugeModelRecordedIsTrue :
      finiteDepthBTBuildingGaugeModelRecorded ≡ true

    transferMatrixStageRecorded :
      Bool

    transferMatrixStageRecordedIsTrue :
      transferMatrixStageRecorded ≡ true

    reflectionPositivityStageRecorded :
      Bool

    reflectionPositivityStageRecordedIsTrue :
      reflectionPositivityStageRecorded ≡ true

    gaugeInvariantHilbertSpaceConstructed :
      Bool

    gaugeInvariantHilbertSpaceConstructedIsFalse :
      gaugeInvariantHilbertSpaceConstructed ≡ false

    finiteDepthSpectralGapMDRecorded :
      Bool

    finiteDepthSpectralGapMDRecordedIsTrue :
      finiteDepthSpectralGapMDRecorded ≡ true

    uniformFiniteBuildingLowerBoundProved :
      Bool

    uniformFiniteBuildingLowerBoundProvedIsFalse :
      uniformFiniteBuildingLowerBoundProved ≡ false

    continuumTransferFromFiniteBTBuildingProved :
      Bool

    continuumTransferFromFiniteBTBuildingProvedIsFalse :
      continuumTransferFromFiniteBTBuildingProved ≡ false

    upstreamRealCarrierBlocker :
      S8.S8GlobalYangMillsHamiltonianCarrierMissingTheorem

    upstreamRealCarrierBlockerIsSelfAdjointYangMillsHamiltonian :
      upstreamRealCarrierBlocker
      ≡
      S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient

    exactHardBlocker :
      BTFiniteBuildingYMGapTransferHardBlocker

    exactHardBlockerIsUniformFiniteBuildingMassGapLowerBound :
      exactHardBlocker
      ≡
      missingUniformFiniteBuildingMassGapLowerBound

    hardBlockers :
      List BTFiniteBuildingYMGapTransferHardBlocker

    hardBlockersAreCanonical :
      hardBlockers ≡ canonicalBTFiniteBuildingYMGapTransferHardBlockers

    stages :
      List BTFiniteBuildingYMGapTransferStage

    stagesAreCanonical :
      stages ≡ canonicalBTFiniteBuildingYMGapTransferStages

    stageCount :
      Nat

    stageCountIs7 :
      stageCount ≡ 7

    rows :
      List BTFiniteBuildingYMGapTransferRow

    rowsAreCanonical :
      rows ≡ canonicalBTFiniteBuildingYMGapTransferRows

    rowCount :
      Nat

    rowCountIs13 :
      rowCount ≡ 13

    spectralGapPromoted :
      Bool

    spectralGapPromotedIsFalse :
      spectralGapPromoted ≡ false

    continuumTransferPromoted :
      Bool

    continuumTransferPromotedIsFalse :
      continuumTransferPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    boundary :
      List String

open BTFiniteBuildingYMGapTransferBoundary public

canonicalBTFiniteBuildingYMGapTransferBoundary :
  BTFiniteBuildingYMGapTransferBoundary
canonicalBTFiniteBuildingYMGapTransferBoundary =
  record
    { status =
        finiteBuildingGapTransferBoundaryUniformDepthLowerBoundMissing
    ; bruhatTitsProductTree =
        BTProduct.canonicalBruhatTitsProductTreeReceipt
    ; bruhatTitsProductTreeCanonical =
        true
    ; bruhatTitsProductTreeCanonicalIsTrue =
        refl
    ; productTreeWilsonActionInhabitable =
        BTProduct.BruhatTitsProductTreeReceipt.wilsonActionOnProductTreeInhabitableIsTrue
          BTProduct.canonicalBruhatTitsProductTreeReceipt
    ; productTreeReflectionPositivityInhabitable =
        BTProduct.BruhatTitsProductTreeReceipt.reflectionPositivityInhabitableIsTrue
          BTProduct.canonicalBruhatTitsProductTreeReceipt
    ; bruhatTitsPathCounting =
        BTPath.canonicalYMBruhatTitsPathCountingKPThresholdReceipt
    ; bruhatTitsPathCountingCanonical =
        true
    ; bruhatTitsPathCountingCanonicalIsTrue =
        refl
    ; transferReflectionPositivityAuthority =
        RPTransfer.canonicalYMSprint87TransferReflectionPositivityAuthorityReceipt
    ; transferReflectionPositivityAuthorityCanonical =
        true
    ; transferReflectionPositivityAuthorityCanonicalIsTrue =
        refl
    ; latticeMassGapFromTransferMatrix =
        LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; finiteTransferMatrixDefined =
        LatticeGap.LatticeMassGapFromTransferMatrixReceipt.transferMatrixDefinedIsTrue
          LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; finiteTransferMatrixGapPositive =
        LatticeGap.LatticeMassGapFromTransferMatrixReceipt.finiteLatticeGapPositiveIsTrue
          LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; latticeUniformContinuumGapStillFalse =
        LatticeGap.LatticeMassGapFromTransferMatrixReceipt.uniformContinuumGapProvedIsFalse
          LatticeGap.canonicalLatticeMassGapFromTransferMatrixReceipt
    ; sourcedEquationHamiltonianBoundary =
        Sourced.canonicalYMSourcedEquationToHamiltonianQuotientBoundary
    ; sourcedEquationHamiltonianBoundaryCanonical =
        true
    ; sourcedEquationHamiltonianBoundaryCanonicalIsTrue =
        refl
    ; hamiltonianRequirementNormalizer =
        Normalizer.canonicalYMSelfAdjointHamiltonianQuotientRequirementNormalizer
    ; hamiltonianRequirementNormalizerCanonical =
        true
    ; hamiltonianRequirementNormalizerCanonicalIsTrue =
        refl
    ; selectedCarrierLowerBound =
        Hamiltonian.canonicalSelectedCarrierSpectralLowerBoundReceipt
    ; selectedCarrierLowerBoundCanonical =
        true
    ; selectedCarrierLowerBoundCanonicalIsTrue =
        refl
    ; selectedFiniteCarrierLowerBoundAvailable =
        Hamiltonian.SelectedCarrierSpectralLowerBoundReceipt.finiteCarrierLowerBoundAvailableIsTrue
          Hamiltonian.canonicalSelectedCarrierSpectralLowerBoundReceipt
    ; selectedCarrierLowerBoundNotTransportedToRealYM =
        Hamiltonian.SelectedCarrierSpectralLowerBoundReceipt.lowerBoundTransportedToRealYMIsFalse
          Hamiltonian.canonicalSelectedCarrierSpectralLowerBoundReceipt
    ; sprint129TransportContext =
        Sprint129.canonicalYMSprint129SpectralGapTransportClosureReceipt
    ; sprint129TransportContextCanonical =
        true
    ; sprint129TransportContextCanonicalIsTrue =
        refl
    ; finiteDepthBTBuildingGaugeModelRecorded =
        true
    ; finiteDepthBTBuildingGaugeModelRecordedIsTrue =
        refl
    ; transferMatrixStageRecorded =
        true
    ; transferMatrixStageRecordedIsTrue =
        refl
    ; reflectionPositivityStageRecorded =
        true
    ; reflectionPositivityStageRecordedIsTrue =
        refl
    ; gaugeInvariantHilbertSpaceConstructed =
        false
    ; gaugeInvariantHilbertSpaceConstructedIsFalse =
        refl
    ; finiteDepthSpectralGapMDRecorded =
        true
    ; finiteDepthSpectralGapMDRecordedIsTrue =
        refl
    ; uniformFiniteBuildingLowerBoundProved =
        false
    ; uniformFiniteBuildingLowerBoundProvedIsFalse =
        refl
    ; continuumTransferFromFiniteBTBuildingProved =
        false
    ; continuumTransferFromFiniteBTBuildingProvedIsFalse =
        refl
    ; upstreamRealCarrierBlocker =
        S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
    ; upstreamRealCarrierBlockerIsSelfAdjointYangMillsHamiltonian =
        refl
    ; exactHardBlocker =
        missingUniformFiniteBuildingMassGapLowerBound
    ; exactHardBlockerIsUniformFiniteBuildingMassGapLowerBound =
        refl
    ; hardBlockers =
        canonicalBTFiniteBuildingYMGapTransferHardBlockers
    ; hardBlockersAreCanonical =
        refl
    ; stages =
        canonicalBTFiniteBuildingYMGapTransferStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        7
    ; stageCountIs7 =
        refl
    ; rows =
        canonicalBTFiniteBuildingYMGapTransferRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        13
    ; rowCountIs13 =
        refl
    ; spectralGapPromoted =
        false
    ; spectralGapPromotedIsFalse =
        refl
    ; continuumTransferPromoted =
        false
    ; continuumTransferPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; boundary =
        "Finite-depth BT product-tree and path-counting receipts supply a discrete building carrier boundary"
        ∷ "Transfer reflection positivity and finite transfer-matrix gap receipts are consumed as finite-stage evidence"
        ∷ "The selected-carrier lower bound is available only on the selected finite carrier and is not transported to real YM"
        ∷ "The gauge-invariant Hilbert space on the finite BT building is named as a target, not constructed here"
        ∷ "The exact BT-building hard blocker is missingUniformFiniteBuildingMassGapLowerBound"
        ∷ "The upstream real-carrier blocker remains missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient"
        ∷ "No finite-building uniform lower bound, continuum transfer, Clay Yang-Mills, or terminal promotion is constructed"
        ∷ []
    }

canonicalBTFiniteBuildingYMGapTransferRowCountIs13 :
  listCount canonicalBTFiniteBuildingYMGapTransferRows ≡ 13
canonicalBTFiniteBuildingYMGapTransferRowCountIs13 =
  refl

canonicalBTFiniteBuildingYMGapTransferStageCountIs7 :
  listCount canonicalBTFiniteBuildingYMGapTransferStages ≡ 7
canonicalBTFiniteBuildingYMGapTransferStageCountIs7 =
  refl

canonicalBTFiniteBuildingYMGapTransferHardBlocker :
  exactHardBlocker canonicalBTFiniteBuildingYMGapTransferBoundary
  ≡
  missingUniformFiniteBuildingMassGapLowerBound
canonicalBTFiniteBuildingYMGapTransferHardBlocker =
  refl

canonicalBTFiniteBuildingYMGapTransferUpstreamBlocker :
  upstreamRealCarrierBlocker canonicalBTFiniteBuildingYMGapTransferBoundary
  ≡
  S8.missingSelfAdjointYangMillsHamiltonianOnCarrierQuotient
canonicalBTFiniteBuildingYMGapTransferUpstreamBlocker =
  refl

canonicalBTFiniteBuildingYMGapTransferUniformLowerBoundFalse :
  uniformFiniteBuildingLowerBoundProved
    canonicalBTFiniteBuildingYMGapTransferBoundary
  ≡
  false
canonicalBTFiniteBuildingYMGapTransferUniformLowerBoundFalse =
  refl

canonicalBTFiniteBuildingYMGapTransferContinuumTransferFalse :
  continuumTransferFromFiniteBTBuildingProved
    canonicalBTFiniteBuildingYMGapTransferBoundary
  ≡
  false
canonicalBTFiniteBuildingYMGapTransferContinuumTransferFalse =
  refl

canonicalBTFiniteBuildingYMGapTransferClayFalse :
  clayYangMillsPromoted canonicalBTFiniteBuildingYMGapTransferBoundary
  ≡
  false
canonicalBTFiniteBuildingYMGapTransferClayFalse =
  refl

canonicalBTFiniteBuildingYMGapTransferTerminalFalse :
  terminalPromotion canonicalBTFiniteBuildingYMGapTransferBoundary
  ≡
  false
canonicalBTFiniteBuildingYMGapTransferTerminalFalse =
  refl
