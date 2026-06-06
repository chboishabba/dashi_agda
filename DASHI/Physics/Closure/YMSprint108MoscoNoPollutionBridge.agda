module DASHI.Physics.Closure.YMSprint108MoscoNoPollutionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; lsuc; lzero)

import DASHI.Physics.Closure.YMSprint106EffectiveMassLowerBound
  as EffectiveMass106
import DASHI.Physics.Closure.YMSprint106TransferGapLowerBoundAssembly
  as Assembly106
import DASHI.Physics.Closure.YMSprint106TransferMatrixGapComparison
  as TransferMatrix106
import DASHI.Physics.Closure.YMSprint107FiniteContinuumUniformityBoundary
  as Uniformity107
import DASHI.Physics.Closure.YMSprint107TransferGapCriticalPathAssembly
  as CriticalPath107
import DASHI.Physics.Closure.YMSprint107UniformTransferConstantLedger
  as ConstantLedger107

------------------------------------------------------------------------
-- Sprint 108 Mosco and no-spectral-pollution bridge.
--
-- This module records the continuum spectral-passage part of the uniform
-- transfer lower-bound package:
--
--   gap(T(a)) >= c * m_eff(a) * a
--
-- The bridge is status-level but concrete.  It records the exact ingredients
-- that are still required for a Mosco/no-bottom-spectrum-pollution passage:
-- lower semicontinuity of quadratic forms, liminf lower spectral control,
-- recovery sequences, exclusion of bottom-spectrum pollution, and the explicit
-- fact that finite transfer support alone is not sufficient.  No Clay or
-- target lower-bound promotion is made here.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

bridgeReceiptRecorded : Bool
bridgeReceiptRecorded = true

moscoBridgeProvedHere : Bool
moscoBridgeProvedHere = false

lowerSemicontinuityProvedHere : Bool
lowerSemicontinuityProvedHere = false

liminfSpectralLowerBoundProvedHere : Bool
liminfSpectralLowerBoundProvedHere = false

recoverySequenceConstructedHere : Bool
recoverySequenceConstructedHere = false

noBottomSpectrumPollutionProvedHere : Bool
noBottomSpectrumPollutionProvedHere = false

uniformTransferTargetProvedHere : Bool
uniformTransferTargetProvedHere = false

finiteTransferSupportEnoughAlone : Bool
finiteTransferSupportEnoughAlone = false

finiteTransferSupportImported : Bool
finiteTransferSupportImported =
  TransferMatrix106.finiteTransferGapPositive

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c * m_eff(a) * a"

moscoBridgeStatementText : String
moscoBridgeStatementText =
  "The finite transfer quadratic forms must converge to the continuum closed semibounded form in the Mosco sense on the physical carrier domain."

lowerSemicontinuityStatementText : String
lowerSemicontinuityStatementText =
  "Mosco liminf side: weakly convergent finite-energy approximants must not lose energy below the continuum quadratic form."

liminfSpectralStatementText : String
liminfSpectralStatementText =
  "Spectral liminf side: bottom spectral values of the finite transfer operators must have continuum lower bounds in the physical sector."

recoverySequenceStatementText : String
recoverySequenceStatementText =
  "Mosco recovery side: every continuum finite-energy vector needs finite transfer approximants with matching norm and energy limit."

noBottomPollutionStatementText : String
noBottomPollutionStatementText =
  "No bottom-spectrum pollution: no spurious finite-transfer eigenvalue branch may converge below the continuum physical Hamiltonian bottom."

finiteSupportInsufficientStatementText : String
finiteSupportInsufficientStatementText =
  "Finite transfer positivity is imported support, but by itself it gives no uniform continuum lower bound and no no-pollution theorem."

bridgeToTargetStatementText : String
bridgeToTargetStatementText =
  "When Mosco liminf, recovery, no bottom-spectrum pollution, and uniform constants are all supplied, the bridge targets gap(T(a)) >= c * m_eff(a) * a."

openTheoremBoundaryText : String
openTheoremBoundaryText =
  "The target lower-bound theorem remains open in Sprint108 because this file records required statuses rather than a DASHI-native Mosco/no-pollution proof."

sprint106EffectiveMassPath : String
sprint106EffectiveMassPath =
  "DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda"

sprint106TransferMatrixPath : String
sprint106TransferMatrixPath =
  "DASHI/Physics/Closure/YMSprint106TransferMatrixGapComparison.agda"

sprint106AssemblyPath : String
sprint106AssemblyPath =
  "DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda"

sprint107UniformityPath : String
sprint107UniformityPath =
  "DASHI/Physics/Closure/YMSprint107FiniteContinuumUniformityBoundary.agda"

sprint107ConstantLedgerPath : String
sprint107ConstantLedgerPath =
  "DASHI/Physics/Closure/YMSprint107UniformTransferConstantLedger.agda"

sprint107CriticalPathPath : String
sprint107CriticalPathPath =
  "DASHI/Physics/Closure/YMSprint107TransferGapCriticalPathAssembly.agda"

data MoscoBridgeStatus : Set where
  recorded-required :
    MoscoBridgeStatus
  imported-support :
    MoscoBridgeStatus
  required-not-proved :
    MoscoBridgeStatus
  finite-support-insufficient :
    MoscoBridgeStatus
  target-open :
    MoscoBridgeStatus
  nonpromotion :
    MoscoBridgeStatus

data MoscoBridgeLane : Set where
  lower-semicontinuity-of-forms :
    MoscoBridgeLane
  liminf-spectral-lower-bound :
    MoscoBridgeLane
  recovery-sequence-requirement :
    MoscoBridgeLane
  no-bottom-spectrum-pollution :
    MoscoBridgeLane
  finite-transfer-support-boundary :
    MoscoBridgeLane
  bridge-to-transfer-target :
    MoscoBridgeLane

data BridgeLaneList : Set where
  laneNil :
    BridgeLaneList
  laneCons :
    MoscoBridgeLane -> BridgeLaneList -> BridgeLaneList

canonicalBridgeLanes : BridgeLaneList
canonicalBridgeLanes =
  laneCons
    lower-semicontinuity-of-forms
    (laneCons
      liminf-spectral-lower-bound
      (laneCons
        recovery-sequence-requirement
        (laneCons
          no-bottom-spectrum-pollution
          (laneCons
            finite-transfer-support-boundary
            (laneCons bridge-to-transfer-target laneNil)))))

record Sprint106Sprint107TypedSupply : Set₁ where
  constructor mkSprint106Sprint107TypedSupply
  field
    effectiveMassReceipt :
      EffectiveMass106.YMSprint106EffectiveMassLowerBoundReceipt
    transferMatrixReceipt :
      TransferMatrix106.YMSprint106TransferMatrixGapComparisonReceipt
    transferGapAssemblyReceipt :
      Assembly106.TransferGapLowerBoundAssemblyReceipt
    uniformityReceipt :
      Uniformity107.YMSprint107FiniteContinuumUniformityBoundaryReceipt
    constantLedgerReceipt :
      ConstantLedger107.UniformTransferTargetLedger
    criticalPathReceipt :
      CriticalPath107.TransferGapCriticalPathAssemblyReceipt
    effectiveMassPath :
      String
    transferMatrixPath :
      String
    assemblyPath :
      String
    uniformityPath :
      String
    constantLedgerPath :
      String
    criticalPathPath :
      String
    importsAreSprint106OrSprint107 :
      Bool
    importedClayFlagsKeptFalse :
      Bool

record LowerSemicontinuityOfQuadraticFormsStatus : Set where
  constructor mkLowerSemicontinuityOfQuadraticFormsStatus
  field
    lane :
      MoscoBridgeLane
    statement :
      String
    requiredForMosco :
      Bool
    requiredForTargetBound :
      Bool
    provedHere :
      Bool
    status :
      MoscoBridgeStatus

record LiminfSpectralLowerBoundStatus : Set where
  constructor mkLiminfSpectralLowerBoundStatus
  field
    lane :
      MoscoBridgeLane
    statement :
      String
    followsFromFinitePositivityAlone :
      Bool
    requiresMoscoLiminf :
      Bool
    requiresUniformAWindow :
      Bool
    provedHere :
      Bool
    status :
      MoscoBridgeStatus

record RecoverySequenceRequirementStatus : Set where
  constructor mkRecoverySequenceRequirementStatus
  field
    lane :
      MoscoBridgeLane
    statement :
      String
    requiredForMosco :
      Bool
    constructedHere :
      Bool
    finiteCarrierDensityRequired :
      Bool
    energyRecoveryRequired :
      Bool
    status :
      MoscoBridgeStatus

record NoBottomSpectrumPollutionStatus : Set where
  constructor mkNoBottomSpectrumPollutionStatus
  field
    lane :
      MoscoBridgeLane
    statement :
      String
    requiredForContinuumGap :
      Bool
    strongResolventAloneEnough :
      Bool
    compactnessOrTightnessRequired :
      Bool
    isolatedBottomSectorRequired :
      Bool
    provedHere :
      Bool
    status :
      MoscoBridgeStatus

record FiniteTransferSupportNotEnoughStatus : Set₁ where
  constructor mkFiniteTransferSupportNotEnoughStatus
  field
    lane :
      MoscoBridgeLane
    transferMatrixReceipt :
      TransferMatrix106.YMSprint106TransferMatrixGapComparisonReceipt
    finiteTransferMatrixDefined :
      Bool
    finiteTransferGapPositive :
      Bool
    importedSupport :
      Bool
    enoughAloneForContinuum :
      Bool
    enoughAloneForNoPollution :
      Bool
    limitation :
      String
    status :
      MoscoBridgeStatus

record BridgeToUniformTransferTargetStatus : Set₁ where
  constructor mkBridgeToUniformTransferTargetStatus
  field
    lane :
      MoscoBridgeLane
    targetFormula :
      String
    statement :
      String
    uniformityReceipt :
      Uniformity107.YMSprint107FiniteContinuumUniformityBoundaryReceipt
    constantLedgerReceipt :
      ConstantLedger107.UniformTransferTargetLedger
    criticalPathReceipt :
      CriticalPath107.TransferGapCriticalPathAssemblyReceipt
    moscoInputsAllProvedHere :
      Bool
    noPollutionProvedHere :
      Bool
    uniformConstantsRecorded :
      Bool
    targetTheoremProvedHere :
      Bool
    status :
      MoscoBridgeStatus

record OpenTheoremBoundaryStatus : Set where
  constructor mkOpenTheoremBoundaryStatus
  field
    targetFormula :
      String
    openBoundary :
      String
    lowerSemicontinuityClosed :
      Bool
    liminfSpectralBoundClosed :
      Bool
    recoverySequenceClosed :
      Bool
    noBottomPollutionClosed :
      Bool
    finiteSupportEnoughAlone :
      Bool
    targetTheoremProvedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    status :
      MoscoBridgeStatus

record YMSprint108MoscoNoPollutionBridgeReceipt : Set₁ where
  constructor mkYMSprint108MoscoNoPollutionBridgeReceipt
  field
    typedSupply :
      Sprint106Sprint107TypedSupply
    bridgeLanes :
      BridgeLaneList
    lowerSemicontinuity :
      LowerSemicontinuityOfQuadraticFormsStatus
    liminfSpectralLowerBound :
      LiminfSpectralLowerBoundStatus
    recoverySequenceRequirement :
      RecoverySequenceRequirementStatus
    noBottomSpectrumPollution :
      NoBottomSpectrumPollutionStatus
    finiteTransferSupportBoundary :
      FiniteTransferSupportNotEnoughStatus
    bridgeToTarget :
      BridgeToUniformTransferTargetStatus
    theoremBoundary :
      OpenTheoremBoundaryStatus
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool

canonicalTypedSupply : Sprint106Sprint107TypedSupply
canonicalTypedSupply =
  mkSprint106Sprint107TypedSupply
    EffectiveMass106.canonicalYMSprint106EffectiveMassLowerBoundReceipt
    TransferMatrix106.canonicalYMSprint106TransferMatrixGapComparisonReceipt
    Assembly106.canonicalTransferGapLowerBoundAssemblyReceipt
    Uniformity107.canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt
    ConstantLedger107.canonicalUniformTransferTargetLedger
    CriticalPath107.canonicalTransferGapCriticalPathAssemblyReceipt
    sprint106EffectiveMassPath
    sprint106TransferMatrixPath
    sprint106AssemblyPath
    sprint107UniformityPath
    sprint107ConstantLedgerPath
    sprint107CriticalPathPath
    true
    true

canonicalLowerSemicontinuityStatus :
  LowerSemicontinuityOfQuadraticFormsStatus
canonicalLowerSemicontinuityStatus =
  mkLowerSemicontinuityOfQuadraticFormsStatus
    lower-semicontinuity-of-forms
    lowerSemicontinuityStatementText
    true
    true
    lowerSemicontinuityProvedHere
    required-not-proved

canonicalLiminfSpectralLowerBoundStatus :
  LiminfSpectralLowerBoundStatus
canonicalLiminfSpectralLowerBoundStatus =
  mkLiminfSpectralLowerBoundStatus
    liminf-spectral-lower-bound
    liminfSpectralStatementText
    false
    true
    true
    liminfSpectralLowerBoundProvedHere
    required-not-proved

canonicalRecoverySequenceRequirementStatus :
  RecoverySequenceRequirementStatus
canonicalRecoverySequenceRequirementStatus =
  mkRecoverySequenceRequirementStatus
    recovery-sequence-requirement
    recoverySequenceStatementText
    true
    recoverySequenceConstructedHere
    true
    true
    required-not-proved

canonicalNoBottomSpectrumPollutionStatus :
  NoBottomSpectrumPollutionStatus
canonicalNoBottomSpectrumPollutionStatus =
  mkNoBottomSpectrumPollutionStatus
    no-bottom-spectrum-pollution
    noBottomPollutionStatementText
    true
    false
    true
    true
    noBottomSpectrumPollutionProvedHere
    required-not-proved

canonicalFiniteTransferSupportNotEnoughStatus :
  FiniteTransferSupportNotEnoughStatus
canonicalFiniteTransferSupportNotEnoughStatus =
  mkFiniteTransferSupportNotEnoughStatus
    finite-transfer-support-boundary
    TransferMatrix106.canonicalYMSprint106TransferMatrixGapComparisonReceipt
    TransferMatrix106.finiteTransferMatrixDefined
    TransferMatrix106.finiteTransferGapPositive
    finiteTransferSupportImported
    finiteTransferSupportEnoughAlone
    false
    finiteSupportInsufficientStatementText
    finite-support-insufficient

canonicalBridgeToUniformTransferTargetStatus :
  BridgeToUniformTransferTargetStatus
canonicalBridgeToUniformTransferTargetStatus =
  mkBridgeToUniformTransferTargetStatus
    bridge-to-transfer-target
    targetFormulaText
    bridgeToTargetStatementText
    Uniformity107.canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt
    ConstantLedger107.canonicalUniformTransferTargetLedger
    CriticalPath107.canonicalTransferGapCriticalPathAssemblyReceipt
    moscoBridgeProvedHere
    noBottomSpectrumPollutionProvedHere
    ConstantLedger107.ledgerRecorded
    uniformTransferTargetProvedHere
    target-open

canonicalOpenTheoremBoundaryStatus :
  OpenTheoremBoundaryStatus
canonicalOpenTheoremBoundaryStatus =
  mkOpenTheoremBoundaryStatus
    targetFormulaText
    openTheoremBoundaryText
    lowerSemicontinuityProvedHere
    liminfSpectralLowerBoundProvedHere
    recoverySequenceConstructedHere
    noBottomSpectrumPollutionProvedHere
    finiteTransferSupportEnoughAlone
    uniformTransferTargetProvedHere
    clayYangMillsPromoted
    nonpromotion

canonicalYMSprint108MoscoNoPollutionBridgeReceipt :
  YMSprint108MoscoNoPollutionBridgeReceipt
canonicalYMSprint108MoscoNoPollutionBridgeReceipt =
  mkYMSprint108MoscoNoPollutionBridgeReceipt
    canonicalTypedSupply
    canonicalBridgeLanes
    canonicalLowerSemicontinuityStatus
    canonicalLiminfSpectralLowerBoundStatus
    canonicalRecoverySequenceRequirementStatus
    canonicalNoBottomSpectrumPollutionStatus
    canonicalFiniteTransferSupportNotEnoughStatus
    canonicalBridgeToUniformTransferTargetStatus
    canonicalOpenTheoremBoundaryStatus
    bridgeReceiptRecorded
    clayYangMillsPromoted

canonicalReceipt : YMSprint108MoscoNoPollutionBridgeReceipt
canonicalReceipt =
  canonicalYMSprint108MoscoNoPollutionBridgeReceipt

canonicalReceiptFiniteSupportEnoughAlone : Bool
canonicalReceiptFiniteSupportEnoughAlone =
  FiniteTransferSupportNotEnoughStatus.enoughAloneForContinuum
    (YMSprint108MoscoNoPollutionBridgeReceipt.finiteTransferSupportBoundary
      canonicalReceipt)

canonicalReceiptNoBottomPollutionProvedHere : Bool
canonicalReceiptNoBottomPollutionProvedHere =
  NoBottomSpectrumPollutionStatus.provedHere
    (YMSprint108MoscoNoPollutionBridgeReceipt.noBottomSpectrumPollution
      canonicalReceipt)

canonicalReceiptTargetTheoremProvedHere : Bool
canonicalReceiptTargetTheoremProvedHere =
  OpenTheoremBoundaryStatus.targetTheoremProvedHere
    (YMSprint108MoscoNoPollutionBridgeReceipt.theoremBoundary
      canonicalReceipt)

canonicalReceiptClayYangMillsPromoted : Bool
canonicalReceiptClayYangMillsPromoted =
  YMSprint108MoscoNoPollutionBridgeReceipt.clayYangMillsPromotedHere
    canonicalReceipt
