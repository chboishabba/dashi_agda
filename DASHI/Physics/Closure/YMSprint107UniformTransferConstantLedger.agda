module DASHI.Physics.Closure.YMSprint107UniformTransferConstantLedger where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; lsuc; lzero)

import DASHI.Physics.Closure.YMSprint106EffectiveMassLowerBound
  as EffectiveMass106
import DASHI.Physics.Closure.YMSprint106TransferMatrixGapComparison
  as TransferMatrix106

------------------------------------------------------------------------
-- Sprint 107 uniform transfer-constant ledger.
--
-- This module records concrete constants and status boundaries for the
-- target lower bound
--
--   gap(T(a)) >= c * m_eff(a) * a.
--
-- It is a constants ledger, not a proof of the comparison theorem.  The
-- constant c is recorded as positive and independent of a on a named
-- lattice-spacing window, with block-size normalization made explicit.  The
-- effective-mass input remains the Sprint 106 WC3 lower-bound surface and
-- does not use the desired mass gap.  The transfer comparison remains open.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

ledgerRecorded : Bool
ledgerRecorded = true

targetLowerBoundProvedHere : Bool
targetLowerBoundProvedHere = false

transferComparisonProvedHere : Bool
transferComparisonProvedHere = false

uniformConstantPositive : Bool
uniformConstantPositive = true

uniformConstantIndependentOfA : Bool
uniformConstantIndependentOfA = true

effectiveMassIndependentOfDesiredGap : Bool
effectiveMassIndependentOfDesiredGap = true

aWindowNonempty : Bool
aWindowNonempty = true

blockSizeNormalizationFixed : Bool
blockSizeNormalizationFixed = true

constantNameText : String
constantNameText = "c_transfer"

constantConcreteValueText : String
constantConcreteValueText = "c_transfer = 1/64"

constantPositivityText : String
constantPositivityText =
  "c_transfer is recorded as 1/64, hence positive in the constants ledger."

constantIndependenceText : String
constantIndependenceText =
  "c_transfer is fixed once for the Sprint107 transfer ledger and does not vary with lattice spacing a."

aWindowText : String
aWindowText =
  "a-window: 0 < a <= a_0 with canonical a_0 index recorded as 16."

aWindowBoundaryText : String
aWindowBoundaryText =
  "The window is a status boundary for the comparison target; no continuum a -> 0 theorem is inferred from this ledger alone."

blockSizeNormalizationText : String
blockSizeNormalizationText =
  "Block-size normalization: transfer steps are measured in one normalized time block and the comparison factor is charged to c_transfer."

blockSizeConcreteText : String
blockSizeConcreteText =
  "canonical normalized block size B = 4."

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c_transfer * m_eff(a) * a"

effectiveMassIndependenceText : String
effectiveMassIndependenceText =
  "The Sprint106 effective-mass receipt records desiredMassGapUsed = false; the WC3 effective mass is not computed from a desired mass gap."

transferComparisonOpenText : String
transferComparisonOpenText =
  "Open: prove the DASHI-native transfer comparison from WC3 effective mass to the transfer-matrix spectral gap with the recorded uniform constant."

finiteTransferInputText : String
finiteTransferInputText =
  "Sprint106 transfer-matrix comparison imports finite transfer-matrix definition and finite positive gap status only."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "This Sprint107 ledger records constants for the target inequality; it does not promote the Clay Yang-Mills mass gap."

record UniformTransferConstant : Set where
  constructor mkUniformTransferConstant
  field
    name :
      String
    concreteValue :
      String
    numeratorNat :
      Nat
    denominatorNat :
      Nat
    positive :
      Bool
    independentOfA :
      Bool
    positivityStatement :
      String
    independenceStatement :
      String

record LatticeSpacingWindow : Set where
  constructor mkLatticeSpacingWindow
  field
    statement :
      String
    upperIndexNat :
      Nat
    nonempty :
      Bool
    lowerBoundStrict :
      Bool
    upperBoundInclusive :
      Bool
    continuumTheoremClaimedHere :
      Bool
    boundary :
      String

record BlockSizeNormalization : Set where
  constructor mkBlockSizeNormalization
  field
    statement :
      String
    concreteBlockSizeNat :
      Nat
    fixedForLedger :
      Bool
    chargedIntoUniformConstant :
      Bool
    changesWithA :
      Bool
    concreteValue :
      String

record EffectiveMassInputBoundary : Set (lsuc lzero) where
  constructor mkEffectiveMassInputBoundary
  field
    sprint106Receipt :
      EffectiveMass106.YMSprint106EffectiveMassLowerBoundReceipt
    statement :
      String
    desiredMassGapUsedBySprint106 :
      Bool
    independentOfDesiredMassGap :
      Bool
    lowerBoundSurfaceRecorded :
      Bool
    transferGapComparisonAlreadyProved :
      Bool

record TransferComparisonBoundary : Set where
  constructor mkTransferComparisonBoundary
  field
    sprint106Receipt :
      TransferMatrix106.YMSprint106TransferMatrixGapComparisonReceipt
    targetFormula :
      String
    status :
      String
    requiredForFinalGap :
      Bool
    provedHere :
      Bool
    finiteTransferMatrixDefined :
      Bool
    finiteTransferGapPositive :
      Bool
    uniformContinuumLowerBoundProvedHere :
      Bool

record UniformTransferTargetLedger : Set (lsuc lzero) where
  constructor mkUniformTransferTargetLedger
  field
    uniformConstant :
      UniformTransferConstant
    latticeSpacingWindow :
      LatticeSpacingWindow
    blockSizeNormalization :
      BlockSizeNormalization
    effectiveMassBoundary :
      EffectiveMassInputBoundary
    transferComparisonBoundary :
      TransferComparisonBoundary
    targetFormula :
      String
    targetLowerBoundProved :
      Bool
    ledgerInhabited :
      Bool
    clayYangMillsPromotedHere :
      Bool
    boundary :
      String

canonicalUniformTransferConstant : UniformTransferConstant
canonicalUniformTransferConstant =
  mkUniformTransferConstant
    constantNameText
    constantConcreteValueText
    1
    64
    uniformConstantPositive
    uniformConstantIndependentOfA
    constantPositivityText
    constantIndependenceText

canonicalLatticeSpacingWindow : LatticeSpacingWindow
canonicalLatticeSpacingWindow =
  mkLatticeSpacingWindow
    aWindowText
    16
    aWindowNonempty
    true
    true
    false
    aWindowBoundaryText

canonicalBlockSizeNormalization : BlockSizeNormalization
canonicalBlockSizeNormalization =
  mkBlockSizeNormalization
    blockSizeNormalizationText
    4
    blockSizeNormalizationFixed
    true
    false
    blockSizeConcreteText

canonicalEffectiveMassInputBoundary :
  EffectiveMassInputBoundary
canonicalEffectiveMassInputBoundary =
  mkEffectiveMassInputBoundary
    EffectiveMass106.canonicalYMSprint106EffectiveMassLowerBoundReceipt
    effectiveMassIndependenceText
    EffectiveMass106.effectiveMassUsesDesiredMassGap
    effectiveMassIndependentOfDesiredGap
    EffectiveMass106.wc3LowerBoundSurfaceRecorded
    EffectiveMass106.transferGapComparisonTheoremProved

canonicalTransferComparisonBoundary :
  TransferComparisonBoundary
canonicalTransferComparisonBoundary =
  mkTransferComparisonBoundary
    TransferMatrix106.canonicalYMSprint106TransferMatrixGapComparisonReceipt
    targetFormulaText
    transferComparisonOpenText
    true
    transferComparisonProvedHere
    TransferMatrix106.finiteTransferMatrixDefined
    TransferMatrix106.finiteTransferGapPositive
    TransferMatrix106.uniformContinuumLowerBoundProved

canonicalUniformTransferTargetLedger :
  UniformTransferTargetLedger
canonicalUniformTransferTargetLedger =
  mkUniformTransferTargetLedger
    canonicalUniformTransferConstant
    canonicalLatticeSpacingWindow
    canonicalBlockSizeNormalization
    canonicalEffectiveMassInputBoundary
    canonicalTransferComparisonBoundary
    targetFormulaText
    targetLowerBoundProvedHere
    ledgerRecorded
    clayYangMillsPromoted
    nonPromotionBoundaryText

canonicalReceipt : UniformTransferTargetLedger
canonicalReceipt =
  canonicalUniformTransferTargetLedger

canonicalConstantPositiveAndUniformInA : Bool
canonicalConstantPositiveAndUniformInA =
  UniformTransferConstant.positive canonicalUniformTransferConstant

canonicalComparisonStillOpen : Bool
canonicalComparisonStillOpen = true

canonicalClayYangMillsPromotedHere : Bool
canonicalClayYangMillsPromotedHere =
  UniformTransferTargetLedger.clayYangMillsPromotedHere
    canonicalUniformTransferTargetLedger
