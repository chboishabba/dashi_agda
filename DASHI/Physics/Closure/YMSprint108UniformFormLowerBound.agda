module DASHI.Physics.Closure.YMSprint108UniformFormLowerBound where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; lsuc; lzero)

import DASHI.Physics.Closure.YMSprint106EffectiveMassLowerBound
  as EffectiveMass106
import DASHI.Physics.Closure.YMSprint107FiniteContinuumUniformityBoundary
  as Uniformity107
import DASHI.Physics.Closure.YMSprint107UniformTransferConstantLedger
  as ConstantLedger107

------------------------------------------------------------------------
-- Sprint 108 uniform quadratic/form lower-bound ledger.
--
-- This module consumes only stable Sprint106/Sprint107 surfaces and records
-- the uniform-in-a form target
--
--   gap(T(a)) >= c_transfer * m_eff(a) * a
--
-- with c_transfer fixed as 1/64.  It is an inhabited ledger of constants,
-- normalization, lower-bound form status, and exact theorem blockers.  The
-- analytic lower-bound theorem and Clay Yang-Mills promotion remain open.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

uniformFormLedgerRecorded : Bool
uniformFormLedgerRecorded = true

uniformFormLowerBoundTheoremProved : Bool
uniformFormLowerBoundTheoremProved = false

quadraticFormCoercivityProvedHere : Bool
quadraticFormCoercivityProvedHere = false

transferComparisonProvedHere : Bool
transferComparisonProvedHere =
  ConstantLedger107.transferComparisonProvedHere

continuumSpectralPassageProvedHere : Bool
continuumSpectralPassageProvedHere =
  Uniformity107.continuumPassageProvedHere

normalizationWindowProvedHere : Bool
normalizationWindowProvedHere =
  Uniformity107.uniformAWindowProvedHere

wc3EffectiveMassIndependenceRecorded : Bool
wc3EffectiveMassIndependenceRecorded =
  ConstantLedger107.effectiveMassIndependentOfDesiredGap

cTransferNumerator : Nat
cTransferNumerator = 1

cTransferDenominator : Nat
cTransferDenominator = 64

canonicalBlockSizeNat : Nat
canonicalBlockSizeNat = 4

canonicalAUpperIndexNat : Nat
canonicalAUpperIndexNat = 16

cTransferNameText : String
cTransferNameText = "c_transfer"

cTransferValueText : String
cTransferValueText = "c_transfer = 1/64"

targetFormLowerBoundText : String
targetFormLowerBoundText =
  "gap(T(a)) >= c_transfer * m_eff(a) * a"

quadraticFormStatementText : String
quadraticFormStatementText =
  "For normalized transfer block forms Q_a, the recorded target is Q_a(v) >= c_transfer * m_eff(a) * a * N_a(v) on the physical normalized domain."

spectralGapStatementText : String
spectralGapStatementText =
  "The spectral-gap form of the same ledger is gap(T(a)) >= c_transfer * m_eff(a) * a."

uniformInAStatementText : String
uniformInAStatementText =
  "The constants c_transfer, block size, and WC3 effective-mass independence are recorded uniformly for 0 < a <= a0."

normalizationWindowText : String
normalizationWindowText =
  "Normalization window: 0 < a <= a0, canonical a0 index 16, one normalized transfer block B = 4, and transfer-charge factor c_transfer = 1/64."

wc3IndependenceText : String
wc3IndependenceText =
  "Sprint106 records desiredMassGapUsed = false, so the WC3 effective-mass lower-bound surface is independent of the desired continuum mass gap."

notATheoremText : String
notATheoremText =
  "This Sprint108 surface records the uniform form lower-bound ledger; it does not prove the analytic lower-bound theorem."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "No Clay Yang-Mills promotion is made: clayYangMillsPromoted remains false."

transferComparisonBlockerText : String
transferComparisonBlockerText =
  "Blocker: prove the DASHI-native transfer comparison from WC3 effective mass to the transfer-matrix spectral gap with constant c_transfer."

uniformWindowBlockerText : String
uniformWindowBlockerText =
  "Blocker: prove the normalization window and all constants are uniform throughout 0 < a <= a0."

continuumPassageBlockerText : String
continuumPassageBlockerText =
  "Blocker: prove no-spectral-pollution and Mosco-style quadratic-form passage to the continuum operator."

formDomainBlockerText : String
formDomainBlockerText =
  "Blocker: identify the physical normalized form domain and norm N_a used by Q_a without changing constants with a."

hamiltonianBridgeBlockerText : String
hamiltonianBridgeBlockerText =
  "Blocker: bridge the transfer lower bound to the Hamiltonian spectral gap without losing the uniform positive factor."

record Sprint108TypedInputs : Set (lsuc lzero) where
  constructor mkSprint108TypedInputs
  field
    effectiveMassReceipt :
      EffectiveMass106.YMSprint106EffectiveMassLowerBoundReceipt
    uniformConstantLedger :
      ConstantLedger107.UniformTransferTargetLedger
    finiteContinuumBoundary :
      Uniformity107.YMSprint107FiniteContinuumUniformityBoundaryReceipt
    effectiveMassImported :
      Bool
    uniformConstantLedgerImported :
      Bool
    finiteContinuumBoundaryImported :
      Bool
    sprint106DesiredMassGapUsed :
      Bool
    sprint106Wc3LowerBoundRecorded :
      Bool

record UniformInAConstants : Set where
  constructor mkUniformInAConstants
  field
    constantName :
      String
    constantValue :
      String
    numerator :
      Nat
    denominator :
      Nat
    positive :
      Bool
    independentOfA :
      Bool
    blockSizeNat :
      Nat
    aUpperIndexNat :
      Nat
    statement :
      String

record NormalizationWindow : Set where
  constructor mkNormalizationWindow
  field
    statement :
      String
    zeroLessThanA :
      Bool
    upperBoundInclusive :
      Bool
    aWindowNonempty :
      Bool
    blockSizeFixed :
      Bool
    constantsUniformInA :
      Bool
    provedHere :
      Bool

record LowerBoundFormStatement : Set where
  constructor mkLowerBoundFormStatement
  field
    targetFormula :
      String
    quadraticFormStatement :
      String
    spectralGapStatement :
      String
    usesCTransfer :
      Bool
    usesWC3EffectiveMass :
      Bool
    usesLatticeSpacingFactorA :
      Bool
    theoremProvedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool

record WC3IndependenceStatus : Set where
  constructor mkWC3IndependenceStatus
  field
    statement :
      String
    sprint106DesiredMassGapUsed :
      Bool
    independentOfDesiredMassGap :
      Bool
    wc3LowerBoundSurfaceRecorded :
      Bool
    consumedBySprint108 :
      Bool

data ExactBlocker : Set where
  transfer-comparison-blocker :
    ExactBlocker
  normalization-window-blocker :
    ExactBlocker
  continuum-passage-blocker :
    ExactBlocker
  form-domain-blocker :
    ExactBlocker
  hamiltonian-bridge-blocker :
    ExactBlocker

record BlockerReceipt : Set where
  constructor mkBlockerReceipt
  field
    blocker :
      ExactBlocker
    statement :
      String
    requiredForTheorem :
      Bool
    dischargedHere :
      Bool

data BlockerList : Set where
  blockerNil :
    BlockerList
  blockerCons :
    BlockerReceipt -> BlockerList -> BlockerList

record OpenMathBoundary : Set where
  constructor mkOpenMathBoundary
  field
    blockers :
      BlockerList
    transferComparisonProved :
      Bool
    normalizationWindowProved :
      Bool
    continuumPassageProved :
      Bool
    quadraticFormCoercivityProved :
      Bool
    theoremProvedHere :
      Bool
    boundaryStatement :
      String

record YMSprint108UniformFormLowerBoundReceipt : Set (lsuc lzero) where
  constructor mkYMSprint108UniformFormLowerBoundReceipt
  field
    typedInputs :
      Sprint108TypedInputs
    uniformConstants :
      UniformInAConstants
    normalizationWindow :
      NormalizationWindow
    wc3Independence :
      WC3IndependenceStatus
    lowerBoundForm :
      LowerBoundFormStatement
    openBoundary :
      OpenMathBoundary
    ledgerRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool
    nonPromotionBoundary :
      String

canonicalSprint108TypedInputs : Sprint108TypedInputs
canonicalSprint108TypedInputs =
  mkSprint108TypedInputs
    EffectiveMass106.canonicalYMSprint106EffectiveMassLowerBoundReceipt
    ConstantLedger107.canonicalUniformTransferTargetLedger
    Uniformity107.canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt
    true
    true
    true
    EffectiveMass106.effectiveMassUsesDesiredMassGap
    EffectiveMass106.wc3LowerBoundSurfaceRecorded

canonicalUniformInAConstants : UniformInAConstants
canonicalUniformInAConstants =
  mkUniformInAConstants
    cTransferNameText
    cTransferValueText
    cTransferNumerator
    cTransferDenominator
    ConstantLedger107.uniformConstantPositive
    ConstantLedger107.uniformConstantIndependentOfA
    canonicalBlockSizeNat
    canonicalAUpperIndexNat
    uniformInAStatementText

canonicalNormalizationWindow : NormalizationWindow
canonicalNormalizationWindow =
  mkNormalizationWindow
    normalizationWindowText
    true
    true
    ConstantLedger107.aWindowNonempty
    ConstantLedger107.blockSizeNormalizationFixed
    ConstantLedger107.uniformConstantIndependentOfA
    normalizationWindowProvedHere

canonicalLowerBoundFormStatement : LowerBoundFormStatement
canonicalLowerBoundFormStatement =
  mkLowerBoundFormStatement
    targetFormLowerBoundText
    quadraticFormStatementText
    spectralGapStatementText
    true
    true
    true
    uniformFormLowerBoundTheoremProved
    clayYangMillsPromoted

canonicalWC3IndependenceStatus : WC3IndependenceStatus
canonicalWC3IndependenceStatus =
  mkWC3IndependenceStatus
    wc3IndependenceText
    EffectiveMass106.effectiveMassUsesDesiredMassGap
    wc3EffectiveMassIndependenceRecorded
    EffectiveMass106.wc3LowerBoundSurfaceRecorded
    true

transferComparisonBlocker : BlockerReceipt
transferComparisonBlocker =
  mkBlockerReceipt
    transfer-comparison-blocker
    transferComparisonBlockerText
    true
    transferComparisonProvedHere

normalizationWindowBlocker : BlockerReceipt
normalizationWindowBlocker =
  mkBlockerReceipt
    normalization-window-blocker
    uniformWindowBlockerText
    true
    normalizationWindowProvedHere

continuumPassageBlocker : BlockerReceipt
continuumPassageBlocker =
  mkBlockerReceipt
    continuum-passage-blocker
    continuumPassageBlockerText
    true
    continuumSpectralPassageProvedHere

formDomainBlocker : BlockerReceipt
formDomainBlocker =
  mkBlockerReceipt
    form-domain-blocker
    formDomainBlockerText
    true
    quadraticFormCoercivityProvedHere

hamiltonianBridgeBlocker : BlockerReceipt
hamiltonianBridgeBlocker =
  mkBlockerReceipt
    hamiltonian-bridge-blocker
    hamiltonianBridgeBlockerText
    true
    false

canonicalExactBlockers : BlockerList
canonicalExactBlockers =
  blockerCons
    transferComparisonBlocker
    (blockerCons
      normalizationWindowBlocker
      (blockerCons
        continuumPassageBlocker
        (blockerCons
          formDomainBlocker
          (blockerCons hamiltonianBridgeBlocker blockerNil))))

canonicalOpenMathBoundary : OpenMathBoundary
canonicalOpenMathBoundary =
  mkOpenMathBoundary
    canonicalExactBlockers
    transferComparisonProvedHere
    normalizationWindowProvedHere
    continuumSpectralPassageProvedHere
    quadraticFormCoercivityProvedHere
    uniformFormLowerBoundTheoremProved
    notATheoremText

canonicalYMSprint108UniformFormLowerBoundReceipt :
  YMSprint108UniformFormLowerBoundReceipt
canonicalYMSprint108UniformFormLowerBoundReceipt =
  mkYMSprint108UniformFormLowerBoundReceipt
    canonicalSprint108TypedInputs
    canonicalUniformInAConstants
    canonicalNormalizationWindow
    canonicalWC3IndependenceStatus
    canonicalLowerBoundFormStatement
    canonicalOpenMathBoundary
    uniformFormLedgerRecorded
    clayYangMillsPromoted
    nonPromotionBoundaryText

canonicalReceipt : YMSprint108UniformFormLowerBoundReceipt
canonicalReceipt =
  canonicalYMSprint108UniformFormLowerBoundReceipt

canonicalCTransferIsOneOverSixtyFour : Bool
canonicalCTransferIsOneOverSixtyFour = true

canonicalWC3IndependentOfDesiredGap : Bool
canonicalWC3IndependentOfDesiredGap =
  WC3IndependenceStatus.independentOfDesiredMassGap
    canonicalWC3IndependenceStatus

canonicalTheoremStillOpen : Bool
canonicalTheoremStillOpen = true

canonicalClayYangMillsPromotedHere : Bool
canonicalClayYangMillsPromotedHere =
  YMSprint108UniformFormLowerBoundReceipt.clayYangMillsPromotedHere
    canonicalReceipt
