module DASHI.Physics.Closure.YMSprint107FiniteContinuumUniformityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint106EffectiveMassLowerBound
  as EffectiveMass106
import DASHI.Physics.Closure.YMSprint106TransferGapLowerBoundAssembly
  as Assembly106
import DASHI.Physics.Closure.YMSprint106TransferMatrixGapComparison
  as TransferMatrix106

------------------------------------------------------------------------
-- Sprint 107 finite-to-continuum uniformity boundary.
--
-- This module records the boundary condition for promoting finite transfer
-- positivity toward a continuum lower bound:
--
--   gap(T(a)) >= c * m_eff(a) * a
--
-- The receipt is intentionally status-level.  It records the required uniform
-- a-window, the needed c > 0 witness status, and the no-spectral-pollution /
-- Mosco-style passage boundary as obligations.  Finite transfer positivity is
-- imported as support, but is explicitly not enough to prove the continuum
-- theorem.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

boundaryReceiptRecorded : Bool
boundaryReceiptRecorded = true

finiteTransferPositiveImported : Bool
finiteTransferPositiveImported =
  TransferMatrix106.finiteTransferGapPositive

finiteTransferPositiveEnoughForContinuum : Bool
finiteTransferPositiveEnoughForContinuum = false

uniformAWindowRecorded : Bool
uniformAWindowRecorded = true

uniformAWindowProvedHere : Bool
uniformAWindowProvedHere = false

positiveCStatusRecorded : Bool
positiveCStatusRecorded = true

positiveCProvedHere : Bool
positiveCProvedHere = false

noSpectralPollutionBoundaryRecorded : Bool
noSpectralPollutionBoundaryRecorded = true

moscoStyleBoundaryRecorded : Bool
moscoStyleBoundaryRecorded = true

continuumPassageProvedHere : Bool
continuumPassageProvedHere = false

targetLowerBoundTheoremProvedHere : Bool
targetLowerBoundTheoremProvedHere = false

actualProofPresent : Bool
actualProofPresent = false

targetFormulaText : String
targetFormulaText =
  "gap(T(a)) >= c * m_eff(a) * a"

uniformAWindowText : String
uniformAWindowText =
  "There must be an a-window 0 < a <= a0 on which the comparison constants and effective-mass lower-bound surface are uniform."

positiveCStatusText : String
positiveCStatusText =
  "The continuum comparison needs a single constant c with c > 0 that is independent of a throughout the uniform a-window."

noSpectralPollutionText : String
noSpectralPollutionText =
  "The finite transfer spectra must pass to the continuum without spectral pollution at the bottom of the physical Hamiltonian spectrum."

moscoStyleBoundaryText : String
moscoStyleBoundaryText =
  "A Mosco-style or equivalent quadratic-form convergence boundary must identify the continuum operator and preserve the relevant lower bound."

finiteTransferNotEnoughText : String
finiteTransferNotEnoughText =
  "Finite transfer positivity is necessary support, but it does not by itself imply a uniform continuum mass-gap lower bound."

theoremOpenUnlessProofText : String
theoremOpenUnlessProofText =
  "The target lower-bound theorem remains open unless an actual DASHI-native proof of the uniform window, c > 0, and continuum spectral passage is supplied."

sprint106EffectiveMassPath : String
sprint106EffectiveMassPath =
  "DASHI/Physics/Closure/YMSprint106EffectiveMassLowerBound.agda"

sprint106TransferMatrixPath : String
sprint106TransferMatrixPath =
  "DASHI/Physics/Closure/YMSprint106TransferMatrixGapComparison.agda"

sprint106AssemblyPath : String
sprint106AssemblyPath =
  "DASHI/Physics/Closure/YMSprint106TransferGapLowerBoundAssembly.agda"

data BoundaryStatus : Set where
  imported-finite-support :
    BoundaryStatus
  required-uniform-window :
    BoundaryStatus
  required-positive-c :
    BoundaryStatus
  required-continuum-spectral-passage :
    BoundaryStatus
  open-theorem-boundary :
    BoundaryStatus
  not-promoted :
    BoundaryStatus

record UniformAWindowStatus : Set where
  constructor mkUniformAWindowStatus
  field
    statement :
      String
    recorded :
      Bool
    required :
      Bool
    provedHere :
      Bool
    status :
      BoundaryStatus

record PositiveConstantStatus : Set where
  constructor mkPositiveConstantStatus
  field
    formula :
      String
    statement :
      String
    cPositiveRequired :
      Bool
    cIndependentOfARequired :
      Bool
    recorded :
      Bool
    provedHere :
      Bool
    status :
      BoundaryStatus

record ContinuumSpectralPassageBoundary : Set where
  constructor mkContinuumSpectralPassageBoundary
  field
    noSpectralPollutionStatement :
      String
    moscoStyleStatement :
      String
    noSpectralPollutionRecorded :
      Bool
    moscoStyleEvidenceRecorded :
      Bool
    passageRequired :
      Bool
    passageProvedHere :
      Bool
    status :
      BoundaryStatus

record FiniteTransferSupportBoundary : Set where
  constructor mkFiniteTransferSupportBoundary
  field
    transferMatrixReceipt :
      TransferMatrix106.YMSprint106TransferMatrixGapComparisonReceipt
    importedFiniteTransferPositive :
      Bool
    finiteTransferPositiveNeeded :
      Bool
    finiteTransferPositiveEnough :
      Bool
    limitation :
      String
    status :
      BoundaryStatus

record Sprint106TypedInputs : Set₁ where
  constructor mkSprint106TypedInputs
  field
    effectiveMassReceipt :
      EffectiveMass106.YMSprint106EffectiveMassLowerBoundReceipt
    transferMatrixReceipt :
      TransferMatrix106.YMSprint106TransferMatrixGapComparisonReceipt
    assemblyReceipt :
      Assembly106.TransferGapLowerBoundAssemblyReceipt
    effectiveMassPath :
      String
    transferMatrixPath :
      String
    assemblyPath :
      String
    effectiveMassImported :
      Bool
    transferMatrixImported :
      Bool
    assemblyImported :
      Bool

record TheoremBoundaryStatus : Set where
  constructor mkTheoremBoundaryStatus
  field
    target :
      String
    theoremOpenUnlessProofPresent :
      String
    uniformWindowProved :
      Bool
    positiveCProved :
      Bool
    continuumPassageProved :
      Bool
    actualProofPresentStatus :
      Bool
    theoremProvedHere :
      Bool
    clayYangMillsPromotedHere :
      Bool
    status :
      BoundaryStatus

record YMSprint107FiniteContinuumUniformityBoundaryReceipt : Set₁ where
  constructor mkYMSprint107FiniteContinuumUniformityBoundaryReceipt
  field
    typedInputs :
      Sprint106TypedInputs
    uniformAWindow :
      UniformAWindowStatus
    positiveConstant :
      PositiveConstantStatus
    continuumSpectralPassage :
      ContinuumSpectralPassageBoundary
    finiteTransferSupport :
      FiniteTransferSupportBoundary
    theoremBoundary :
      TheoremBoundaryStatus
    receiptRecorded :
      Bool
    clayYangMillsPromotedHere :
      Bool

canonicalUniformAWindowStatus : UniformAWindowStatus
canonicalUniformAWindowStatus =
  mkUniformAWindowStatus
    uniformAWindowText
    uniformAWindowRecorded
    true
    uniformAWindowProvedHere
    required-uniform-window

canonicalPositiveConstantStatus : PositiveConstantStatus
canonicalPositiveConstantStatus =
  mkPositiveConstantStatus
    targetFormulaText
    positiveCStatusText
    true
    true
    positiveCStatusRecorded
    positiveCProvedHere
    required-positive-c

canonicalContinuumSpectralPassageBoundary :
  ContinuumSpectralPassageBoundary
canonicalContinuumSpectralPassageBoundary =
  mkContinuumSpectralPassageBoundary
    noSpectralPollutionText
    moscoStyleBoundaryText
    noSpectralPollutionBoundaryRecorded
    moscoStyleBoundaryRecorded
    true
    continuumPassageProvedHere
    required-continuum-spectral-passage

canonicalFiniteTransferSupportBoundary : FiniteTransferSupportBoundary
canonicalFiniteTransferSupportBoundary =
  mkFiniteTransferSupportBoundary
    TransferMatrix106.canonicalYMSprint106TransferMatrixGapComparisonReceipt
    finiteTransferPositiveImported
    true
    finiteTransferPositiveEnoughForContinuum
    finiteTransferNotEnoughText
    imported-finite-support

canonicalSprint106TypedInputs : Sprint106TypedInputs
canonicalSprint106TypedInputs =
  mkSprint106TypedInputs
    EffectiveMass106.canonicalYMSprint106EffectiveMassLowerBoundReceipt
    TransferMatrix106.canonicalYMSprint106TransferMatrixGapComparisonReceipt
    Assembly106.canonicalTransferGapLowerBoundAssemblyReceipt
    sprint106EffectiveMassPath
    sprint106TransferMatrixPath
    sprint106AssemblyPath
    true
    true
    true

canonicalTheoremBoundaryStatus : TheoremBoundaryStatus
canonicalTheoremBoundaryStatus =
  mkTheoremBoundaryStatus
    targetFormulaText
    theoremOpenUnlessProofText
    uniformAWindowProvedHere
    positiveCProvedHere
    continuumPassageProvedHere
    actualProofPresent
    targetLowerBoundTheoremProvedHere
    clayYangMillsPromoted
    open-theorem-boundary

canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt :
  YMSprint107FiniteContinuumUniformityBoundaryReceipt
canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt =
  mkYMSprint107FiniteContinuumUniformityBoundaryReceipt
    canonicalSprint106TypedInputs
    canonicalUniformAWindowStatus
    canonicalPositiveConstantStatus
    canonicalContinuumSpectralPassageBoundary
    canonicalFiniteTransferSupportBoundary
    canonicalTheoremBoundaryStatus
    boundaryReceiptRecorded
    clayYangMillsPromoted

canonicalReceipt : YMSprint107FiniteContinuumUniformityBoundaryReceipt
canonicalReceipt =
  canonicalYMSprint107FiniteContinuumUniformityBoundaryReceipt

canonicalReceiptFiniteTransferPositiveEnough : Bool
canonicalReceiptFiniteTransferPositiveEnough =
  FiniteTransferSupportBoundary.finiteTransferPositiveEnough
    (YMSprint107FiniteContinuumUniformityBoundaryReceipt.finiteTransferSupport
      canonicalReceipt)

canonicalReceiptTheoremProvedHere : Bool
canonicalReceiptTheoremProvedHere =
  TheoremBoundaryStatus.theoremProvedHere
    (YMSprint107FiniteContinuumUniformityBoundaryReceipt.theoremBoundary
      canonicalReceipt)

canonicalReceiptClayYangMillsPromoted : Bool
canonicalReceiptClayYangMillsPromoted =
  YMSprint107FiniteContinuumUniformityBoundaryReceipt.clayYangMillsPromotedHere
    canonicalReceipt
