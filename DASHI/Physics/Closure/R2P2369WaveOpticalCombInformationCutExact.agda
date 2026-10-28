module DASHI.Physics.Closure.R2P2369WaveOpticalCombInformationCutExact where

------------------------------------------------------------------------
-- 369 WAVE / OPTICAL-COMB INFORMATION CUT
--
-- MATHEMATICAL OWNER / PRIOR ART:
-- Daubechies 1992 (wavelets), Hall / Haensch / Diddams frequency-comb
-- metrology, and Caldwell / Triano / Sinclair 2025 optical transfer.
-- Reuse exact DASHI wave observer and generic nonfactorability theorems.
-- The original theorem identities and their authors stay with their owners.
--
-- DASHI NEW FINITE ADAPTER:
-- Two exact *synthetic* signed beat branches have equal absolute beat
-- amplitude and identical 369 trit observer, but DIFFERENT optical Hz.
-- Consequently no map out of that trit alone can recover the signed
-- optical carrier. Encoding the full state together with the trit
-- remains invertible. This identifies a concrete instrument-data loss cut.
--
-- Wave/369 addresses, C3 phases, finite wave steps and sampled complex
-- phases do NOT construct an actual optical clock, link stabiliser,
-- atmospheric reciprocity, continuous Maxwell solution or quantum gravity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as Trit
import Base369
import DASHI.Foundations.Base369TriTruthField
import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as Wave
import DASHI.Foundations.Base369SymmetryWaveRound9Validation as Round9
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IndexedRelationalPadicWaveContinuousAdaptersExact as Indexed
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.ShiftWaveRefinementSeam as Seam
import DASHI.Physics.Base369PhaseBridge as Phase369
import DASHI.Physics.WaveAlgorithmLift as Algorithm
import DASHI.Physics.Closure.Base369PolyphaseKernelBoundary as Phase
import DASHI.Foundations.Base369PolyphaseCharacters as Characters
import DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw as SI
import DASHI.Physics.Closure.R2P2MountainOpticalClockComparisonExact as R2P2

data BeatBranch : Set where
  aboveTooth : BeatBranch
  belowTooth : BeatBranch

-- These are exactly the prior R2P2 source-written synthetic comb witnesses.
-- 3*10 + 2 = 32 Hz; signed beat +/- 4 gives 36 or 28 Hz.
branchOpticalHz : BeatBranch → Nat
branchOpticalHz aboveTooth =
  R2P2.AboveCombTooth.opticalHz R2P2.exampleAboveCombTooth
branchOpticalHz belowTooth =
  R2P2.BelowCombTooth.opticalHz R2P2.exampleBelowCombTooth

aboveBranchIs36 : branchOpticalHz aboveTooth ≡ 36
aboveBranchIs36 = refl

belowBranchIs28 : branchOpticalHz belowTooth ≡ 28
belowBranchIs28 = refl

-- An absolute beat-size observer retains no beat sign.
-- Its 369 trit is deliberately constant on these two synthetic samples.
absoluteBeatOrientation : BeatBranch → Trit.SSPTrit
absoluteBeatOrientation aboveTooth = Trit.sspZero
absoluteBeatOrientation belowTooth = Trit.sspZero

sameAbsoluteBeatOrientation :
  absoluteBeatOrientation aboveTooth
  ≡ absoluteBeatOrientation belowTooth
sameAbsoluteBeatOrientation = refl

differentSignedOpticalHz :
  branchOpticalHz aboveTooth ≡ branchOpticalHz belowTooth → ⊥
differentSignedOpticalHz ()

-- Reuse the source-owned generic nonfactorability theorem.
beatSignInformationCollision :
  Core.ConsumerCollision absoluteBeatOrientation branchOpticalHz
beatSignInformationCollision =
  NF.nonFactorabilityWitness
    aboveTooth
    belowTooth
    sameAbsoluteBeatOrientation
    differentSignedOpticalHz

absoluteBeatTritCannotRecoverOpticalHz :
  Core.ConsumerSufficient absoluteBeatOrientation branchOpticalHz → ⊥
absoluteBeatTritCannotRecoverOpticalHz =
  Core.collisionRefutesSufficiency beatSignInformationCollision

-- Any downstream recoding / new 369 names / nonlinear chart of the trit
-- remains insufficient. Data augmentation must retain a signed branch.
renamingTritCannotRestoreBeatSign :
  ∀ {Chart : Set} →
  (rechart : Trit.SSPTrit → Chart) →
  Core.ConsumerSufficient
    (λ branch → rechart (absoluteBeatOrientation branch))
    branchOpticalHz →
  ⊥
renamingTritCannotRestoreBeatSign rechart =
  Core.collisionSurvivesRechart rechart beatSignInformationCollision

-- Source-owned exact-state fibre construction fixes the information loss:
-- the trit is an index and full beat state survives inside the fibre.
signedBeatWaveCoding : Wave.SymbolicCoding BeatBranch
signedBeatWaveCoding =
  Wave.symbolicCoding absoluteBeatOrientation

signedBeatEncodeDecode :
  (branch : BeatBranch) →
  Wave.decode (Wave.encode signedBeatWaveCoding branch) ≡ branch
signedBeatEncodeDecode =
  Round9.symbolicCodingRetainsExactCarrier signedBeatWaveCoding

fullBeatWaveFibreDeterminesOpticalHz :
  Core.ConsumerSufficient
    (Wave.encode signedBeatWaveCoding)
    branchOpticalHz
fullBeatWaveFibreDeterminesOpticalHz =
  NF.factorsThrough
    (λ encoded → branchOpticalHz (Wave.decode encoded))
    (λ branch → refl)

-- Reuse full-state adequacy and the independent existing finite wave seam.
waveEncodedStateIsSufficient :
  Core.ConsumerSufficient (Wave.encode signedBeatWaveCoding)
    (λ (branch : BeatBranch) → branch)
waveEncodedStateIsSufficient =
  Indexed.symbolicEncodedStateIsSufficient signedBeatWaveCoding

shiftFiniteWaveFineProjectsToCoarse :
  Core.ConsumerSufficient Seam.fineObserve Seam.coarseObserve
shiftFiniteWaveFineProjectsToCoarse =
  Indexed.waveFineRecoversCoarse

-- Source-owned physical clock phase and GR redshift are dimensionless
-- observables, but an arbitrary trit is not a phase-calibrated clock datum.
clockPhaseIsDimensionless :
  SI.observableDimension
    (SI.phaseLaw SI.canonicalQuantumClockDimensionlessObservableLaw)
    ≡ SI.dimensionlessVector
clockPhaseIsDimensionless =
  SI.canonicalPhaseObservableDimensionless

redshiftIsDimensionless :
  SI.observableDimension
    (SI.redshiftLaw SI.canonicalQuantumClockDimensionlessObservableLaw)
    ≡ SI.dimensionlessVector
redshiftIsDimensionless =
  SI.canonicalRedshiftObservableDimensionless

finiteC3OneStepIsAdditive :
  (mode : Characters.C3Sequence) →
  (phase : Base369.TriTruth) →
  Characters.characterExponent3 mode (Phase.oneStepPhase phase)
    ≡
  DASHI.Foundations.Base369TriTruthField.triAdd
    (Characters.characterExponent3 mode
      DASHI.Foundations.Base369TriTruthField.triOne)
    (Characters.characterExponent3 mode phase)
finiteC3OneStepIsAdditive = Phase.characterOneStepLaw

-- Existing wave-algorithm carrier proves an involutive trit *encoding*.
-- It does not imply reversal of an observed physical optical signal.
finiteWaveAlgorithmTritInvolution :
  (trit : Algorithm.Trit) →
  Algorithm.tritInvolution (Algorithm.tritInvolution trit) ≡ trit
finiteWaveAlgorithmTritInvolution =
  Algorithm.tritInvolution²

-- Reuse the actual Base369 physics phase bridge rather than asserting
-- that all 3/6/9 coarse projections are interchangeable. q6 and q9
-- respect their declared one-step rotations. Nonary block projection
-- has a *source-owned obstruction* at non-0. Hence choosing the wrong
-- 369 phase quotient can break an expected covariance law even before
-- applying real optical calibration.
sixPhaseCoarseRotationLaw :
  (h : Base369.HexTruth) →
  Phase369.q6 (Base369.rotateHex h)
    ≡ Base369.rotateTri (Phase369.q6 h)
sixPhaseCoarseRotationLaw = Phase369.q6-rotate

ninePhaseCoarseRotationLaw :
  (n : Base369.NonaryTruth) →
  Phase369.q9 (Base369.rotateNonary n)
    ≡ Base369.rotateTri (Phase369.q9 n)
ninePhaseCoarseRotationLaw = Phase369.q9-rotate

nonaryBlockCoarsePhaseRotationObstruction :
  Phase369.coarseNonaryBlock (Base369.rotateNonary Base369.non-0)
    ≡
  Base369.rotateTri (Phase369.coarseNonaryBlock Base369.non-0)
    →
  ⊥
nonaryBlockCoarsePhaseRotationObstruction =
  Phase369.coarseNonaryBlock-rotate-obstruction

-- Wave algorithm's generic Hilbert/unitarity obligations were not solved
-- by finite synthetic beat witnesses.
record WaveCombAuthorityBoundary : Set where
  field
    source : R2P2.R2P2ClockComparisonBoundary
    sourceCanonical :
      source ≡ R2P2.canonicalR2P2ClockComparisonBoundary
    exactWaveCarrier : Wave.SymbolicCoding BeatBranch
    waveCarrierCanonical : exactWaveCarrier ≡ signedBeatWaveCoding
    signedBeatIsRequiredForFrequency : Bool
    signedBeatIsRequiredForFrequencyIsTrue :
      signedBeatIsRequiredForFrequency ≡ true
    fullStateCanBeRecovered : Bool
    fullStateCanBeRecoveredIsTrue : fullStateCanBeRecovered ≡ true
    genericWaveAlgorithmCanBeFullyInstantiated : Bool
    genericWaveAlgorithmCannotBeFullyInstantiated :
      genericWaveAlgorithmCanBeFullyInstantiated ≡ false
    c3ProvesOpticalCarrierPhaseCalibration : Bool
    c3DoesNotProveOpticalCarrierPhaseCalibration :
      c3ProvesOpticalCarrierPhaseCalibration ≡ false
    opticalPhaseContinuityMeasuredHere : Bool
    noMeasuredPhaseContinuity :
      opticalPhaseContinuityMeasuredHere ≡ false
    twoWayTransferReciprocityMeasuredHere : Bool
    noMeasuredTransferReciprocity :
      twoWayTransferReciprocityMeasuredHere ≡ false
    quantumGravityProofClaimed : Bool
    noQuantumGravityProofClaimed : quantumGravityProofClaimed ≡ false
    pendingExternalSourceItems : List String

open WaveCombAuthorityBoundary public

canonicalWaveCombAuthorityBoundary : WaveCombAuthorityBoundary
canonicalWaveCombAuthorityBoundary = record
  { source = R2P2.canonicalR2P2ClockComparisonBoundary
  ; sourceCanonical = refl
  ; exactWaveCarrier = signedBeatWaveCoding
  ; waveCarrierCanonical = refl
  ; signedBeatIsRequiredForFrequency = true
  ; signedBeatIsRequiredForFrequencyIsTrue = refl
  ; fullStateCanBeRecovered = true
  ; fullStateCanBeRecoveredIsTrue = refl
  ; genericWaveAlgorithmCanBeFullyInstantiated = false
  ; genericWaveAlgorithmCannotBeFullyInstantiated = refl
  ; c3ProvesOpticalCarrierPhaseCalibration = false
  ; c3DoesNotProveOpticalCarrierPhaseCalibration = refl
  ; opticalPhaseContinuityMeasuredHere = false
  ; noMeasuredPhaseContinuity = refl
  ; twoWayTransferReciprocityMeasuredHere = false
  ; noMeasuredTransferReciprocity = refl
  ; quantumGravityProofClaimed = false
  ; noQuantumGravityProofClaimed = refl
  ; pendingExternalSourceItems =
      "source-owned optical comb mode number, signed beat, f_CEO and f_rep traces"
      ∷ "continuous unwrapped carrier phase and phase-slip/cycle-slip checks"
      ∷ "atmospheric and fibre directional phase/noise transfer functions"
      ∷ "nonreciprocal turbulence, time of flight and moving-platform corrections"
      ∷ "same-epoch calibrated optical frequency and SI uncertainty"
      ∷ "surveyed geopotential and gravity-residual model"
      ∷ []
  }

waveBridgeDoesNotCalibratePhysicalPhase :
  c3ProvesOpticalCarrierPhaseCalibration canonicalWaveCombAuthorityBoundary ≡ false
waveBridgeDoesNotCalibratePhysicalPhase =
  c3DoesNotProveOpticalCarrierPhaseCalibration canonicalWaveCombAuthorityBoundary

waveBridgeDoesNotObserveQuantumGravity :
  quantumGravityProofClaimed canonicalWaveCombAuthorityBoundary ≡ false
waveBridgeDoesNotObserveQuantumGravity =
  noQuantumGravityProofClaimed canonicalWaveCombAuthorityBoundary
