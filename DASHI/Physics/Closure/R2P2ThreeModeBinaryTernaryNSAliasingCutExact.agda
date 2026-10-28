module DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact where

------------------------------------------------------------------------
-- THREE-MODE FOURIER / CODEC / NAVIER-STOKES INFORMATION CUT
--
-- Scientific prior art: Orszag/Patterson pseudo-spectral dealiasing;
-- Lambert, Reneuve, Augier (2026, arXiv:2603.08892), phase-shifting
-- dealiasing. This is not an original result in Fourier analysis or NS.
--
-- Original DASHI owners: VerifiedFiniteTritCoder, BinaryBalancedTernary-
-- SubcarrierExact, NSIntegerFourierLattice, NSCross369OrientationBridgeExact,
-- SparseTwistLESOperator/Bridge, NSTriadKN369HighHighGramBridgeReceipt.
-- Import them. Do not fork their theorem statements or Monster/3B owners.
--
-- NEW finite application: [-1,0,+1] <-> balanced Trit <-> two-bit code;
-- exact quadratic (+1)+(+1)=+2 versus periodic C3 wrap(+2)=-1;
-- retained mode cannot distinguish a true -1 from an aliased +2.
-- This is a specific Fourier *mode-index* collision, not an equation
-- of optical lattice dynamics, physical wave amplitudes, NS velocity or
-- continuum Navier--Stokes. No Clay/QG theorem is implied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; _∷_; [])
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer.Base using (+_)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Codec.VerifiedFiniteTritCoder as TwoBits
import DASHI.Codec.BalancedTritBitFibre as SignFibre
import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as BinaryInTernary
import DASHI.ComputerScience.BalancedTernaryQutritBasisBridgeExact as QutritBasis
import DASHI.Algebra.Quantum.FiniteQutrit as Qutrit
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Physics.Closure.NSIntegerFourierLattice as NSFourier
import DASHI.Physics.Closure.NSCross369OrientationBridgeExact as NS369
import DASHI.Physics.Closure.NSTriadKN369HighHighGramBridgeReceipt as Gram
import DASHI.Physics.CFD.SparseTwistLESBridge as LES
import DASHI.Physics.CFD.SparseTwistLESOperator as LESOp
import DASHI.Physics.Closure.R2P2OpticalLattice369HamiltonianCutExact as Optical

data ThreeMode : Set where
  modeMinus : ThreeMode
  modeZero : ThreeMode
  modePlus : ThreeMode

threeModeToTrit : ThreeMode → Trit.Trit
threeModeToTrit modeMinus = Trit.neg
threeModeToTrit modeZero = Trit.zer
threeModeToTrit modePlus = Trit.pos

tritToThreeMode : Trit.Trit → ThreeMode
tritToThreeMode Trit.neg = modeMinus
tritToThreeMode Trit.zer = modeZero
tritToThreeMode Trit.pos = modePlus

threeModeAfterTritRoundTrip :
  (mode : ThreeMode) → tritToThreeMode (threeModeToTrit mode) ≡ mode
threeModeAfterTritRoundTrip modeMinus = refl
threeModeAfterTritRoundTrip modeZero = refl
threeModeAfterTritRoundTrip modePlus = refl

tritAfterThreeModeRoundTrip :
  (t : Trit.Trit) → threeModeToTrit (tritToThreeMode t) ≡ t
tritAfterThreeModeRoundTrip Trit.neg = refl
tritAfterThreeModeRoundTrip Trit.zer = refl
tritAfterThreeModeRoundTrip Trit.pos = refl

-- Reuse the canonical two-bit trit coder. 11 is INVALID, not a fourth mode.
threeModeToTwoBits : ThreeMode → TwoBits.Word2
threeModeToTwoBits mode = TwoBits.encodeTrit (threeModeToTrit mode)

twoBitsToThreeMode : TwoBits.Word2 → Maybe ThreeMode
twoBitsToThreeMode TwoBits.word00 = just modeMinus
twoBitsToThreeMode TwoBits.word01 = just modeZero
twoBitsToThreeMode TwoBits.word10 = just modePlus
twoBitsToThreeMode TwoBits.word11 = nothing

threeModeTwoBitRoundTrip :
  (mode : ThreeMode) →
  twoBitsToThreeMode (threeModeToTwoBits mode) ≡ just mode
threeModeTwoBitRoundTrip modeMinus = refl
threeModeTwoBitRoundTrip modeZero = refl
threeModeTwoBitRoundTrip modePlus = refl

twoBitWord11Rejected :
  twoBitsToThreeMode TwoBits.word11 ≡ nothing
twoBitWord11Rejected = refl

inheritedTritCoderRoundTrip :
  (t : Trit.Trit) →
  TwoBits.decodeWord (TwoBits.encodeTrit t) ≡ just t
inheritedTritCoderRoundTrip = TwoBits.decode-encode

-- The original binary-in-ternary strict subcarrier has no zero.
bitToNonzeroMode : Bool → ThreeMode
bitToNonzeroMode false = modeMinus
bitToNonzeroMode true = modePlus

modeToBalancedSSP : ThreeMode → SSP.SSPTrit
modeToBalancedSSP modeMinus = SSP.sspNegOne
modeToBalancedSSP modeZero = SSP.sspZero
modeToBalancedSSP modePlus = SSP.sspPosOne

binarySubcarrierIsTheNonzeroModePart :
  (bit : Bool) →
  modeToBalancedSSP (bitToNonzeroMode bit)
  ≡ BinaryInTernary.embedBit bit
binarySubcarrierIsTheNonzeroModePart false = refl
binarySubcarrierIsTheNonzeroModePart true = refl

binarySubcarrierRoundTrip :
  (bit : Bool) →
  BinaryInTernary.decodeEmbeddedBit
    (modeToBalancedSSP (bitToNonzeroMode bit)) ≡ bit
binarySubcarrierRoundTrip false = refl
binarySubcarrierRoundTrip true = refl

zeroModeIsNotAnEmbeddedBit :
  (bit : Bool) →
  modeToBalancedSSP (bitToNonzeroMode bit) ≡ SSP.sspZero → ⊥
zeroModeIsNotAnEmbeddedBit false =
  BinaryInTernary.centreIsUnusedByBinaryEmbedding false
zeroModeIsNotAnEmbeddedBit true =
  BinaryInTernary.centreIsUnusedByBinaryEmbedding true

-- The original balanced support/sign codec retains the orientation bit
-- only when the mode is nonzero. A support bit ALONE merges +/- modes.
threeModeSupport : ThreeMode → Bool
threeModeSupport mode =
  SignFibre.supportBit (SignFibre.encodeFibre (threeModeToTrit mode))

oppositeModesHaveSameBinarySupport :
  threeModeSupport modeMinus ≡ threeModeSupport modePlus
oppositeModesHaveSameBinarySupport = refl

minusIsNotPlus : modeMinus ≡ modePlus → ⊥
minusIsNotPlus ()

supportForgetsSignedFourierOrientation :
  Core.ConsumerCollision threeModeSupport (λ m → m)
supportForgetsSignedFourierOrientation =
  NF.nonFactorabilityWitness modeMinus modePlus
    oppositeModesHaveSameBinarySupport minusIsNotPlus

supportBitCannotDecodeSignedFourierMode :
  Core.ConsumerSufficient threeModeSupport (λ m → m) → ⊥
supportBitCannotDecodeSignedFourierMode =
  Core.collisionRefutesSufficiency supportForgetsSignedFourierOrientation

fullSupportPlusOptionalSignRecoversThreeMode :
  (mode : ThreeMode) →
  tritToThreeMode
    (SignFibre.decodeFibre
      (SignFibre.encodeFibre (threeModeToTrit mode)))
    ≡ mode
fullSupportPlusOptionalSignRecoversThreeMode modeMinus = refl
fullSupportPlusOptionalSignRecoversThreeMode modeZero = refl
fullSupportPlusOptionalSignRecoversThreeMode modePlus = refl

sourceSignedModeCostIsTwo :
  SignFibre.tritBitCost (threeModeToTrit modePlus) ≡ 2
sourceSignedModeCostIsTwo = refl

sourceZeroModeCostIsOne :
  SignFibre.tritBitCost (threeModeToTrit modeZero) ≡ 1
sourceZeroModeCostIsOne = refl

-- Qutrit *basis label* reuse. Not a quantum state-space equivalence.
threeModeToQutritBasis :
  ThreeMode → Qutrit.QutritBasis
threeModeToQutritBasis mode =
  QutritBasis.tritToQutritBasis (modeToBalancedSSP mode)

data FiveMode : Set where
  wideMinusTwo : FiveMode
  wideMinusOne : FiveMode
  wideZero : FiveMode
  widePlusOne : FiveMode
  widePlusTwo : FiveMode

-- Ordinary signed integer mode addition restricted to [-1,0,+1]^2.
-- All nine combinations are given explicitly.
exactQuadraticModeSum : ThreeMode → ThreeMode → FiveMode
exactQuadraticModeSum modeMinus modeMinus = wideMinusTwo
exactQuadraticModeSum modeMinus modeZero = wideMinusOne
exactQuadraticModeSum modeMinus modePlus = wideZero
exactQuadraticModeSum modeZero modeMinus = wideMinusOne
exactQuadraticModeSum modeZero modeZero = wideZero
exactQuadraticModeSum modeZero modePlus = widePlusOne
exactQuadraticModeSum modePlus modeMinus = wideZero
exactQuadraticModeSum modePlus modeZero = widePlusOne
exactQuadraticModeSum modePlus modePlus = widePlusTwo

-- Correct Galerkin projection is partial: outputs outside the
-- retained integer mode window are discarded, NOT wrapped.
exactRetainedModeProjection : FiveMode → Maybe ThreeMode
exactRetainedModeProjection wideMinusTwo = nothing
exactRetainedModeProjection wideMinusOne = just modeMinus
exactRetainedModeProjection wideZero = just modeZero
exactRetainedModeProjection widePlusOne = just modePlus
exactRetainedModeProjection widePlusTwo = nothing

-- The three-point DFT identifies residue classes modulo 3.
-- This is an intentionally lossy projection of exact integer Fourier labels.
periodicThreePointFold : FiveMode → ThreeMode
periodicThreePointFold wideMinusTwo = modePlus
periodicThreePointFold wideMinusOne = modeMinus
periodicThreePointFold wideZero = modeZero
periodicThreePointFold widePlusOne = modePlus
periodicThreePointFold widePlusTwo = modeMinus

periodicQuadraticModeSum : ThreeMode → ThreeMode → ThreeMode
periodicQuadraticModeSum a b =
  periodicThreePointFold (exactQuadraticModeSum a b)

positivePositiveLeavesThreeModeWindow :
  exactQuadraticModeSum modePlus modePlus ≡ widePlusTwo
positivePositiveLeavesThreeModeWindow = refl

positivePositiveAliasesToNegative :
  periodicQuadraticModeSum modePlus modePlus ≡ modeMinus
positivePositiveAliasesToNegative = refl

-- The selected positive-positive quadratic product leaves no retained
-- coefficient at k=-1 when projected in the exact integer lattice.
correctQuadraticProjectionRemovesPlusTwo :
  exactRetainedModeProjection
    (exactQuadraticModeSum modePlus modePlus) ≡ nothing
correctQuadraticProjectionRemovesPlusTwo = refl

-- Evaluating the same product pointwise on three samples instead
-- spuriously creates a retained negative-frequency contribution.
incorrectQuadraticFoldCreatesMinusOne :
  just (periodicQuadraticModeSum modePlus modePlus) ≡ just modeMinus
incorrectQuadraticFoldCreatesMinusOne = refl


negativeNegativeLeavesThreeModeWindow :
  exactQuadraticModeSum modeMinus modeMinus ≡ wideMinusTwo
negativeNegativeLeavesThreeModeWindow = refl

negativeNegativeAliasesToPositive :
  periodicQuadraticModeSum modeMinus modeMinus ≡ modePlus
negativeNegativeAliasesToPositive = refl

widePlusTwoAndGenuineMinusOneHaveSameThreePointLabel :
  periodicThreePointFold widePlusTwo ≡
  periodicThreePointFold wideMinusOne
widePlusTwoAndGenuineMinusOneHaveSameThreePointLabel = refl

widePlusTwoIsNotMinusOne : widePlusTwo ≡ wideMinusOne → ⊥
widePlusTwoIsNotMinusOne ()

-- Source-owned *generic* nonfactorability, instantiated to Fourier aliasing.
wideModeAliasCollision :
  Core.ConsumerCollision periodicThreePointFold (λ w → w)
wideModeAliasCollision =
  NF.nonFactorabilityWitness
    widePlusTwo wideMinusOne
    widePlusTwoAndGenuineMinusOneHaveSameThreePointLabel
    widePlusTwoIsNotMinusOne

foldedThreePointModeCannotRecoverExactFourierIndex :
  Core.ConsumerSufficient periodicThreePointFold (λ w → w) → ⊥
foldedThreePointModeCannotRecoverExactFourierIndex =
  Core.collisionRefutesSufficiency wideModeAliasCollision

rechartingThreePointModeCannotFixAliasing :
  ∀ {Chart : Set} →
  (chart : ThreeMode → Chart) →
  Core.ConsumerSufficient
    (λ w → chart (periodicThreePointFold w)) (λ w → w) → ⊥
rechartingThreePointModeCannotFixAliasing chart =
  Core.collisionSurvivesRechart chart wideModeAliasCollision

-- Crucially, the NS Fourier lattice is Z^3, not C3^3.  It keeps k=2
-- as a distinct integer vector. This is a *one-axis finite illustration*.
nsPlusOneX : NSFourier.FourierMode
nsPlusOneX = NSFourier.mode (+ 1) (+ 0) (+ 0)

nsExactPlusPlusIsPlusTwoX :
  NSFourier.addMode nsPlusOneX nsPlusOneX
    ≡ NSFourier.mode (+ 2) (+ 0) (+ 0)
nsExactPlusPlusIsPlusTwoX = refl

-- Existing NS-369 physical orientation and Gram owners remain original.
-- They require actual complex vector, Leray, helicity, weighted-kernel and
-- Rayleigh estimates, none supplied by this finite frequency codec.
ns369BeltramiCrossIsAlreadySourceOwned :
  NS369.nsBeltramiCrossSuppressionReused ≡ true
ns369BeltramiCrossIsAlreadySourceOwned =
  NS369.nsBeltramiCrossSuppressionReusedIsTrue

nsGramIsNotPromotedByThreeModeAliasing :
  Gram.theoremPromoted Gram.canonicalNSTriadKN369HighHighGramBridgeReceipt
    ≡ false
nsGramIsNotPromotedByThreeModeAliasing =
  Gram.theoremPromotedIsFalse
    Gram.canonicalNSTriadKN369HighHighGramBridgeReceipt

nsLESProxyDoesNotSolveNS :
  LESOp.DASHILESClaimBoundary.navierStokesSolved LES.canonicalDASHILESClaimBoundary ≡ false
nsLESProxyDoesNotSolveNS = refl

-- In the Ma 2026 optical lattice Fourier supercell, ±11 and ±18 are
-- absent from a three-mode {-1,0,+1} window. This is a DIFFERENT cause
-- of truncation loss from quadratic NS aliasing (+1)+(+1)->+2.
maThreeModeSourceSidebandsAreOutOfWindow :
  (a b : Optical.ThreePlaneWaveMode) →
  Optical.MaS6Sideband (Optical.modeSeparation a b) → ⊥
maThreeModeSourceSidebandsAreOutOfWindow =
  Optical.noMaS6SidebandInThreeModeFourierTruncation

record ThreeModeCodecNSAuthority : Set where
  field
    sourceDescription : String
    binaryTernaryCodecLabelsAreLossless : Bool
    codecLabelsLosslessIsTrue :
      binaryTernaryCodecLabelsAreLossless ≡ true
    quadraticThreePointFourierAliasingOccurs : Bool
    finiteAliasingOccursIsTrue :
      quadraticThreePointFourierAliasingOccurs ≡ true
    codecRoundTripProvesQuadraticAliasFree : Bool
    codecRoundTripDoesNotProveAliasFree :
      codecRoundTripProvesQuadraticAliasFree ≡ false
    fullNavierStokesNonlinearityRealised : Bool
    fullNSNonlinearityRealisedIsFalse :
      fullNavierStokesNonlinearityRealised ≡ false
    maSourceAAHamiltonianIdentifiedWithNS : Bool
    maAndNSRemainSeparate :
      maSourceAAHamiltonianIdentifiedWithNS ≡ false
    nsClayRegularityProved : Bool
    nsClayRegularityProvedIsFalse : nsClayRegularityProved ≡ false
    r2p2GravityFromTriadicAliasing : Bool
    r2p2GravityFromTriadicAliasingIsFalse :
      r2p2GravityFromTriadicAliasing ≡ false
    remainingProducerRequirements : List String

open ThreeModeCodecNSAuthority public

canonicalThreeModeCodecNSAuthority : ThreeModeCodecNSAuthority
canonicalThreeModeCodecNSAuthority = record
  { sourceDescription =
      "Orszag/Patterson pseudo-spectral aliasing, Lambert et al 2026, original DASHI binary/ternary and NS owners"
  ; binaryTernaryCodecLabelsAreLossless = true
  ; codecLabelsLosslessIsTrue = refl
  ; quadraticThreePointFourierAliasingOccurs = true
  ; finiteAliasingOccursIsTrue = refl
  ; codecRoundTripProvesQuadraticAliasFree = false
  ; codecRoundTripDoesNotProveAliasFree = refl
  ; fullNavierStokesNonlinearityRealised = false
  ; fullNSNonlinearityRealisedIsFalse = refl
  ; maSourceAAHamiltonianIdentifiedWithNS = false
  ; maAndNSRemainSeparate = refl
  ; nsClayRegularityProved = false
  ; nsClayRegularityProvedIsFalse = refl
  ; r2p2GravityFromTriadicAliasing = false
  ; r2p2GravityFromTriadicAliasingIsFalse = refl
  ; remainingProducerRequirements =
      "selected NS Fourier coefficients, exact triad sums and cutoff geometry"
      ∷ "quadratic convolution output/support and alias-free projection/phase shift"
      ∷ "complex3 Leray, helicity, physical units and time-evolution closure"
      ∷ "uniform-in-cutoff analytic estimates or independent numerical error bounds"
      ∷ "separate Ma 87Sr optical lattice and R2P2 Yb measurement authorities"
      ∷ []
  }

threeModeCodecIsNotAnNSProof :
  nsClayRegularityProved canonicalThreeModeCodecNSAuthority ≡ false
threeModeCodecIsNotAnNSProof =
  nsClayRegularityProvedIsFalse canonicalThreeModeCodecNSAuthority
