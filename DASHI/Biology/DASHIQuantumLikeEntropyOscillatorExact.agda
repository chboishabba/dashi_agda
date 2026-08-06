module DASHI.Biology.DASHIQuantumLikeEntropyOscillatorExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as Hyper
import DASHI.Biology.SpectralGrokkingLatticeExact as Spectral

------------------------------------------------------------------------
-- Exact state-count and binary-capacity audit.

binaryCapacity : Nat → Nat
binaryCapacity n = Hyper.powNat 2 n

ternaryNineStateCount : Nat
ternaryNineStateCount = Hyper.ternaryLatticeCount 9

binaryCapacityFourteen : Nat
binaryCapacityFourteen = binaryCapacity 14

binaryCapacityFifteen : Nat
binaryCapacityFifteen = binaryCapacity 15

binaryCapacityFourteenIs16384 : binaryCapacityFourteen ≡ 16384
binaryCapacityFourteenIs16384 = refl

binaryCapacityFifteenIs32768 : binaryCapacityFifteen ≡ 32768
binaryCapacityFifteenIs32768 = refl

leqNat : Nat → Nat → Bool
leqNat zero n = true
leqNat (suc m) zero = false
leqNat (suc m) (suc n) = leqNat m n

fourteenBitsDoNotCoverTernaryNineSheet :
  leqNat ternaryNineStateCount binaryCapacityFourteen ≡ false
fourteenBitsDoNotCoverTernaryNineSheet = refl

fifteenBitsCoverTernaryNineSheet :
  leqNat ternaryNineStateCount binaryCapacityFifteen ≡ true
fifteenBitsCoverTernaryNineSheet = refl

------------------------------------------------------------------------
-- Finite mixing profile.  Stabilization means arrival at a stationary
-- distribution on the accessible carrier, not a quantum phase transition.

record ThreeStateDistribution : Set where
  constructor threeStateDistribution
  field
    negativeMass : Nat
    zeroMass : Nat
    positiveMass : Nat

open ThreeStateDistribution public

uniformThreeDistribution : ThreeStateDistribution
uniformThreeDistribution = threeStateDistribution 1 1 1

mixStep : ThreeStateDistribution → ThreeStateDistribution
mixStep distribution = uniformThreeDistribution

mixingStabilizesAfterOneStep :
  (distribution : ThreeStateDistribution) →
  mixStep (mixStep distribution) ≡ mixStep distribution
mixingStabilizesAfterOneStep distribution = refl

data EntropyLevel : Set where
  concentratedEntropy : EntropyLevel
  partialEntropy : EntropyLevel
  maximalThreeStateEntropy : EntropyLevel

entropyClass : ThreeStateDistribution → EntropyLevel
entropyClass (threeStateDistribution 1 1 1) = maximalThreeStateEntropy
entropyClass distribution = partialEntropy

mixedDistributionHasMaximalThreeStateEntropyClass :
  (distribution : ThreeStateDistribution) →
  entropyClass (mixStep distribution) ≡ maximalThreeStateEntropy
mixedDistributionHasMaximalThreeStateEntropyClass distribution = refl

------------------------------------------------------------------------
-- Discrete Laplacian-plus-potential oscillator.

data DiscreteOscillatorMode : Set where
  groundMode : DiscreteOscillatorMode
  firstOddMode : DiscreteOscillatorMode
  secondEvenMode : DiscreteOscillatorMode

laplacianContribution : DiscreteOscillatorMode → Nat
laplacianContribution groundMode = 0
laplacianContribution firstOddMode = 3
laplacianContribution secondEvenMode = 3

potentialContribution : DiscreteOscillatorMode → Nat
potentialContribution groundMode = 0
potentialContribution firstOddMode = 1
potentialContribution secondEvenMode = 3

oscillatorEnergy : DiscreteOscillatorMode → Nat
oscillatorEnergy mode =
  laplacianContribution mode + potentialContribution mode

oscillatorGroundEnergy : oscillatorEnergy groundMode ≡ 0
oscillatorGroundEnergy = refl

oscillatorFirstEnergy : oscillatorEnergy firstOddMode ≡ 4
oscillatorFirstEnergy = refl

oscillatorSecondEnergy : oscillatorEnergy secondEvenMode ≡ 6
oscillatorSecondEnergy = refl

modeDegeneracyComesFromLaplacianBeforePotential :
  laplacianContribution firstOddMode
  ≡ laplacianContribution secondEvenMode
modeDegeneracyComesFromLaplacianBeforePotential = refl

------------------------------------------------------------------------
-- Correlation claims require a declared embedding/order and null model.

record CorrelationProtocol : Set where
  constructor correlationProtocol
  field
    fixedEncodingBeforeObservation : Bool
    metricDeclared : Bool
    alternativesCounted : Bool
    nullDistributionDeclared : Bool
    heldOutReplication : Bool

open CorrelationProtocol public

incompleteOscillatorCorrelationProtocol : CorrelationProtocol
incompleteOscillatorCorrelationProtocol =
  correlationProtocol false false false false false

record DASHIQuantumLikeBoundary : Set where
  constructor dashiQuantumLikeBoundary
  field
    entropyStabilizationIsQuantumCondensation : Bool
    entropyStabilizationIsQuantumCondensationIsFalse :
      entropyStabilizationIsQuantumCondensation ≡ false

    LaplacianPlusPotentialIsPhysicalQuantization : Bool
    LaplacianPlusPotentialIsPhysicalQuantizationIsFalse :
      LaplacianPlusPotentialIsPhysicalQuantization ≡ false

    stateOrderingCanBeChosenAfterSeeingCorrelation : Bool
    stateOrderingCanBeChosenAfterSeeingCorrelationIsFalse :
      stateOrderingCanBeChosenAfterSeeingCorrelation ≡ false

    symmetryReducedEntropyCeilingsRemainMeaningful : Bool
    symmetryReducedEntropyCeilingsRemainMeaningfulIsTrue :
      symmetryReducedEntropyCeilingsRemainMeaningful ≡ true

open DASHIQuantumLikeBoundary public

canonicalDASHIQuantumLikeBoundary : DASHIQuantumLikeBoundary
canonicalDASHIQuantumLikeBoundary =
  dashiQuantumLikeBoundary false refl false refl false refl true refl
