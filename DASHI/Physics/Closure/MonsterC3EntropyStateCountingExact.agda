module DASHI.Physics.Closure.MonsterC3EntropyStateCountingExact where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster3BBalancedRegularFibreExact as Monster3B
import DASHI.Moonshine.MonsterC3ResidualTernaryArithmeticExact as Arithmetic

------------------------------------------------------------------------
-- State-counting consumer for the exact Monster 3B C3 fibre.
--
-- This module does not identify representation multiplicity with physical
-- thermodynamic entropy.  It exposes the finite count and the coarse C3
-- observation separately so downstream entropy models can consume them with
-- an explicit probability / density / physical-identification adapter.
------------------------------------------------------------------------

data EntropyObservableKind : Set where
  finiteStateCount : EntropyObservableKind
  shannonEntropyTarget : EntropyObservableKind
  vonNeumannEntropyTarget : EntropyObservableKind
  relativeEntropyTarget : EntropyObservableKind
  localEntropyDensityTarget : EntropyObservableKind
  boundaryAreaEntropyTarget : EntropyObservableKind

record MonsterC3StateCountingReceipt : Set where
  constructor monsterC3StateCountingReceipt
  field
    residualStates : Nat
    regularCopiesPerPhase : Nat
    c3PhaseCount : Nat
    identityVisibleStates : Nat
    nontrivialPhaseVisibleStates : Nat
    regularFibreNontrivialContribution : Nat
    conformalIdentityVisibleStates : Nat
    conformalNontrivialVisibleStates : Nat

    identityCountMatchesCertifiedMonsterDegree :
      identityVisibleStates ≡ Monster3B.identityEvaluation
        Monster3B.monster3BResidualRegularCarrier

    nontrivialCountMatchesCertifiedResidual :
      nontrivialPhaseVisibleStates ≡ Monster3B.nontrivialPhaseEvaluation
        Monster3B.monster3BResidualRegularCarrier

    balancedRegularCancellationMatchesCertifiedOwner :
      regularFibreNontrivialContribution ≡
        Monster3B.balancedRegularFibreNontrivialContribution
          Monster3B.monster3BResidualRegularCarrier

    arithmeticResidualCoordinateMatches :
      residualStates ≡ Arithmetic.residual53FromTernaryNeighbour

open MonsterC3StateCountingReceipt public

canonicalMonsterC3StateCountingReceipt : MonsterC3StateCountingReceipt
canonicalMonsterC3StateCountingReceipt =
  monsterC3StateCountingReceipt
    53
    65610
    3
    196883
    53
    0
    196884
    54
    refl
    refl
    refl
    refl

record StateCountingEntropyBridge : Set₁ where
  constructor stateCountingEntropyBridge
  field
    Microstate : Set
    CoarseObservation : Set
    ProbabilityWeight : Microstate → Set
    Region : Set
    VolumeOrAreaMeasure : Region → Set
    DensityMatrix : Set
    ReferenceState : Set

    finiteCount : CoarseObservation → Nat
    shannonEntropy : Set
    vonNeumannEntropy : Set
    relativeEntropy : Set
    localEntropyDensity : Set
    boundaryAreaEntropy : Set

    countToProbabilityIdentification : Set
    probabilityNormalization : Set
    densityMatrixPhysicalIdentification : Set
    regionMeasureIdentification : Set
    thermodynamicIdentification : Set

record StateCountingEntropyBoundary : Set where
  constructor stateCountingEntropyBoundary
  field
    degeneracyDeterminesProbabilityDistribution : Bool
    degeneracyDeterminesProbabilityDistributionIsFalse :
      degeneracyDeterminesProbabilityDistribution ≡ false

    stateCountIsThermodynamicEntropyWithoutModel : Bool
    stateCountIsThermodynamicEntropyWithoutModelIsFalse :
      stateCountIsThermodynamicEntropyWithoutModel ≡ false

    stateCountDeterminesVonNeumannEntropy : Bool
    stateCountDeterminesVonNeumannEntropyIsFalse :
      stateCountDeterminesVonNeumannEntropy ≡ false

    entropyDeterminesEntropyDensityWithoutMeasure : Bool
    entropyDeterminesEntropyDensityWithoutMeasureIsFalse :
      entropyDeterminesEntropyDensityWithoutMeasure ≡ false

    volumeEntropyDensityEqualsBoundaryAreaEntropy : Bool
    volumeEntropyDensityEqualsBoundaryAreaEntropyIsFalse :
      volumeEntropyDensityEqualsBoundaryAreaEntropy ≡ false

    balancedCharacterCancellationMeansFineStatesAbsent : Bool
    balancedCharacterCancellationMeansFineStatesAbsentIsFalse :
      balancedCharacterCancellationMeansFineStatesAbsent ≡ false

    coarseCancellationPreservesFineStateCount : Bool
    coarseCancellationPreservesFineStateCountIsTrue :
      coarseCancellationPreservesFineStateCount ≡ true

canonicalStateCountingEntropyBoundary : StateCountingEntropyBoundary
canonicalStateCountingEntropyBoundary =
  stateCountingEntropyBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Useful exact observations for downstream cross-pollination.
------------------------------------------------------------------------

identityVisibleStatesIs196883 :
  identityVisibleStates canonicalMonsterC3StateCountingReceipt ≡ 196883
identityVisibleStatesIs196883 = refl

nontrivialPhaseVisibleStatesIs53 :
  nontrivialPhaseVisibleStates canonicalMonsterC3StateCountingReceipt ≡ 53
nontrivialPhaseVisibleStatesIs53 = refl

conformalNontrivialVisibleStatesIs54 :
  conformalNontrivialVisibleStates canonicalMonsterC3StateCountingReceipt ≡ 54
conformalNontrivialVisibleStatesIs54 = refl

regularC3FineStates : Nat
regularC3FineStates = 3 * 65610

regularC3FineStatesIs196830 : regularC3FineStates ≡ 196830
regularC3FineStatesIs196830 = refl

finePlusResidualIsMonsterDegree :
  regularC3FineStates + 53 ≡ 196883
finePlusResidualIsMonsterDegree = refl
