module DASHI.Physics.Foundations.ScaleInvariantTheorySelectionExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TernaryHypercubeHyperfabricExact as ExistingHyperfabric

------------------------------------------------------------------------
-- Finite Buckingham-style dimension kernel.
--
-- A physical dimension is represented as a fraction of nonnegative exponent
-- vectors.  Two quantities have the same dimension when cross-multiplication
-- of their numerator/denominator vectors agrees.  This permits exact negative
-- powers without importing a numerical value for any physical scale.

record DimensionVector : Set where
  constructor dimensionVector
  field
    lengthPower : Nat
    timePower : Nat
    massPower : Nat

open DimensionVector public

_⊕dim_ : DimensionVector → DimensionVector → DimensionVector
dimensionVector l₁ t₁ m₁ ⊕dim dimensionVector l₂ t₂ m₂ =
  dimensionVector (l₁ + l₂) (t₁ + t₂) (m₁ + m₂)

zeroDimension : DimensionVector
zeroDimension = dimensionVector 0 0 0

lengthDimension : DimensionVector
lengthDimension = dimensionVector 1 0 0

timeDimension : DimensionVector
timeDimension = dimensionVector 0 1 0

record QuantityDimension : Set where
  constructor quantityDimension
  field
    numeratorDimension : DimensionVector
    denominatorDimension : DimensionVector

open QuantityDimension public

multiplyDimension : QuantityDimension → QuantityDimension → QuantityDimension
multiplyDimension x y =
  quantityDimension
    (numeratorDimension x ⊕dim numeratorDimension y)
    (denominatorDimension x ⊕dim denominatorDimension y)

sameDimension : QuantityDimension → QuantityDimension → Set
sameDimension x y =
  numeratorDimension x ⊕dim denominatorDimension y
  ≡
  numeratorDimension y ⊕dim denominatorDimension x

lengthQuantityDimension : QuantityDimension
lengthQuantityDimension =
  quantityDimension lengthDimension zeroDimension

timeQuantityDimension : QuantityDimension
timeQuantityDimension =
  quantityDimension timeDimension zeroDimension

speedQuantityDimension : QuantityDimension
speedQuantityDimension =
  quantityDimension lengthDimension timeDimension

speedTimesTimeHasLengthDimension :
  sameDimension
    (multiplyDimension speedQuantityDimension timeQuantityDimension)
    lengthQuantityDimension
speedTimesTimeHasLengthDimension = refl

record DimensionlessRatioWitness : Set where
  constructor dimensionlessRatioWitness
  field
    numeratorQuantity : QuantityDimension
    denominatorQuantity : QuantityDimension
    dimensionsCancel : sameDimension numeratorQuantity denominatorQuantity

open DimensionlessRatioWitness public

speedTimeOverLength : DimensionlessRatioWitness
speedTimeOverLength =
  dimensionlessRatioWitness
    (multiplyDimension speedQuantityDimension timeQuantityDimension)
    lengthQuantityDimension
    refl

------------------------------------------------------------------------
-- Spontaneous scale breaking: the laws preserve a scale orbit, while a chosen
-- vacuum selects one representative.  The equations alone do not choose it.

data ScaleVacuum : Set where
  vacuumUnit : ScaleVacuum
  vacuumTriple : ScaleVacuum

data ScaleAction : Set where
  identityScaleAction : ScaleAction
  tripleScaleAction : ScaleAction

actOnVacuum : ScaleAction → ScaleVacuum → ScaleVacuum
actOnVacuum identityScaleAction vacuum = vacuum
actOnVacuum tripleScaleAction vacuumUnit = vacuumTriple
actOnVacuum tripleScaleAction vacuumTriple = vacuumUnit

scaleLawEnergy : ScaleVacuum → Nat
scaleLawEnergy vacuumUnit = 0
scaleLawEnergy vacuumTriple = 0

lawIsDegenerateAcrossScaleOrbit :
  scaleLawEnergy vacuumUnit ≡ scaleLawEnergy vacuumTriple
lawIsDegenerateAcrossScaleOrbit = refl

record ChosenVacuum : Set where
  constructor chosenVacuum
  field
    selectedVacuum : ScaleVacuum

canonicalChosenVacuum : ChosenVacuum
canonicalChosenVacuum = chosenVacuum vacuumUnit

------------------------------------------------------------------------
-- Discrete depth quantises relative scales while retaining a base calibration.

data TriadicDepth : Set where
  depth0 : TriadicDepth
  depth1 : TriadicDepth
  depth2 : TriadicDepth
  depth3 : TriadicDepth

scaleAtDepth : Nat → TriadicDepth → Nat
scaleAtDepth base depth0 = 27 * base
scaleAtDepth base depth1 = 9 * base
scaleAtDepth base depth2 = 3 * base
scaleAtDepth base depth3 = base

depthZeroIsTripleDepthOne :
  scaleAtDepth 1 depth0 ≡ 3 * scaleAtDepth 1 depth1
depthZeroIsTripleDepthOne = refl

depthOneIsTripleDepthTwo :
  scaleAtDepth 1 depth1 ≡ 3 * scaleAtDepth 1 depth2
depthOneIsTripleDepthTwo = refl

depthTwoIsTripleDepthThree :
  scaleAtDepth 1 depth2 ≡ 3 * scaleAtDepth 1 depth3
depthTwoIsTripleDepthThree = refl

baseCalibrationChangesEveryAbsoluteScale :
  scaleAtDepth 1 depth2 ≡ 3
  ×
  scaleAtDepth 2 depth2 ≡ 6
baseCalibrationChangesEveryAbsoluteScale = refl , refl

existingTriadicScaleCarrier : Set
existingTriadicScaleCarrier = ExistingHyperfabric.CarrierScale

------------------------------------------------------------------------
-- Global MDL/Bayesian theory selection over a declared finite candidate class.

data UniverseCandidate : Set where
  compactUniverse : UniverseCandidate
  flexibleUniverse : UniverseCandidate
  overfitUniverse : UniverseCandidate

lawCodeLength : UniverseCandidate → Nat
lawCodeLength compactUniverse = 2
lawCodeLength flexibleUniverse = 4
lawCodeLength overfitUniverse = 7

data ObservationDataset : Set where
  canonicalDataset : ObservationDataset

dataLikelihoodPenalty : UniverseCandidate → ObservationDataset → Nat
dataLikelihoodPenalty compactUniverse canonicalDataset = 4
dataLikelihoodPenalty flexibleUniverse canonicalDataset = 1
dataLikelihoodPenalty overfitUniverse canonicalDataset = 0

posteriorDescriptionScore : UniverseCandidate → ObservationDataset → Nat
posteriorDescriptionScore universe dataset =
  lawCodeLength universe + dataLikelihoodPenalty universe dataset

compactPosteriorScoreIsSix :
  posteriorDescriptionScore compactUniverse canonicalDataset ≡ 6
compactPosteriorScoreIsSix = refl

flexiblePosteriorScoreIsFive :
  posteriorDescriptionScore flexibleUniverse canonicalDataset ≡ 5
flexiblePosteriorScoreIsFive = refl

overfitPosteriorScoreIsSeven :
  posteriorDescriptionScore overfitUniverse canonicalDataset ≡ 7
overfitPosteriorScoreIsSeven = refl

selectedUniverse : UniverseCandidate
selectedUniverse = flexibleUniverse

selectedUniverseScoreIsFive :
  posteriorDescriptionScore selectedUniverse canonicalDataset ≡ 5
selectedUniverseScoreIsFive = refl

------------------------------------------------------------------------
-- Universal-machine dependence is bounded only after a relation between code
-- systems is supplied.  The finite example exposes the additive offset.

data ReferenceMachine : Set where
  machineA : ReferenceMachine
  machineB : ReferenceMachine

machineOffset : ReferenceMachine → Nat
machineOffset machineA = 0
machineOffset machineB = 3

machineCodeLength : ReferenceMachine → UniverseCandidate → Nat
machineCodeLength machine universe =
  machineOffset machine + lawCodeLength universe

machineBAddsThreeToCompactLaw :
  machineCodeLength machineB compactUniverse ≡ 5
machineBAddsThreeToCompactLaw = refl

------------------------------------------------------------------------
-- Finite joint parameter flow: RG drift, variational selection, and resource
-- exhaustion can terminate in different stationary classes.

data JointParameterState : Set where
  selectionDominatedState : JointParameterState
  rgFixedState : JointParameterState
  balancedState : JointParameterState
  frozenNonEquilibriumState : JointParameterState

data ResourceRegime : Set where
  activeResource : ResourceRegime
  exhaustedResource : ResourceRegime

jointFlowStep : ResourceRegime → JointParameterState → JointParameterState
jointFlowStep activeResource selectionDominatedState = balancedState
jointFlowStep activeResource rgFixedState = rgFixedState
jointFlowStep activeResource balancedState = balancedState
jointFlowStep activeResource frozenNonEquilibriumState = balancedState
jointFlowStep exhaustedResource state = frozenNonEquilibriumState

activeSelectionCanReachBalancedState :
  jointFlowStep activeResource selectionDominatedState ≡ balancedState
activeSelectionCanReachBalancedState = refl

exhaustionFreezesReachedValue :
  jointFlowStep exhaustedResource balancedState ≡ frozenNonEquilibriumState
exhaustionFreezesReachedValue = refl

record ScaleInvariantTheorySelectionBoundary : Set where
  constructor scaleInvariantTheorySelectionBoundary
  field
    dimensionMatrixKernelDeterminesPhysicalCoefficient : Bool
    dimensionMatrixKernelDeterminesPhysicalCoefficientIsFalse :
      dimensionMatrixKernelDeterminesPhysicalCoefficient ≡ false

    spontaneousScaleBreakingSelectsVacuumWithoutStateData : Bool
    spontaneousScaleBreakingSelectsVacuumWithoutStateDataIsFalse :
      spontaneousScaleBreakingSelectsVacuumWithoutStateData ≡ false

    triadicDepthFixesAbsoluteBaseScale : Bool
    triadicDepthFixesAbsoluteBaseScaleIsFalse :
      triadicDepthFixesAbsoluteBaseScale ≡ false

    globalMDLIsACompleteCosmicLawWithoutCandidateClass : Bool
    globalMDLIsACompleteCosmicLawWithoutCandidateClassIsFalse :
      globalMDLIsACompleteCosmicLawWithoutCandidateClass ≡ false

    machineRelativeCodeLengthIsAbsolutelyCanonical : Bool
    machineRelativeCodeLengthIsAbsolutelyCanonicalIsFalse :
      machineRelativeCodeLengthIsAbsolutelyCanonical ≡ false

    frozenJointValueIsNecessarilyUniversal : Bool
    frozenJointValueIsNecessarilyUniversalIsFalse :
      frozenJointValueIsNecessarilyUniversal ≡ false

open ScaleInvariantTheorySelectionBoundary public

canonicalScaleInvariantTheorySelectionBoundary :
  ScaleInvariantTheorySelectionBoundary
canonicalScaleInvariantTheorySelectionBoundary =
  scaleInvariantTheorySelectionBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
