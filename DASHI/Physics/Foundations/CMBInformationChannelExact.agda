module DASHI.Physics.Foundations.CMBInformationChannelExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite quantum/statistical channel analogue.

data EarlyDensityState : Set where
  earlyDensityA : EarlyDensityState
  earlyDensityB : EarlyDensityState
  earlyDensityC : EarlyDensityState

data CMBReducedState : Set where
  reducedSkyCommon : CMBReducedState
  reducedSkyDistinct : CMBReducedState

cmbChannel : EarlyDensityState → CMBReducedState
cmbChannel earlyDensityA = reducedSkyCommon
cmbChannel earlyDensityB = reducedSkyCommon
cmbChannel earlyDensityC = reducedSkyDistinct

channelIsNonInjective :
  cmbChannel earlyDensityA ≡ cmbChannel earlyDensityB
channelIsNonInjective = refl

data MeasurementOutcome : Set where
  coldOutcome : MeasurementOutcome
  hotOutcome : MeasurementOutcome

measurementWeight : CMBReducedState → MeasurementOutcome → Nat
measurementWeight reducedSkyCommon coldOutcome = 2
measurementWeight reducedSkyCommon hotOutcome = 2
measurementWeight reducedSkyDistinct coldOutcome = 1
measurementWeight reducedSkyDistinct hotOutcome = 3

commonSkyOutcomeWeightIsBalanced :
  measurementWeight reducedSkyCommon coldOutcome
  ≡
  measurementWeight reducedSkyCommon hotOutcome
commonSkyOutcomeWeightIsBalanced = refl

------------------------------------------------------------------------
-- Distinguishability cannot increase through this coarse channel in the finite
-- example.

earlyDistinguishability : EarlyDensityState → EarlyDensityState → Nat
earlyDistinguishability earlyDensityA earlyDensityA = 0
earlyDistinguishability earlyDensityB earlyDensityB = 0
earlyDistinguishability earlyDensityC earlyDensityC = 0
earlyDistinguishability earlyDensityA earlyDensityB = 2
earlyDistinguishability earlyDensityB earlyDensityA = 2
earlyDistinguishability earlyDensityA earlyDensityC = 3
earlyDistinguishability earlyDensityC earlyDensityA = 3
earlyDistinguishability earlyDensityB earlyDensityC = 3
earlyDistinguishability earlyDensityC earlyDensityB = 3

reducedDistinguishability : CMBReducedState → CMBReducedState → Nat
reducedDistinguishability reducedSkyCommon reducedSkyCommon = 0
reducedDistinguishability reducedSkyDistinct reducedSkyDistinct = 0
reducedDistinguishability reducedSkyCommon reducedSkyDistinct = 1
reducedDistinguishability reducedSkyDistinct reducedSkyCommon = 1

channelErasesABDistinguishability :
  earlyDistinguishability earlyDensityA earlyDensityB ≡ 2
  ×
  reducedDistinguishability
    (cmbChannel earlyDensityA)
    (cmbChannel earlyDensityB)
  ≡
  0
channelErasesABDistinguishability = refl , refl

------------------------------------------------------------------------
-- Coding factorisation and physical transition factorisation are homologous
-- but live in separate types.

data CodeState : Set where
  codeState0 : CodeState
  codeState1 : CodeState

data PhysicalState : Set where
  physicalState0 : PhysicalState
  physicalState1 : PhysicalState
  physicalState2 : PhysicalState

codeConditionalWeight : CodeState → CodeState → Nat
codeConditionalWeight codeState0 codeState0 = 3
codeConditionalWeight codeState0 codeState1 = 1
codeConditionalWeight codeState1 codeState0 = 1
codeConditionalWeight codeState1 codeState1 = 3

physicalTransitionWeight : PhysicalState → PhysicalState → Nat
physicalTransitionWeight physicalState0 physicalState0 = 2
physicalTransitionWeight physicalState0 physicalState1 = 2
physicalTransitionWeight physicalState0 physicalState2 = 0
physicalTransitionWeight physicalState1 physicalState0 = 1
physicalTransitionWeight physicalState1 physicalState1 = 2
physicalTransitionWeight physicalState1 physicalState2 = 1
physicalTransitionWeight physicalState2 physicalState0 = 0
physicalTransitionWeight physicalState2 physicalState1 = 1
physicalTransitionWeight physicalState2 physicalState2 = 3

record ForwardFactorisationWitness : Set where
  constructor forwardFactorisationWitness
  field
    initialWeight : Nat
    firstConditionalWeight : Nat
    secondConditionalWeight : Nat

open ForwardFactorisationWitness public

codeFactorisation : ForwardFactorisationWitness
codeFactorisation = forwardFactorisationWitness 1 3 1

physicalFactorisation : ForwardFactorisationWitness
physicalFactorisation = forwardFactorisationWitness 1 2 1

codeAndPhysicalFactorsAreNotDefinitionallyEqual :
  firstConditionalWeight codeFactorisation ≡ 3
  ×
  firstConditionalWeight physicalFactorisation ≡ 2
codeAndPhysicalFactorsAreNotDefinitionallyEqual = refl , refl

------------------------------------------------------------------------
-- Deterministic decoding and physical law types remain separate.

data DecoderLaw : Set where
  deterministicDecoder : DecoderLaw
  stochasticDecoder : DecoderLaw

data PhysicalLawKind : Set where
  deterministicPhysicalLaw : PhysicalLawKind
  stochasticPhysicalLaw : PhysicalLawKind
  quantumChannelLaw : PhysicalLawKind
  constraintHistoryLaw : PhysicalLawKind

record CMBInformationChannelBoundary : Set where
  constructor cmbInformationChannelBoundary
  field
    noninjectiveCMBChannelIsLossless : Bool
    noninjectiveCMBChannelIsLosslessIsFalse :
      noninjectiveCMBChannelIsLossless ≡ false

    deterministicDecoderForcesDeterministicPhysics : Bool
    deterministicDecoderForcesDeterministicPhysicsIsFalse :
      deterministicDecoderForcesDeterministicPhysics ≡ false

    matchingForwardFactorisationMakesCoderAndDynamicsIdentical : Bool
    matchingForwardFactorisationMakesCoderAndDynamicsIdenticalIsFalse :
      matchingForwardFactorisationMakesCoderAndDynamicsIdentical ≡ false

    finiteMeasurementWeightsAreACompletedPOVM : Bool
    finiteMeasurementWeightsAreACompletedPOVMIsFalse :
      finiteMeasurementWeightsAreACompletedPOVM ≡ false

open CMBInformationChannelBoundary public

canonicalCMBInformationChannelBoundary : CMBInformationChannelBoundary
canonicalCMBInformationChannelBoundary =
  cmbInformationChannelBoundary false refl false refl false refl false refl
