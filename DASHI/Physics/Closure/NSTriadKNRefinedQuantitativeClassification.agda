module DASHI.Physics.Closure.NSTriadKNRefinedQuantitativeClassification where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy as Scale
import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation

------------------------------------------------------------------------
-- The theorem-producing class records the quantitative mechanism, not merely
-- a human-facing FT/TRANS/ADV name.
------------------------------------------------------------------------

data LocalityRegime : Set where
  separatedLowHigh separatedHighLow comparableInputs highHighToLow :
    LocalityRegime

data AngularRegime : Set where
  angularGeneric angularSmall nearParallel nearAntiparallel : AngularRegime

data PolarisationRegime : Set where
  polarisationGeneric inputNullSuppressed outputOrthogonal
  helicalSelectionSuppressed : PolarisationRegime

data CancellationOrbit : Set where
  orderedSingleton swapPair realityPair completeTriadOrbit : CancellationOrbit

data MultiplicityRegime : Set where
  uniformlyBounded surfaceOrder volumeOrder : MultiplicityRegime

record RefinedStage3Class : Set where
  constructor refined-class
  field
    locality : LocalityRegime
    angular : AngularRegime
    polarisation : PolarisationRegime
    cancellation : CancellationOrbit
    multiplicity : MultiplicityRegime

open RefinedStage3Class public

coarseProjection : RefinedStage3Class → Allocation.Stage3Class
coarseProjection class with locality class
... | separatedLowHigh = Allocation.forcedTail
... | separatedHighLow = Allocation.forcedTail
... | comparableInputs = Allocation.transition
... | highHighToLow = Allocation.adversarial

scaleProjection : RefinedStage3Class → Scale.ScaleRegime
scaleProjection class with locality class
... | separatedLowHigh = Scale.lowHigh
... | separatedHighLow = Scale.highLow
... | comparableInputs = Scale.comparable
... | highHighToLow = Scale.highHigh

------------------------------------------------------------------------
-- Quantitative gains exposed by a class.
------------------------------------------------------------------------

data GainMechanism : Set where
  scaleRatioGain : Nat → GainMechanism
  angularDefectGain : Nat → GainMechanism
  polarisationNullGain : Nat → GainMechanism
  signedSwapCancellation : GainMechanism
  realityOrbitCancellation : GainMechanism
  completeTriadCancellation : GainMechanism
  boundedMultiplicityGain : Nat → GainMechanism
  modifiedEnergyCoercivity : GainMechanism

record RefinedClassificationPolicy {p : Level} (PhysicalIncidence : Set p) :
    Set (lsuc p) where
  field
    classifyLocality : PhysicalIncidence → LocalityRegime
    classifyAngular : PhysicalIncidence → AngularRegime
    classifyPolarisation : PhysicalIncidence → PolarisationRegime
    classifyCancellation : PhysicalIncidence → CancellationOrbit
    classifyMultiplicity : PhysicalIncidence → MultiplicityRegime

    gains : PhysicalIncidence → GainMechanism

    localityScaleSound :
      (τ : PhysicalIncidence) →
      Set

    angularDecisionSound :
      (τ : PhysicalIncidence) →
      Set

    polarisationDecisionSound :
      (τ : PhysicalIncidence) →
      Set

    cancellationOrbitComplete :
      (τ : PhysicalIncidence) →
      Set

    multiplicityClassificationSound :
      (τ : PhysicalIncidence) →
      Set

open RefinedClassificationPolicy public

classifyRefined :
  ∀ {p} {PhysicalIncidence : Set p} →
  RefinedClassificationPolicy PhysicalIncidence →
  PhysicalIncidence → RefinedStage3Class
classifyRefined policy τ = refined-class
  (classifyLocality policy τ)
  (classifyAngular policy τ)
  (classifyPolarisation policy τ)
  (classifyCancellation policy τ)
  (classifyMultiplicity policy τ)

record RefinedClassEstimate
    {p : Level}
    {PhysicalIncidence : Set p}
    (policy : RefinedClassificationPolicy PhysicalIncidence) : Set (lsuc p) where
  field
    Scalar : Set
    coefficientMagnitude envelope : PhysicalIncidence → Scalar
    _≤_ : Scalar → Scalar → Set

    estimateFromRecordedMechanism :
      (τ : PhysicalIncidence) →
      coefficientMagnitude τ ≤ envelope τ

    estimateUsesClass :
      (τ : PhysicalIncidence) →
      Set

    estimateUsesGain :
      (τ : PhysicalIncidence) →
      Set

open RefinedClassEstimate public

record DeterministicRefinedAllocation
    {p : Level}
    {PhysicalIncidence : Set p}
    (policy : RefinedClassificationPolicy PhysicalIncidence) : Set (lsuc p) where
  field
    allocatedClass : PhysicalIncidence → RefinedStage3Class
    allocatedClassComputed :
      (τ : PhysicalIncidence) →
      allocatedClass τ ≡ classifyRefined policy τ

    allocationEstimate : RefinedClassEstimate policy

open DeterministicRefinedAllocation public

refinedClassificationAxesImplemented : Bool
refinedClassificationAxesImplemented = true

refinedClassificationAxesImplementedIsTrue :
  refinedClassificationAxesImplemented ≡ true
refinedClassificationAxesImplementedIsTrue = refl

refinedClassesCarryGainMechanism : Bool
refinedClassesCarryGainMechanism = true

refinedClassesCarryGainMechanismIsTrue :
  refinedClassesCarryGainMechanism ≡ true
refinedClassesCarryGainMechanismIsTrue = refl

uniformRefinedEstimateInhabited : Bool
uniformRefinedEstimateInhabited = false

uniformRefinedEstimateInhabitedIsFalse :
  uniformRefinedEstimateInhabited ≡ false
uniformRefinedEstimateInhabitedIsFalse = refl
