module DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

Not : Set → Set
Not proposition = proposition → ⊥

------------------------------------------------------------------------
-- P5 limit closure.
--
-- K. Osterwalder and R. Schrader,
-- "Axioms for Euclidean Green's functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738
--
-- K. Osterwalder and R. Schrader,
-- "Axioms for Euclidean Green's functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
--
-- Every property below is transported through an actual sequential-closedness
-- theorem.  For reflection positivity, however, the abstract field
-- `reflectionPositiveClosed` is not accepted as a physical producer by itself.
-- It must be instantiated by convergence of complete reflected Gram quadratic
-- forms, as implemented in BalabanClayT5OSGramTopologyExact and
-- BalabanClayT5OSGramClosedPropertyExact.  Pointwise convergence of individual
-- correlators is deliberately insufficient.
------------------------------------------------------------------------

record SequentialLimit (Object : Set) : Set₁ where
  field
    limit : (Nat → Object) → Object
    Converges : (Nat → Object) → Object → Set
    sequenceConvergesToLimit : ∀ sequence → Converges sequence (limit sequence)

open SequentialLimit public

record SequentiallyClosedProperty (Object : Set)
    (Property : Object → Set) : Set₁ where
  field
    limits : SequentialLimit Object
    closedUnderLimit : ∀ sequence target →
      Converges limits sequence target →
      (∀ depth → Property (sequence depth)) →
      Property target

open SequentiallyClosedProperty public

propertyAtConstructedLimit :
  ∀ {Object} {Property : Object → Set}
    (closed : SequentiallyClosedProperty Object Property)
    sequence →
  (∀ depth → Property (sequence depth)) →
  Property (limit (limits closed) sequence)
propertyAtConstructedLimit closed sequence pointwise =
  closedUnderLimit closed sequence (limit (limits closed) sequence)
    (sequenceConvergesToLimit (limits closed) sequence)
    pointwise

record FiniteToContinuumOSClosure (Measure Schwinger : Set) : Set₁ where
  field
    finiteMeasures : Nat → Measure
    continuumMeasure : Measure
    schwinger : Measure → Schwinger

    measureLimit : SequentialLimit Measure
    continuumIsLimit :
      Converges measureLimit finiteMeasures continuumMeasure

    Normalized Positive GaugeInvariant ReflectionPositiveMeasure : Measure → Set
    EuclideanCovariant ReflectionPositive Symmetric Tempered Regular Clustered :
      Schwinger → Set

    finiteNormalized : ∀ depth → Normalized (finiteMeasures depth)
    finitePositive : ∀ depth → Positive (finiteMeasures depth)
    finiteGaugeInvariant : ∀ depth → GaugeInvariant (finiteMeasures depth)
    finiteReflectionPositive : ∀ depth →
      ReflectionPositiveMeasure (finiteMeasures depth)

    normalizedClosed : ∀ sequence target →
      Converges measureLimit sequence target →
      (∀ depth → Normalized (sequence depth)) → Normalized target
    positiveClosed : ∀ sequence target →
      Converges measureLimit sequence target →
      (∀ depth → Positive (sequence depth)) → Positive target
    gaugeInvariantClosed : ∀ sequence target →
      Converges measureLimit sequence target →
      (∀ depth → GaugeInvariant (sequence depth)) → GaugeInvariant target
    reflectionPositiveClosed : ∀ sequence target →
      Converges measureLimit sequence target →
      (∀ depth → ReflectionPositiveMeasure (sequence depth)) →
      ReflectionPositiveMeasure target

    continuumEuclideanCovariant : EuclideanCovariant (schwinger continuumMeasure)
    continuumSymmetric : Symmetric (schwinger continuumMeasure)
    continuumTempered : Tempered (schwinger continuumMeasure)
    continuumRegular : Regular (schwinger continuumMeasure)
    continuumClustered : Clustered (schwinger continuumMeasure)

    measureReflectionImpliesSchwingerReflection : ∀ measure →
      ReflectionPositiveMeasure measure →
      ReflectionPositive (schwinger measure)

open FiniteToContinuumOSClosure public

continuumNormalized :
  ∀ {Measure Schwinger} →
  (dataSet : FiniteToContinuumOSClosure Measure Schwinger) →
  Normalized dataSet (continuumMeasure dataSet)
continuumNormalized dataSet =
  normalizedClosed dataSet
    (finiteMeasures dataSet) (continuumMeasure dataSet)
    (continuumIsLimit dataSet) (finiteNormalized dataSet)

continuumPositive :
  ∀ {Measure Schwinger} →
  (dataSet : FiniteToContinuumOSClosure Measure Schwinger) →
  Positive dataSet (continuumMeasure dataSet)
continuumPositive dataSet =
  positiveClosed dataSet
    (finiteMeasures dataSet) (continuumMeasure dataSet)
    (continuumIsLimit dataSet) (finitePositive dataSet)

continuumGaugeInvariant :
  ∀ {Measure Schwinger} →
  (dataSet : FiniteToContinuumOSClosure Measure Schwinger) →
  GaugeInvariant dataSet (continuumMeasure dataSet)
continuumGaugeInvariant dataSet =
  gaugeInvariantClosed dataSet
    (finiteMeasures dataSet) (continuumMeasure dataSet)
    (continuumIsLimit dataSet) (finiteGaugeInvariant dataSet)

continuumReflectionPositive :
  ∀ {Measure Schwinger} →
  (dataSet : FiniteToContinuumOSClosure Measure Schwinger) →
  ReflectionPositive dataSet (schwinger dataSet (continuumMeasure dataSet))
continuumReflectionPositive dataSet =
  measureReflectionImpliesSchwingerReflection dataSet
    (continuumMeasure dataSet)
    (reflectionPositiveClosed dataSet
      (finiteMeasures dataSet) (continuumMeasure dataSet)
      (continuumIsLimit dataSet) (finiteReflectionPositive dataSet))

------------------------------------------------------------------------
-- Nontriviality: a nonzero connected fourth cumulant is incompatible with a
-- generalized Gaussian continuum field.
------------------------------------------------------------------------

record FourthCumulantWitness (Measure Observable Value : Set) : Set₁ where
  field
    fourthConnectedCumulant : Measure → Observable → Value
    witnessObservable : Observable
    zero : Value
    continuumMeasure : Measure

    Nonzero : Value → Set
    cumulantNonzero :
      Nonzero (fourthConnectedCumulant continuumMeasure witnessObservable)

    GeneralizedGaussian : Measure → Set
    gaussianFourthCumulantVanishes : ∀ measure →
      GeneralizedGaussian measure →
      fourthConnectedCumulant measure witnessObservable ≡ zero

    nonzeroContradictsZero : ∀ value →
      Nonzero value → value ≡ zero → ⊥

open FourthCumulantWitness public

nonzeroFourthCumulantExcludesGaussian :
  ∀ {Measure Observable Value}
    (dataSet : FourthCumulantWitness Measure Observable Value) →
  Not (GeneralizedGaussian dataSet (continuumMeasure dataSet))
nonzeroFourthCumulantExcludesGaussian dataSet gaussian =
  nonzeroContradictsZero dataSet
    (fourthConnectedCumulant dataSet
      (continuumMeasure dataSet) (witnessObservable dataSet))
    (cumulantNonzero dataSet)
    (gaussianFourthCumulantVanishes dataSet
      (continuumMeasure dataSet) gaussian)

finiteToContinuumPositivityClosureLevel : ProofLevel
finiteToContinuumPositivityClosureLevel = machineChecked

continuumOSPropertyTransportLevel : ProofLevel
continuumOSPropertyTransportLevel = machineChecked

osClosureRequiresGramTopologyLevel : ProofLevel
osClosureRequiresGramTopologyLevel = machineChecked

fourthCumulantNontrivialityLevel : ProofLevel
fourthCumulantNontrivialityLevel = machineChecked

-- Tightness, uniqueness of the thermodynamic/continuum limits, restoration of
-- Euclidean covariance, Gram-topology convergence and a uniform nonzero
-- fourth-cumulant lower bound remain the literal analytic producers.
physicalLimitTightnessAndNontrivialityLevel : ProofLevel
physicalLimitTightnessAndNontrivialityLevel = conditional
