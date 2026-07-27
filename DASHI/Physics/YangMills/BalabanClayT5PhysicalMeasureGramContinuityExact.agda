module DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS

------------------------------------------------------------------------
-- Literature:
--
-- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738
--
-- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
--
-- P. Menotti and A. Pelissetto, "General proof of Osterwalder-Schrader
-- positivity for the Wilson action", Communications in Mathematical Physics
-- 113 (1987), 369--373. DOI: 10.1007/BF01221251
------------------------------------------------------------------------

record PhysicalPositiveTimeCylinderTest
    (Observable Scalar : Set) : Set₁ where
  constructor cylinderTest
  field
    observable : Observable
    coefficient : Scalar
    PositiveTimeSupported : Set
    GaugeInvariantObservable : Set

open PhysicalPositiveTimeCylinderTest public

record PhysicalOSFiniteTestFamily
    (Observable Scalar : Set) : Set₁ where
  constructor finiteTestFamily
  field
    tests : List (PhysicalPositiveTimeCylinderTest Observable Scalar)

open PhysicalOSFiniteTestFamily public

record PhysicalOSOperations
    (Measure Observable Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    conjugate : Scalar → Scalar
    reflectObservable : Observable → Observable
    multiplyObservable : Observable → Observable → Observable
    expectation : Measure → Observable → Scalar

open PhysicalOSOperations public

physicalReflectedGramEntry :
  ∀ {Measure Observable Scalar} →
  PhysicalOSOperations Measure Observable Scalar →
  Measure →
  PhysicalPositiveTimeCylinderTest Observable Scalar →
  PhysicalPositiveTimeCylinderTest Observable Scalar →
  Scalar
physicalReflectedGramEntry operations measure left right =
  multiply operations
    (multiply operations
      (conjugate operations (coefficient left))
      (coefficient right))
    (expectation operations measure
      (multiplyObservable operations
        (reflectObservable operations (observable left))
        (observable right)))

sumList :
  ∀ {A Scalar : Set} →
  (Scalar → Scalar → Scalar) → Scalar →
  List A → (A → Scalar) → Scalar
sumList add zero [] term = zero
sumList add zero (value ∷ values) term =
  add (term value) (sumList add zero values term)

physicalReflectedGramQuadraticForm :
  ∀ {Measure Observable Scalar} →
  PhysicalOSOperations Measure Observable Scalar →
  Measure → PhysicalOSFiniteTestFamily Observable Scalar → Scalar
physicalReflectedGramQuadraticForm operations measure family =
  sumList (add operations) (zero operations) (tests family)
    (λ left →
      sumList (add operations) (zero operations) (tests family)
        (λ right →
          physicalReflectedGramEntry operations measure left right))

reflectedGramQuadraticFormFiniteExpansion :
  ∀ {Measure Observable Scalar}
    (operations : PhysicalOSOperations Measure Observable Scalar)
    measure family →
  physicalReflectedGramQuadraticForm operations measure family
  ≡ sumList (add operations) (zero operations) (tests family)
      (λ left →
        sumList (add operations) (zero operations) (tests family)
          (λ right →
            physicalReflectedGramEntry operations measure left right))
reflectedGramQuadraticFormFiniteExpansion operations measure family = refl

record PhysicalReflectionCovariance
    (Cutoff Observable : Set) : Set₁ where
  field
    renormalize : Cutoff → Observable → Observable
    reflectObservable : Observable → Observable
    PositiveTimeSupported GaugeInvariantObservable : Observable → Set

    renormalizationCommutesWithReflection : ∀ cutoff observable →
      renormalize cutoff (reflectObservable observable)
      ≡ reflectObservable (renormalize cutoff observable)

    blockingPreservesPositiveTimeSupport : ∀ cutoff observable →
      PositiveTimeSupported observable →
      PositiveTimeSupported (renormalize cutoff observable)

    reflectionPreservesGaugeInvariantObservable : ∀ observable →
      GaugeInvariantObservable observable →
      GaugeInvariantObservable (reflectObservable observable)

open PhysicalReflectionCovariance public

record ScalarConvergenceAlgebra
    (Scalar : Set)
    (zeroValue : Scalar)
    (addValue multiplyValue : Scalar → Scalar → Scalar) : Set₁ where
  field
    Converges : (Nat → Scalar) → Scalar → Set
    constantConverges : ∀ value →
      Converges (λ cutoff → value) value
    addConverges : ∀ firstSequence firstLimit secondSequence secondLimit →
      Converges firstSequence firstLimit →
      Converges secondSequence secondLimit →
      Converges
        (λ cutoff → addValue (firstSequence cutoff) (secondSequence cutoff))
        (addValue firstLimit secondLimit)
    multiplyConstantConverges : ∀ coefficient sequence limit →
      Converges sequence limit →
      Converges
        (λ cutoff → multiplyValue coefficient (sequence cutoff))
        (multiplyValue coefficient limit)

open ScalarConvergenceAlgebra public

finiteSumCommutesWithLimit :
  ∀ {A Scalar}
    {zeroValue : Scalar}
    {addValue multiplyValue : Scalar → Scalar → Scalar}
    (algebra : ScalarConvergenceAlgebra
      Scalar zeroValue addValue multiplyValue)
    (values : List A)
    (sequence : A → Nat → Scalar)
    (limit : A → Scalar) →
  (∀ value → Converges algebra (sequence value) (limit value)) →
  Converges algebra
    (λ cutoff →
      sumList addValue zeroValue values
        (λ value → sequence value cutoff))
    (sumList addValue zeroValue values limit)
finiteSumCommutesWithLimit algebra [] sequence limit pointwise =
  constantConverges algebra _
finiteSumCommutesWithLimit algebra (value ∷ values) sequence limit pointwise =
  addConverges algebra
    (sequence value) (limit value)
    (λ cutoff →
      sumList _ _ values (λ tail → sequence tail cutoff))
    (sumList _ _ values limit)
    (pointwise value)
    (finiteSumCommutesWithLimit algebra values sequence limit pointwise)

record PhysicalMeasureConvergenceData
    (Measure Observable Scalar : Set) : Set₁ where
  field
    operations : PhysicalOSOperations Measure Observable Scalar
    scalarConvergence :
      ScalarConvergenceAlgebra Scalar
        (zero operations) (add operations) (multiply operations)

    measureSequence : Nat → Measure
    continuumMeasure : Measure

    LocalGaugeInvariant RenormalizedObservable BoundedObservable :
      Observable → Set
    UniformlyIntegrable : (Nat → Observable) → Set

    finiteVolumeReflectedPairExpectationConverges :
      ∀ left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      Converges scalarConvergence
        (λ cutoff →
          expectation operations (measureSequence cutoff)
            (multiplyObservable operations
              (reflectObservable operations left) right))
        (expectation operations continuumMeasure
          (multiplyObservable operations
            (reflectObservable operations left) right))

    thermodynamicReflectedPairExpectationConverges :
      ∀ left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      Converges scalarConvergence
        (λ cutoff →
          expectation operations (measureSequence cutoff)
            (multiplyObservable operations
              (reflectObservable operations left) right))
        (expectation operations continuumMeasure
          (multiplyObservable operations
            (reflectObservable operations left) right))

    continuumReflectedPairExpectationConverges :
      ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      Converges scalarConvergence
        (λ cutoff →
          expectation operations (measureSequence cutoff)
            (multiplyObservable operations
              (reflectObservable operations left) right))
        (expectation operations continuumMeasure
          (multiplyObservable operations
            (reflectObservable operations left) right))

    wilsonCylinderObservableUniformlyBounded : ∀ observable →
      BoundedObservable observable → Set
    boundedWeakConvergenceImpliesExpectationConvergence : ∀ observable →
      BoundedObservable observable →
      Converges scalarConvergence
        (λ cutoff → expectation operations (measureSequence cutoff) observable)
        (expectation operations continuumMeasure observable)
    uniformRenormalizedInsertionMomentBound : ∀ observable →
      RenormalizedObservable observable → Set
    uniformIntegrabilityOfReflectedProducts : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      UniformlyIntegrable
        (λ cutoff →
          multiplyObservable operations
            (reflectObservable operations left) right)
    weakConvergencePlusUniformIntegrability : ∀ sequence →
      UniformlyIntegrable sequence → Set

open PhysicalMeasureConvergenceData public

record AdmissiblePhysicalTestFamily
    {Measure Observable Scalar}
    (dataSet : PhysicalMeasureConvergenceData Measure Observable Scalar)
    (family : PhysicalOSFiniteTestFamily Observable Scalar) : Set₁ where
  field
    testObservableLocal : ∀ test →
      LocalGaugeInvariant dataSet (observable test)

open AdmissiblePhysicalTestFamily public

finiteGramEntrywiseConvergence :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalMeasureConvergenceData Measure Observable Scalar)
    (family : PhysicalOSFiniteTestFamily Observable Scalar) →
  AdmissiblePhysicalTestFamily dataSet family →
  ∀ left right →
  Converges (scalarConvergence dataSet)
    (λ cutoff →
      physicalReflectedGramEntry (operations dataSet)
        (measureSequence dataSet cutoff) left right)
    (physicalReflectedGramEntry (operations dataSet)
      (continuumMeasure dataSet) left right)
finiteGramEntrywiseConvergence dataSet family admissible left right =
  multiplyConstantConverges (scalarConvergence dataSet)
    (multiply (operations dataSet)
      (conjugate (operations dataSet) (coefficient left))
      (coefficient right))
    (λ cutoff →
      expectation (operations dataSet)
        (measureSequence dataSet cutoff)
        (multiplyObservable (operations dataSet)
          (reflectObservable (operations dataSet) (observable left))
          (observable right)))
    (expectation (operations dataSet)
      (continuumMeasure dataSet)
      (multiplyObservable (operations dataSet)
        (reflectObservable (operations dataSet) (observable left))
        (observable right)))
    (finiteVolumeReflectedPairExpectationConverges dataSet
      (observable left) (observable right)
      (testObservableLocal admissible left)
      (testObservableLocal admissible right))

finiteDoubleSumCommutesWithLimit :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalMeasureConvergenceData Measure Observable Scalar)
    (family : PhysicalOSFiniteTestFamily Observable Scalar) →
  AdmissiblePhysicalTestFamily dataSet family →
  Converges (scalarConvergence dataSet)
    (λ cutoff →
      physicalReflectedGramQuadraticForm (operations dataSet)
        (measureSequence dataSet cutoff) family)
    (physicalReflectedGramQuadraticForm (operations dataSet)
      (continuumMeasure dataSet) family)
finiteDoubleSumCommutesWithLimit dataSet family admissible =
  finiteSumCommutesWithLimit
    (scalarConvergence dataSet) (tests family)
    (λ left cutoff →
      sumList (add (operations dataSet)) (zero (operations dataSet))
        (tests family)
        (λ right →
          physicalReflectedGramEntry (operations dataSet)
            (measureSequence dataSet cutoff) left right))
    (λ left →
      sumList (add (operations dataSet)) (zero (operations dataSet))
        (tests family)
        (λ right →
          physicalReflectedGramEntry (operations dataSet)
            (continuumMeasure dataSet) left right))
    (λ left →
      finiteSumCommutesWithLimit
        (scalarConvergence dataSet) (tests family)
        (λ right cutoff →
          physicalReflectedGramEntry (operations dataSet)
            (measureSequence dataSet cutoff) left right)
        (λ right →
          physicalReflectedGramEntry (operations dataSet)
            (continuumMeasure dataSet) left right)
        (λ right →
          finiteGramEntrywiseConvergence dataSet family admissible left right))

finiteGramQuadraticFormConverges = finiteDoubleSumCommutesWithLimit

record PhysicalMeasureToOSGramData
    (Measure Observable Scalar : Set) : Set₁ where
  field
    convergenceData :
      PhysicalMeasureConvergenceData Measure Observable Scalar
    TestFamily : Set
    decodeFamily : TestFamily → PhysicalOSFiniteTestFamily Observable Scalar
    admissibleFamily : ∀ family →
      AdmissiblePhysicalTestFamily convergenceData (decodeFamily family)

    Nonnegative : Scalar → Set
    finiteGramNonnegative : ∀ cutoff family →
      Nonnegative
        (physicalReflectedGramQuadraticForm
          (operations convergenceData)
          (measureSequence convergenceData cutoff)
          (decodeFamily family))
    nonnegativeConeClosed : ∀ sequence target →
      Converges (scalarConvergence convergenceData) sequence target →
      (∀ cutoff → Nonnegative (sequence cutoff)) → Nonnegative target

open PhysicalMeasureToOSGramData public

physicalMeasureTopologyControlsOSGram :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalMeasureToOSGramData Measure Observable Scalar) →
  OS.OSGramLimitData Measure (TestFamily dataSet) Scalar
physicalMeasureTopologyControlsOSGram dataSet = record
  { finiteSchwinger = measureSequence (convergenceData dataSet)
  ; continuumSchwinger = continuumMeasure (convergenceData dataSet)
  ; reflectedGramQuadraticForm =
      λ measure family →
        physicalReflectedGramQuadraticForm
          (operations (convergenceData dataSet)) measure
          (decodeFamily dataSet family)
  ; scalarLimit = record
      { Converges = Converges (scalarConvergence (convergenceData dataSet)) }
  ; Nonnegative = Nonnegative dataSet
  ; gramQuadraticFormConverges =
      λ family →
        finiteGramQuadraticFormConverges
          (convergenceData dataSet)
          (decodeFamily dataSet family)
          (admissibleFamily dataSet family)
  ; finiteGramNonnegative = finiteGramNonnegative dataSet
  ; nonnegativeConeClosed = nonnegativeConeClosed dataSet
  }

physicalMeasureConvergenceImpliesGramConvergence :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalMeasureToOSGramData Measure Observable Scalar)
    family →
  Converges (scalarConvergence (convergenceData dataSet))
    (λ cutoff →
      physicalReflectedGramQuadraticForm
        (operations (convergenceData dataSet))
        (measureSequence (convergenceData dataSet) cutoff)
        (decodeFamily dataSet family))
    (physicalReflectedGramQuadraticForm
      (operations (convergenceData dataSet))
      (continuumMeasure (convergenceData dataSet))
      (decodeFamily dataSet family))
physicalMeasureConvergenceImpliesGramConvergence dataSet family =
  finiteGramQuadraticFormConverges
    (convergenceData dataSet)
    (decodeFamily dataSet family)
    (admissibleFamily dataSet family)

physicalContinuumReflectionPositive :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalMeasureToOSGramData Measure Observable Scalar) →
  OS.GramReflectionPositive
    (physicalMeasureTopologyControlsOSGram dataSet)
    (continuumMeasure (convergenceData dataSet))
physicalContinuumReflectionPositive dataSet =
  OS.continuumReflectionPositiveFromGramTopology
    (physicalMeasureTopologyControlsOSGram dataSet)

physicalFiniteGramExpansionLevel : ProofLevel
physicalFiniteGramExpansionLevel = machineChecked

finiteGramEntrywiseToQuadraticConvergenceLevel : ProofLevel
finiteGramEntrywiseToQuadraticConvergenceLevel = machineChecked

physicalMeasureToOSGramAdapterLevel : ProofLevel
physicalMeasureToOSGramAdapterLevel = machineChecked

physicalExpectationConvergenceInputsLevel : ProofLevel
physicalExpectationConvergenceInputsLevel = conditional
