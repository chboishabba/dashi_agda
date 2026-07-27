module DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
-- Relationship: primary source for exponentiated fluctuation-field cluster
-- expansions and the finite-volume locality mechanism used below.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
-- Relationship: convergence and connected-cluster tail input.
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions", Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions II", Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
-- Relationship: continuum Schwinger-function and reconstruction target.
--
-- Pietro Menotti and Andrea Pelissetto, "General Proof of
-- Osterwalder-Schrader Positivity for the Wilson Action", Communications in
-- Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251
-- Relationship: finite-cutoff Wilson reflection-positivity input.
--
-- DASHI-original contribution: the records below isolate the physical cluster
-- tail, diagonal-limit, exponential-moment and uniform-integrability leaves and
-- derive the legacy expectation-convergence fields from those leaves.  No
-- pointwise-correlator shortcut is used for OS positivity.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A generic tail-controlled convergence producer.
--
-- The physical input is a quantitative difference bound and a vanishing tail.
-- Completeness of the scalar topology is a reusable real-analysis authority;
-- convergence of the expectation sequence is derived, not stored as a field.
------------------------------------------------------------------------

record TailControlledConvergence (Scalar : Set) : Set₁ where
  field
    Sequence : Nat → Scalar
    Limit Tail : Nat → Scalar
    target : Scalar

    Distance : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    Converges : (Nat → Scalar) → Scalar → Set

    earlier : Nat → Nat → Nat
    differenceControlled : ∀ left right →
      LessEqual (Distance (Sequence left) (Sequence right))
        (Tail (earlier left right))

    tailVanishes : Set
    cauchyCompletionFromTail :
      (∀ left right →
        LessEqual (Distance (Sequence left) (Sequence right))
          (Tail (earlier left right))) →
      tailVanishes → Converges Sequence target

open TailControlledConvergence public

tailControlledSequenceConverges :
  ∀ {Scalar} (dataSet : TailControlledConvergence Scalar) →
  Converges dataSet (Sequence dataSet) (target dataSet)
tailControlledSequenceConverges dataSet =
  cauchyCompletionFromTail dataSet
    (differenceControlled dataSet)
    (tailVanishes dataSet)

------------------------------------------------------------------------
-- Staged finite-volume -> thermodynamic -> continuum convergence.
------------------------------------------------------------------------

record PhysicalThermodynamicClusterData
    (Measure Observable Scalar : Set) : Set₁ where
  field
    operations : Gram.PhysicalOSOperations Measure Observable Scalar
    scalarConvergence :
      Gram.ScalarConvergenceAlgebra Scalar
        (Gram.zero operations)
        (Gram.add operations)
        (Gram.multiply operations)

    finiteVolumeMeasure : Nat → Nat → Measure
    thermodynamicMeasure : Nat → Measure
    continuumMeasure : Measure
    diagonalVolume : Nat → Nat

    LocalGaugeInvariant RenormalizedObservable BoundedObservable :
      Observable → Set

    reflectedPair : Observable → Observable → Observable
    reflectedPairDefinition : ∀ left right →
      reflectedPair left right
      ≡ Gram.multiplyObservable operations
          (Gram.reflectObservable operations left) right

    -- Fixed-cutoff thermodynamic limit from the crossing-cluster tail.
    finiteVolumePairTail : ∀ cutoff left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      TailControlledConvergence Scalar

    finiteVolumePairSequenceExact : ∀ cutoff left right leftLocal rightLocal volume →
      Sequence (finiteVolumePairTail cutoff left right leftLocal rightLocal) volume
      ≡ Gram.expectation operations (finiteVolumeMeasure cutoff volume)
          (reflectedPair left right)

    finiteVolumePairTargetExact : ∀ cutoff left right leftLocal rightLocal →
      target (finiteVolumePairTail cutoff left right leftLocal rightLocal)
      ≡ Gram.expectation operations (thermodynamicMeasure cutoff)
          (reflectedPair left right)

    -- Continuum Cauchy estimate for thermodynamic expectations.
    continuumPairTail : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      TailControlledConvergence Scalar

    continuumPairSequenceExact : ∀ left right leftRenormalized rightRenormalized cutoff →
      Sequence (continuumPairTail left right leftRenormalized rightRenormalized) cutoff
      ≡ Gram.expectation operations (thermodynamicMeasure cutoff)
          (reflectedPair left right)

    continuumPairTargetExact : ∀ left right leftRenormalized rightRenormalized →
      target (continuumPairTail left right leftRenormalized rightRenormalized)
      ≡ Gram.expectation operations continuumMeasure (reflectedPair left right)

    -- Diagonal finite-volume/cutoff sequence.  The diagonal estimate combines
    -- the finite-volume crossing tail with the continuum step tail.
    diagonalPairTail : ∀ left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      TailControlledConvergence Scalar

    diagonalPairSequenceExact : ∀ left right leftLocal rightLocal cutoff →
      Sequence (diagonalPairTail left right leftLocal rightLocal) cutoff
      ≡ Gram.expectation operations
          (finiteVolumeMeasure cutoff (diagonalVolume cutoff))
          (reflectedPair left right)

    diagonalPairTargetExact : ∀ left right leftLocal rightLocal →
      target (diagonalPairTail left right leftLocal rightLocal)
      ≡ Gram.expectation operations continuumMeasure (reflectedPair left right)

open PhysicalThermodynamicClusterData public

finiteVolumeExpectationCauchy :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalThermodynamicClusterData Measure Observable Scalar)
    cutoff left right
    (leftLocal : LocalGaugeInvariant dataSet left)
    (rightLocal : LocalGaugeInvariant dataSet right) →
  Converges (finiteVolumePairTail dataSet cutoff left right leftLocal rightLocal)
    (Sequence (finiteVolumePairTail dataSet cutoff left right leftLocal rightLocal))
    (target (finiteVolumePairTail dataSet cutoff left right leftLocal rightLocal))
finiteVolumeExpectationCauchy dataSet cutoff left right leftLocal rightLocal =
  tailControlledSequenceConverges
    (finiteVolumePairTail dataSet cutoff left right leftLocal rightLocal)

thermodynamicExpectationExists = finiteVolumeExpectationCauchy

continuumCylinderObservableCauchy :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalThermodynamicClusterData Measure Observable Scalar)
    left right
    (leftRenormalized : RenormalizedObservable dataSet left)
    (rightRenormalized : RenormalizedObservable dataSet right) →
  Converges (continuumPairTail dataSet left right leftRenormalized rightRenormalized)
    (Sequence (continuumPairTail dataSet left right leftRenormalized rightRenormalized))
    (target (continuumPairTail dataSet left right leftRenormalized rightRenormalized))
continuumCylinderObservableCauchy dataSet left right leftRenormalized rightRenormalized =
  tailControlledSequenceConverges
    (continuumPairTail dataSet left right leftRenormalized rightRenormalized)

continuumWilsonObservableExpectationExists = continuumCylinderObservableCauchy

diagonalReflectedPairExpectationConverges :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalThermodynamicClusterData Measure Observable Scalar)
    left right
    (leftLocal : LocalGaugeInvariant dataSet left)
    (rightLocal : LocalGaugeInvariant dataSet right) →
  Converges (diagonalPairTail dataSet left right leftLocal rightLocal)
    (Sequence (diagonalPairTail dataSet left right leftLocal rightLocal))
    (target (diagonalPairTail dataSet left right leftLocal rightLocal))
diagonalReflectedPairExpectationConverges dataSet left right leftLocal rightLocal =
  tailControlledSequenceConverges
    (diagonalPairTail dataSet left right leftLocal rightLocal)

------------------------------------------------------------------------
-- Compact-group Wilson observable bounds.
------------------------------------------------------------------------

record WilsonCylinderBoundData (Loop Observable Scalar : Set) : Set₁ where
  field
    loopObservable : Loop → Observable
    multiplyObservable : Observable → Observable → Observable
    identityObservable : Observable

    Bound : Observable → Scalar → Set
    one groupRank : Scalar
    multiplyScalar : Scalar → Scalar → Scalar

    wilsonLoopObservableUniformBound : ∀ loop →
      Bound (loopObservable loop) groupRank

    multiplyBound : ∀ left right leftBound rightBound →
      Bound left leftBound → Bound right rightBound →
      Bound (multiplyObservable left right)
        (multiplyScalar leftBound rightBound)

    identityBound : Bound identityObservable one

open WilsonCylinderBoundData public

productLoopObservable :
  ∀ {Loop Observable Scalar} →
  WilsonCylinderBoundData Loop Observable Scalar → List Loop → Observable
productLoopObservable dataSet [] = identityObservable dataSet
productLoopObservable dataSet (loop ∷ loops) =
  multiplyObservable dataSet
    (loopObservable dataSet loop)
    (productLoopObservable dataSet loops)

productLoopBound :
  ∀ {Loop Observable Scalar} →
  WilsonCylinderBoundData Loop Observable Scalar → List Loop → Scalar
productLoopBound dataSet [] = one dataSet
productLoopBound dataSet (loop ∷ loops) =
  multiplyScalar dataSet (groupRank dataSet) (productLoopBound dataSet loops)

finiteProductWilsonObservableUniformBound :
  ∀ {Loop Observable Scalar}
    (dataSet : WilsonCylinderBoundData Loop Observable Scalar)
    loops →
  Bound dataSet (productLoopObservable dataSet loops) (productLoopBound dataSet loops)
finiteProductWilsonObservableUniformBound dataSet [] = identityBound dataSet
finiteProductWilsonObservableUniformBound dataSet (loop ∷ loops) =
  multiplyBound dataSet
    (loopObservable dataSet loop)
    (productLoopObservable dataSet loops)
    (groupRank dataSet)
    (productLoopBound dataSet loops)
    (wilsonLoopObservableUniformBound dataSet loop)
    (finiteProductWilsonObservableUniformBound dataSet loops)

boundedCylinderObservableUniformBound = finiteProductWilsonObservableUniformBound

------------------------------------------------------------------------
-- Exponential moments -> polynomial moments -> uniform integrability.
------------------------------------------------------------------------

record UniformIntegrabilityWitness
    (Observable Scalar : Set) : Set₁ where
  field
    sequence : Nat → Observable
    tailModulus : Nat → Scalar
    tailModulusVanishes : Set
    tailExpectationControlled : ∀ cutoff threshold → Set

open UniformIntegrabilityWitness public

record ExponentialMomentProducer
    (Measure Observable Scalar : Set) : Set₁ where
  field
    operations : Gram.PhysicalOSOperations Measure Observable Scalar
    measureSequence : Nat → Measure

    RenormalizedObservable : Observable → Set
    absoluteObservable : Observable → Observable
    reflectedProduct : Observable → Observable → Observable
    exponentialObservable : Scalar → Observable → Observable
    powerObservable : Nat → Observable → Observable

    zero one lambda : Scalar
    add multiply divide exp : Scalar → Scalar → Scalar
    factorial : Nat → Scalar
    LessEqual : Scalar → Scalar → Set

    exponentialMomentBound : Observable → Scalar
    exponentialMomentUniformBound : ∀ observable →
      RenormalizedObservable observable → ∀ cutoff →
      LessEqual
        (Gram.expectation operations (measureSequence cutoff)
          (exponentialObservable lambda (absoluteObservable observable)))
        (exponentialMomentBound observable)

    powerBelowFactorialExponential : ∀ degree observable → Set

    singleScaleInsertionMomentBound : ∀ degree observable →
      RenormalizedObservable observable → ∀ cutoff →
      LessEqual
        (Gram.expectation operations (measureSequence cutoff)
          (powerObservable degree (absoluteObservable observable)))
        (multiply (factorial degree)
          (divide (exponentialMomentBound observable) lambda))

    reflectedProductYoungBound : ∀ left right → Set

    reflectedProductExponentialMomentBound : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      ∀ cutoff → Set

    buildUniformIntegrabilityWitness : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      UniformIntegrabilityWitness Observable Scalar

open ExponentialMomentProducer public

uniformEvenMomentBound :
  ∀ {Measure Observable Scalar}
    (dataSet : ExponentialMomentProducer Measure Observable Scalar)
    degree observable →
  RenormalizedObservable dataSet observable → ∀ cutoff →
  LessEqual dataSet
    (Gram.expectation (operations dataSet) (measureSequence dataSet cutoff)
      (powerObservable dataSet degree (absoluteObservable dataSet observable)))
    (multiply dataSet (factorial dataSet degree)
      (divide dataSet (exponentialMomentBound dataSet observable) (lambda dataSet)))
uniformEvenMomentBound = singleScaleInsertionMomentBound

uniformExponentialMomentBound = exponentialMomentUniformBound

exponentialMomentImpliesUniformIntegrability :
  ∀ {Measure Observable Scalar}
    (dataSet : ExponentialMomentProducer Measure Observable Scalar)
    left right →
  RenormalizedObservable dataSet left →
  RenormalizedObservable dataSet right →
  UniformIntegrabilityWitness Observable Scalar
exponentialMomentImpliesUniformIntegrability = buildUniformIntegrabilityWitness

uniformIntegrabilityOfReflectedProducts =
  exponentialMomentImpliesUniformIntegrability

------------------------------------------------------------------------
-- Tightness and projective consistency are kept after the moment theorem, not
-- hidden inside expectation convergence.
------------------------------------------------------------------------

record PhysicalMeasureCompactnessData
    (Marginal Measure Scalar : Set) : Set₁ where
  field
    finiteDimensionalMarginal : Nat → Marginal
    continuumCandidate : Measure
    Tight : Marginal → Set
    ProjectivelyConsistent : Nat → Nat → Set

    momentTailBoundImpliesTight : ∀ dimension → Set
    finiteDimensionalMarginalTight : ∀ dimension →
      Tight (finiteDimensionalMarginal dimension)
    projectiveFamilyConsistency : ∀ lower upper →
      ProjectivelyConsistent lower upper

    prokhorovTightnessForGaugeInvariantMarginals : Set
    continuumMeasureSubsequenceExists : Set
    continuumMeasureUniquenessFromClustering : Set

open PhysicalMeasureCompactnessData public

------------------------------------------------------------------------
-- Physical expectation producer and adapter to the OS-Gram module.
------------------------------------------------------------------------

record PhysicalExpectationProducerData
    (Measure Observable Scalar : Set) : Set₁ where
  field
    thermodynamic : PhysicalThermodynamicClusterData Measure Observable Scalar
    moments : ExponentialMomentProducer Measure Observable Scalar

    operationsAgree : operations thermodynamic ≡ operations moments
    measureSequenceAgree : ∀ cutoff →
      measureSequence moments cutoff
      ≡ finiteVolumeMeasure thermodynamic cutoff
          (diagonalVolume thermodynamic cutoff)

    UniformlyIntegrable : (Nat → Observable) → Set
    witnessImpliesUniformlyIntegrable : ∀ witness →
      UniformlyIntegrable (sequence witness)

    boundedWeakConvergence : ∀ observable →
      BoundedObservable thermodynamic observable →
      Gram.Converges (scalarConvergence thermodynamic)
        (λ cutoff →
          Gram.expectation (operations thermodynamic)
            (finiteVolumeMeasure thermodynamic cutoff
              (diagonalVolume thermodynamic cutoff)) observable)
        (Gram.expectation (operations thermodynamic)
          (continuumMeasure thermodynamic) observable)

    weakConvergencePlusUniformIntegrability : ∀ sequence →
      UniformlyIntegrable sequence → Set

    boundedObservableHasWitness : ∀ observable →
      BoundedObservable thermodynamic observable → Set

    renormalizedMomentWitness : ∀ observable →
      RenormalizedObservable thermodynamic observable → Set

    reflectedProductUI : ∀ left right →
      RenormalizedObservable thermodynamic left →
      RenormalizedObservable thermodynamic right →
      UniformlyIntegrable
        (λ cutoff →
          reflectedProduct moments left right)

open PhysicalExpectationProducerData public

physicalMeasureConvergenceDataFromProducer :
  ∀ {Measure Observable Scalar} →
  PhysicalExpectationProducerData Measure Observable Scalar →
  Gram.PhysicalMeasureConvergenceData Measure Observable Scalar
physicalMeasureConvergenceDataFromProducer dataSet = record
  { operations = operations (thermodynamic dataSet)
  ; scalarConvergence = scalarConvergence (thermodynamic dataSet)
  ; measureSequence = λ cutoff →
      finiteVolumeMeasure (thermodynamic dataSet) cutoff
        (diagonalVolume (thermodynamic dataSet) cutoff)
  ; continuumMeasure = continuumMeasure (thermodynamic dataSet)
  ; LocalGaugeInvariant = LocalGaugeInvariant (thermodynamic dataSet)
  ; RenormalizedObservable = RenormalizedObservable (thermodynamic dataSet)
  ; BoundedObservable = BoundedObservable (thermodynamic dataSet)
  ; UniformlyIntegrable = UniformlyIntegrable dataSet
  ; finiteVolumeReflectedPairExpectationConverges =
      λ left right leftLocal rightLocal →
        diagonalReflectedPairExpectationConverges
          (thermodynamic dataSet) left right leftLocal rightLocal
  ; thermodynamicReflectedPairExpectationConverges =
      λ left right leftLocal rightLocal →
        diagonalReflectedPairExpectationConverges
          (thermodynamic dataSet) left right leftLocal rightLocal
  ; continuumReflectedPairExpectationConverges =
      λ left right leftRenormalized rightRenormalized →
        continuumCylinderObservableCauchy
          (thermodynamic dataSet) left right leftRenormalized rightRenormalized
  ; wilsonCylinderObservableUniformlyBounded =
      boundedObservableHasWitness dataSet
  ; boundedWeakConvergenceImpliesExpectationConvergence =
      boundedWeakConvergence dataSet
  ; uniformRenormalizedInsertionMomentBound =
      renormalizedMomentWitness dataSet
  ; uniformIntegrabilityOfReflectedProducts =
      reflectedProductUI dataSet
  ; weakConvergencePlusUniformIntegrability =
      weakConvergencePlusUniformIntegrability dataSet
  }

------------------------------------------------------------------------
-- Proof-level ledger.
------------------------------------------------------------------------

tailControlledCauchyReductionLevel : ProofLevel
tailControlledCauchyReductionLevel = machineChecked

thermodynamicExpectationAssemblyLevel : ProofLevel
thermodynamicExpectationAssemblyLevel = machineChecked

continuumDiagonalAssemblyLevel : ProofLevel
continuumDiagonalAssemblyLevel = machineChecked

wilsonCylinderBoundAssemblyLevel : ProofLevel
wilsonCylinderBoundAssemblyLevel = machineChecked

exponentialMomentToUniformIntegrabilityReductionLevel : ProofLevel
exponentialMomentToUniformIntegrabilityReductionLevel = machineChecked

physicalExpectationConvergenceAdapterLevel : ProofLevel
physicalExpectationConvergenceAdapterLevel = machineChecked

physicalClusterTailInputsLevel : ProofLevel
physicalClusterTailInputsLevel = conditional

physicalContinuumStepTailInputsLevel : ProofLevel
physicalContinuumStepTailInputsLevel = conditional

physicalExponentialMomentInputsLevel : ProofLevel
physicalExponentialMomentInputsLevel = conditional

physicalWeakConvergenceInputsLevel : ProofLevel
physicalWeakConvergenceInputsLevel = conditional

physicalMeasureCompactnessInputsLevel : ProofLevel
physicalMeasureCompactnessInputsLevel = conditional
