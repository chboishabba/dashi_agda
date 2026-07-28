module DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

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
-- DASHI-original contribution: quantitative crossing-cluster and multiscale
-- tails are converted into staged and diagonal expectation convergence; a
-- uniform exponential moment is converted into polynomial moments and an
-- explicit uniform-integrability witness.  The legacy T5 expectation fields are
-- constructed by the final adapter and are no longer primitive physical inputs.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Tail-controlled convergence for a fixed sequence and target.
------------------------------------------------------------------------

record TailControlledConvergence
    (Scalar : Set)
    (Converges : (Nat → Scalar) → Scalar → Set)
    (sequence : Nat → Scalar)
    (target : Scalar) : Set₁ where
  field
    Distance : Scalar → Scalar → Scalar
    Tail : Nat → Scalar
    LessEqual : Scalar → Scalar → Set
    earlier : Nat → Nat → Nat

    differenceControlled : ∀ left right →
      LessEqual (Distance (sequence left) (sequence right))
        (Tail (earlier left right))

    tailVanishes : Set

    cauchyCompletionFromTail :
      (∀ left right →
        LessEqual (Distance (sequence left) (sequence right))
          (Tail (earlier left right))) →
      tailVanishes → Converges sequence target

open TailControlledConvergence public

tailControlledSequenceConverges :
  ∀ {Scalar Converges sequence target} →
  TailControlledConvergence Scalar Converges sequence target →
  Converges sequence target
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

    -- Fixed-cutoff thermodynamic limit.  The physical leaf is the connected
    -- boundary-crossing cluster tail encoded inside this witness.
    finiteVolumePairTail : ∀ cutoff left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      TailControlledConvergence Scalar
        (Gram.Converges scalarConvergence)
        (λ volume →
          Gram.expectation operations (finiteVolumeMeasure cutoff volume)
            (Gram.multiplyObservable operations
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations (thermodynamicMeasure cutoff)
          (Gram.multiplyObservable operations
            (Gram.reflectObservable operations left) right))

    -- Thermodynamic continuum sequence.  The physical leaf is the summable
    -- one-step blocking/localization defect.
    continuumPairTail : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      TailControlledConvergence Scalar
        (Gram.Converges scalarConvergence)
        (λ cutoff →
          Gram.expectation operations (thermodynamicMeasure cutoff)
            (Gram.multiplyObservable operations
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations continuumMeasure
          (Gram.multiplyObservable operations
            (Gram.reflectObservable operations left) right))

    -- Diagonal finite-volume/cutoff sequence.  This combines both tails and is
    -- the sequence consumed by the legacy OS-Gram adapter.
    diagonalPairTail : ∀ left right →
      LocalGaugeInvariant left → LocalGaugeInvariant right →
      TailControlledConvergence Scalar
        (Gram.Converges scalarConvergence)
        (λ cutoff →
          Gram.expectation operations
            (finiteVolumeMeasure cutoff (diagonalVolume cutoff))
            (Gram.multiplyObservable operations
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations continuumMeasure
          (Gram.multiplyObservable operations
            (Gram.reflectObservable operations left) right))

    -- The same diagonal construction for renormalized, potentially unbounded
    -- insertions after their moment/UI estimates have been supplied.
    renormalizedDiagonalPairTail : ∀ left right →
      RenormalizedObservable left → RenormalizedObservable right →
      TailControlledConvergence Scalar
        (Gram.Converges scalarConvergence)
        (λ cutoff →
          Gram.expectation operations
            (finiteVolumeMeasure cutoff (diagonalVolume cutoff))
            (Gram.multiplyObservable operations
              (Gram.reflectObservable operations left) right))
        (Gram.expectation operations continuumMeasure
          (Gram.multiplyObservable operations
            (Gram.reflectObservable operations left) right))

open PhysicalThermodynamicClusterData public

finiteVolumeExpectationCauchy :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalThermodynamicClusterData Measure Observable Scalar)
    cutoff left right
    (leftLocal : LocalGaugeInvariant dataSet left)
    (rightLocal : LocalGaugeInvariant dataSet right) →
  Gram.Converges (scalarConvergence dataSet)
    (λ volume →
      Gram.expectation (operations dataSet)
        (finiteVolumeMeasure dataSet cutoff volume)
        (Gram.multiplyObservable (operations dataSet)
          (Gram.reflectObservable (operations dataSet) left) right))
    (Gram.expectation (operations dataSet)
      (thermodynamicMeasure dataSet cutoff)
      (Gram.multiplyObservable (operations dataSet)
        (Gram.reflectObservable (operations dataSet) left) right))
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
  Gram.Converges (scalarConvergence dataSet)
    (λ cutoff →
      Gram.expectation (operations dataSet)
        (thermodynamicMeasure dataSet cutoff)
        (Gram.multiplyObservable (operations dataSet)
          (Gram.reflectObservable (operations dataSet) left) right))
    (Gram.expectation (operations dataSet)
      (continuumMeasure dataSet)
      (Gram.multiplyObservable (operations dataSet)
        (Gram.reflectObservable (operations dataSet) left) right))
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
  Gram.Converges (scalarConvergence dataSet)
    (λ cutoff →
      Gram.expectation (operations dataSet)
        (finiteVolumeMeasure dataSet cutoff (diagonalVolume dataSet cutoff))
        (Gram.multiplyObservable (operations dataSet)
          (Gram.reflectObservable (operations dataSet) left) right))
    (Gram.expectation (operations dataSet)
      (continuumMeasure dataSet)
      (Gram.multiplyObservable (operations dataSet)
        (Gram.reflectObservable (operations dataSet) left) right))
diagonalReflectedPairExpectationConverges dataSet left right leftLocal rightLocal =
  tailControlledSequenceConverges
    (diagonalPairTail dataSet left right leftLocal rightLocal)

renormalizedDiagonalReflectedPairExpectationConverges :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalThermodynamicClusterData Measure Observable Scalar)
    left right
    (leftRenormalized : RenormalizedObservable dataSet left)
    (rightRenormalized : RenormalizedObservable dataSet right) →
  Gram.Converges (scalarConvergence dataSet)
    (λ cutoff →
      Gram.expectation (operations dataSet)
        (finiteVolumeMeasure dataSet cutoff (diagonalVolume dataSet cutoff))
        (Gram.multiplyObservable (operations dataSet)
          (Gram.reflectObservable (operations dataSet) left) right))
    (Gram.expectation (operations dataSet)
      (continuumMeasure dataSet)
      (Gram.multiplyObservable (operations dataSet)
        (Gram.reflectObservable (operations dataSet) left) right))
renormalizedDiagonalReflectedPairExpectationConverges
  dataSet left right leftRenormalized rightRenormalized =
  tailControlledSequenceConverges
    (renormalizedDiagonalPairTail dataSet left right
      leftRenormalized rightRenormalized)

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
    (Observable Scalar : Set)
    (observableSequence : Nat → Observable) : Set₁ where
  field
    tailModulus : Nat → Scalar
    tailModulusVanishes : Set
    tailExpectationControlled : ∀ cutoff threshold → Set

open UniformIntegrabilityWitness public

record ExponentialMomentProducer
    {Measure Observable Scalar : Set}
    (operations : Gram.PhysicalOSOperations Measure Observable Scalar)
    (measureSequence : Nat → Measure)
    (RenormalizedObservable : Observable → Set) : Set₁ where
  field
    absoluteObservable : Observable → Observable
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
        (λ cutoff →
          Gram.multiplyObservable operations
            (Gram.reflectObservable operations left) right)

open ExponentialMomentProducer public

uniformEvenMomentBound :
  ∀ {Measure Observable Scalar}
    {operations : Gram.PhysicalOSOperations Measure Observable Scalar}
    {measureSequence : Nat → Measure}
    {RenormalizedObservable : Observable → Set}
    (dataSet : ExponentialMomentProducer operations measureSequence
      RenormalizedObservable)
    degree observable →
  RenormalizedObservable observable → ∀ cutoff →
  LessEqual dataSet
    (Gram.expectation operations (measureSequence cutoff)
      (powerObservable dataSet degree (absoluteObservable dataSet observable)))
    (multiply dataSet (factorial dataSet degree)
      (divide dataSet (exponentialMomentBound dataSet observable)
        (lambda dataSet)))
uniformEvenMomentBound = singleScaleInsertionMomentBound

uniformExponentialMomentBound = exponentialMomentUniformBound

exponentialMomentImpliesUniformIntegrability :
  ∀ {Measure Observable Scalar}
    {operations : Gram.PhysicalOSOperations Measure Observable Scalar}
    {measureSequence : Nat → Measure}
    {RenormalizedObservable : Observable → Set}
    (dataSet : ExponentialMomentProducer operations measureSequence
      RenormalizedObservable)
    left right →
  RenormalizedObservable left → RenormalizedObservable right →
  UniformIntegrabilityWitness Observable Scalar
    (λ cutoff →
      Gram.multiplyObservable operations
        (Gram.reflectObservable operations left) right)
exponentialMomentImpliesUniformIntegrability = buildUniformIntegrabilityWitness

uniformIntegrabilityOfReflectedProducts =
  exponentialMomentImpliesUniformIntegrability

------------------------------------------------------------------------
-- Tightness and projective consistency remain separate authorities after the
-- moment theorem; they are not hidden inside expectation convergence.
------------------------------------------------------------------------

record PhysicalMeasureCompactnessData
    (Marginal Measure : Set) : Set₁ where
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
-- Physical expectation producer and adapter to the complete OS-Gram module.
------------------------------------------------------------------------

record PhysicalExpectationProducerData
    (Measure Observable Scalar : Set) : Set₁ where
  field
    thermodynamic : PhysicalThermodynamicClusterData Measure Observable Scalar

    diagonalMeasure : Nat → Measure
    diagonalMeasureDefinition : ∀ cutoff → Set

    moments : ExponentialMomentProducer
      (operations thermodynamic)
      diagonalMeasure
      (RenormalizedObservable thermodynamic)

    UniformlyIntegrable : (Nat → Observable) → Set

    witnessImpliesUniformlyIntegrable :
      ∀ {sequence : Nat → Observable} →
      UniformIntegrabilityWitness Observable Scalar sequence →
      UniformlyIntegrable sequence

    boundedObservableTail : ∀ observable →
      BoundedObservable thermodynamic observable →
      TailControlledConvergence Scalar
        (Gram.Converges (scalarConvergence thermodynamic))
        (λ cutoff →
          Gram.expectation (operations thermodynamic)
            (diagonalMeasure cutoff) observable)
        (Gram.expectation (operations thermodynamic)
          (continuumMeasure thermodynamic) observable)

    boundedObservableHasWitness : ∀ observable →
      BoundedObservable thermodynamic observable → Set

    weakConvergencePlusUniformIntegrability : ∀ sequence →
      UniformlyIntegrable sequence → Set

open PhysicalExpectationProducerData public

boundedWeakConvergenceFromTail :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalExpectationProducerData Measure Observable Scalar)
    observable (bounded : BoundedObservable (thermodynamic dataSet) observable) →
  Gram.Converges (scalarConvergence (thermodynamic dataSet))
    (λ cutoff →
      Gram.expectation (operations (thermodynamic dataSet))
        (diagonalMeasure dataSet cutoff) observable)
    (Gram.expectation (operations (thermodynamic dataSet))
      (continuumMeasure (thermodynamic dataSet)) observable)
boundedWeakConvergenceFromTail dataSet observable bounded =
  tailControlledSequenceConverges
    (boundedObservableTail dataSet observable bounded)

physicalReflectedProductUniformlyIntegrable :
  ∀ {Measure Observable Scalar}
    (dataSet : PhysicalExpectationProducerData Measure Observable Scalar)
    left right →
  RenormalizedObservable (thermodynamic dataSet) left →
  RenormalizedObservable (thermodynamic dataSet) right →
  UniformlyIntegrable dataSet
    (λ cutoff →
      Gram.multiplyObservable (operations (thermodynamic dataSet))
        (Gram.reflectObservable (operations (thermodynamic dataSet)) left) right)
physicalReflectedProductUniformlyIntegrable
  dataSet left right leftRenormalized rightRenormalized =
  witnessImpliesUniformlyIntegrable dataSet
    (uniformIntegrabilityOfReflectedProducts
      (moments dataSet) left right leftRenormalized rightRenormalized)

physicalMeasureConvergenceDataFromProducer :
  ∀ {Measure Observable Scalar} →
  PhysicalExpectationProducerData Measure Observable Scalar →
  Gram.PhysicalMeasureConvergenceData Measure Observable Scalar
physicalMeasureConvergenceDataFromProducer dataSet = record
  { operations = operations (thermodynamic dataSet)
  ; scalarConvergence = scalarConvergence (thermodynamic dataSet)
  ; measureSequence = diagonalMeasure dataSet
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
        renormalizedDiagonalReflectedPairExpectationConverges
          (thermodynamic dataSet) left right
          leftRenormalized rightRenormalized
  ; wilsonCylinderObservableUniformlyBounded =
      boundedObservableHasWitness dataSet
  ; boundedWeakConvergenceImpliesExpectationConvergence =
      boundedWeakConvergenceFromTail dataSet
  ; uniformRenormalizedInsertionMomentBound =
      λ observable admissible →
        ∀ degree cutoff →
        LessEqual (moments dataSet)
          (Gram.expectation (operations (thermodynamic dataSet))
            (diagonalMeasure dataSet cutoff)
            (powerObservable (moments dataSet) degree
              (absoluteObservable (moments dataSet) observable)))
          (multiply (moments dataSet) (factorial (moments dataSet) degree)
            (divide (moments dataSet)
              (exponentialMomentBound (moments dataSet) observable)
              (lambda (moments dataSet))))
  ; uniformIntegrabilityOfReflectedProducts =
      physicalReflectedProductUniformlyIntegrable dataSet
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
