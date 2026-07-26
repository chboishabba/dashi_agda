module DASHI.Physics.YangMills.BalabanClayP5ContinuumMassGapExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- P5A--P5C: all-scale finite-volume measures and their two limits.
------------------------------------------------------------------------

record AllScaleFiniteVolumeConstruction
    (Scale Volume Configuration Observable Measure Value Bound : Set) : Set₁ where
  field
    latticeSpacing : Scale → Bound
    finiteVolumeRegion : Volume → Set
    finiteMeasure : Scale → Volume → Measure
    observableValue : Observable → Configuration → Value
    expectation : Measure → Observable → Value

    Normalized Positive GaugeInvariant ReflectionPositive : Measure → Set

    finiteNormalized : ∀ scale volume → Normalized (finiteMeasure scale volume)
    finitePositive : ∀ scale volume → Positive (finiteMeasure scale volume)
    finiteGaugeInvariant : ∀ scale volume →
      GaugeInvariant (finiteMeasure scale volume)
    finiteReflectionPositive : ∀ scale volume →
      ReflectionPositive (finiteMeasure scale volume)

    ConstantsUniformInScaleAndVolume : Set
    uniformConstants : ConstantsUniformInScaleAndVolume

open AllScaleFiniteVolumeConstruction public

record ThermodynamicLimit
    {Scale Volume Configuration Observable Measure Value Bound : Set}
    (finite : AllScaleFiniteVolumeConstruction
      Scale Volume Configuration Observable Measure Value Bound)
    (InfiniteVolumeMeasure : Set) : Set₁ where
  field
    infiniteVolumeMeasure : Scale → InfiniteVolumeMeasure
    volumeTendsToInfinity : Nat → Volume
    expectationInfinite : Scale → Observable → Value
    Converges : (Nat → Value) → Value → Set

    observableThermodynamicLimit : ∀ scale observable →
      Converges
        (λ n → expectation finite
          (finiteMeasure finite scale (volumeTendsToInfinity n)) observable)
        (expectationInfinite scale observable)

    BoundaryConditionIndependent : Set
    thermodynamicBoundaryIndependence : BoundaryConditionIndependent

open ThermodynamicLimit public

record ContinuumLimit
    {Scale Volume Configuration Observable Measure Value Bound : Set}
    {InfiniteVolumeMeasure : Set}
    (finite : AllScaleFiniteVolumeConstruction
      Scale Volume Configuration Observable Measure Value Bound)
    (thermodynamic : ThermodynamicLimit finite InfiniteVolumeMeasure)
    (ContinuumMeasure ContinuumObservable ContinuumValue : Set) : Set₁ where
  field
    ultravioletSequence : Nat → Scale
    continuumMeasure : ContinuumMeasure
    renormalizeObservable : ContinuumObservable → Nat → Observable
    continuumExpectation : ContinuumMeasure → ContinuumObservable → ContinuumValue
    embedFiniteValue : Value → ContinuumValue
    Converges : (Nat → ContinuumValue) → ContinuumValue → Set

    observableContinuumLimit : ∀ observable →
      Converges
        (λ n → embedFiniteValue
          (expectationInfinite thermodynamic
            (ultravioletSequence n)
            (renormalizeObservable observable n)))
        (continuumExpectation continuumMeasure observable)

open ContinuumLimit public

------------------------------------------------------------------------
-- P5D: the complete Osterwalder--Schrader surface on the actual limit.
------------------------------------------------------------------------

record OsterwalderSchraderLimit
    (ContinuumMeasure SchwingerFamily : Set) : Set₁ where
  field
    schwingerFunctions : ContinuumMeasure → SchwingerFamily

    EuclideanCovariant ReflectionPositive Symmetric Tempered Regular
      Clustered : SchwingerFamily → Set

    euclideanCovariance : ∀ measure →
      EuclideanCovariant (schwingerFunctions measure)
    reflectionPositivity : ∀ measure →
      ReflectionPositive (schwingerFunctions measure)
    symmetry : ∀ measure → Symmetric (schwingerFunctions measure)
    temperedness : ∀ measure → Tempered (schwingerFunctions measure)
    regularity : ∀ measure → Regular (schwingerFunctions measure)
    clustering : ∀ measure → Clustered (schwingerFunctions measure)

open OsterwalderSchraderLimit public

------------------------------------------------------------------------
-- P5E: physical-unit clustering and spectral-gap reconstruction.
------------------------------------------------------------------------

record PhysicalClusteringSurvival
    (Scale Observable Distance Bound Correlation : Set) : Set₁ where
  field
    latticeSpacing latticeMass : Scale → Bound
    physicalMass prefactor : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    Positive : Bound → Set

    latticeDistance : Scale → Distance → Distance
    connectedCorrelation : Scale → Observable → Observable → Distance → Correlation
    correlationMajorant : Bound → Distance → Correlation
    CorrelationBound : Correlation → Correlation → Set

    physicalMassPositive : Positive physicalMass

    latticeMassDominatesPhysicalScale : ∀ scale →
      LessEqual
        (multiply physicalMass (latticeSpacing scale))
        (latticeMass scale)

    latticeExponentialClustering : ∀ scale left right distance →
      CorrelationBound
        (connectedCorrelation scale left right distance)
        (correlationMajorant (latticeMass scale)
          (latticeDistance scale distance))

    exponentConversion : ∀ scale distance →
      CorrelationBound
        (correlationMajorant (latticeMass scale)
          (latticeDistance scale distance))
        (correlationMajorant physicalMass distance)

    correlationTransitive : ∀ {left middle right} →
      CorrelationBound left middle → CorrelationBound middle right →
      CorrelationBound left right

open PhysicalClusteringSurvival public

physicalConnectedCorrelationBound :
  ∀ {Scale Observable Distance Bound Correlation}
    (dataSet : PhysicalClusteringSurvival
      Scale Observable Distance Bound Correlation)
    scale left right distance →
  CorrelationBound dataSet
    (connectedCorrelation dataSet scale left right distance)
    (correlationMajorant dataSet (physicalMass dataSet) distance)
physicalConnectedCorrelationBound dataSet scale left right distance =
  correlationTransitive dataSet
    (latticeExponentialClustering dataSet scale left right distance)
    (exponentConversion dataSet scale distance)

record OSSpectralReconstruction
    (SchwingerFamily Hilbert Hamiltonian Vector Energy Bound : Set) : Set₁ where
  field
    reconstructHilbert : SchwingerFamily → Hilbert
    reconstructHamiltonian : SchwingerFamily → Hamiltonian
    vacuum : SchwingerFamily → Vector
    spectrum : Hamiltonian → Energy → Set
    energyGap : SchwingerFamily → Bound
    Positive : Bound → Set
    ExponentialClustering : SchwingerFamily → Bound → Set

    ReconstructionExact : Set
    reconstruction : ReconstructionExact

    exponentialClusteringImpliesGap : ∀ schwinger mass →
      ExponentialClustering schwinger mass →
      Positive mass →
      Positive (energyGap schwinger)

open OSSpectralReconstruction public

------------------------------------------------------------------------
-- P5F: explicit nontriviality witness.
------------------------------------------------------------------------

record InteractingNontriviality
    (ContinuumMeasure Observable Value : Set) : Set₁ where
  field
    expectation : ContinuumMeasure → Observable → Value
    interactionObservable gaussianComparisonObservable : Observable
    Distinct : Value → Value → Set

    interactingObservableDiffersFromGaussian : ∀ measure →
      Distinct
        (expectation measure interactionObservable)
        (expectation measure gaussianComparisonObservable)

    NotConcentratedAtIdentity : ContinuumMeasure → Set
    NotUltralocalProduct : ContinuumMeasure → Set
    NotZeroAfterRenormalization : ContinuumMeasure → Set

    identityNonconcentration : ∀ measure → NotConcentratedAtIdentity measure
    ultralocalProductExcluded : ∀ measure → NotUltralocalProduct measure
    renormalizedFieldNonzero : ∀ measure → NotZeroAfterRenormalization measure

open InteractingNontriviality public

------------------------------------------------------------------------
-- Complete P5 endpoint package.  The continuum clustering input is explicitly
-- linked to OS reconstruction, yielding a positive spectral-gap conclusion.
------------------------------------------------------------------------

record PhysicalP5MassGapCertificate
    (Scale Volume Configuration Observable Measure Value Bound
     InfiniteVolumeMeasure ContinuumMeasure ContinuumObservable ContinuumValue
     SchwingerFamily Hilbert Hamiltonian Vector Energy Distance Correlation : Set)
    : Set₁ where
  field
    finiteConstruction : AllScaleFiniteVolumeConstruction
      Scale Volume Configuration Observable Measure Value Bound
    thermodynamicLimit : ThermodynamicLimit
      finiteConstruction InfiniteVolumeMeasure
    continuumLimit : ContinuumLimit
      finiteConstruction thermodynamicLimit
      ContinuumMeasure ContinuumObservable ContinuumValue
    osLimit : OsterwalderSchraderLimit ContinuumMeasure SchwingerFamily
    physicalClustering : PhysicalClusteringSurvival
      Scale Observable Distance Bound Correlation
    spectralReconstruction : OSSpectralReconstruction
      SchwingerFamily Hilbert Hamiltonian Vector Energy Bound
    nontriviality : InteractingNontriviality
      ContinuumMeasure ContinuumObservable ContinuumValue

    continuumExponentialClustering :
      ExponentialClustering spectralReconstruction
        (schwingerFunctions osLimit (ContinuumLimit.continuumMeasure continuumLimit))
        (physicalMass physicalClustering)

    positivePhysicalSpectralGap :
      Positive spectralReconstruction
        (energyGap spectralReconstruction
          (schwingerFunctions osLimit
            (ContinuumLimit.continuumMeasure continuumLimit)))
    positivePhysicalSpectralGap =
      exponentialClusteringImpliesGap spectralReconstruction
        (schwingerFunctions osLimit
          (ContinuumLimit.continuumMeasure continuumLimit))
        (physicalMass physicalClustering)
        continuumExponentialClustering
        (physicalMassPositive physicalClustering)

open PhysicalP5MassGapCertificate public

p5PhysicalClusteringScaleConversionLevel : ProofLevel
p5PhysicalClusteringScaleConversionLevel = machineChecked

p5ClusteringToSpectralGapAssemblyLevel : ProofLevel
p5ClusteringToSpectralGapAssemblyLevel = machineChecked

p5FiniteMeasureConstructionProducerLevel : ProofLevel
p5FiniteMeasureConstructionProducerLevel = conditional

p5ThermodynamicLimitProducerLevel : ProofLevel
p5ThermodynamicLimitProducerLevel = conditional

p5ContinuumLimitProducerLevel : ProofLevel
p5ContinuumLimitProducerLevel = conditional

p5OsterwalderSchraderProducerLevel : ProofLevel
p5OsterwalderSchraderProducerLevel = conditional

p5SpectralGapReconstructionProducerLevel : ProofLevel
p5SpectralGapReconstructionProducerLevel = conditional

p5NontrivialityProducerLevel : ProofLevel
p5NontrivialityProducerLevel = conditional
