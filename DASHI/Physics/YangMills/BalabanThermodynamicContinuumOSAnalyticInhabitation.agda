module DASHI.Physics.YangMills.BalabanThermodynamicContinuumOSAnalyticInhabitation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B
open _×_ public

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,Σ_
  field
    witness : A
    proof : B witness
open Σ public

------------------------------------------------------------------------
-- Thermodynamic limit: normalization, Schwinger bounds, compactness,
-- uniqueness and boundary-condition independence.
------------------------------------------------------------------------

record ThermodynamicAnalyticInputs
    (Volume BoundaryCondition TestFunction Scalar Bound SchwingerFamily : Set)
    : Set₁ where
  field
    partitionFunction : Volume → BoundaryCondition → Scalar
    absoluteValue : Scalar → Bound
    LessEqual : Bound → Bound → Set
    transitive : ∀ {a b c} → LessEqual a b → LessEqual b c → LessEqual a c
    zeroBound : Bound
    Positive Finite : Scalar → Set

    finiteVolumePartitionFunctionPositiveInput : ∀ volume boundary →
      Positive (partitionFunction volume boundary)
    finiteVolumePartitionFunctionFiniteInput : ∀ volume boundary →
      Finite (partitionFunction volume boundary)

    UniformFiniteVolumeNormalization : Set
    uniformFiniteVolumeNormalizationInput : UniformFiniteVolumeNormalization

    schwingerMoment connectedSchwingerMoment :
      Volume → BoundaryCondition → Nat → TestFunction → Scalar
    schwingerBound connectedSchwingerBound distributionOrderBound :
      Nat → TestFunction → Bound

    uniformSchwingerMomentBoundInput : ∀ volume boundary order test →
      LessEqual
        (absoluteValue (schwingerMoment volume boundary order test))
        (schwingerBound order test)
    uniformConnectedSchwingerBoundInput : ∀ volume boundary order test →
      LessEqual
        (absoluteValue (connectedSchwingerMoment volume boundary order test))
        (connectedSchwingerBound order test)
    uniformDistributionOrderInput : ∀ volume boundary order test →
      LessEqual
        (absoluteValue (schwingerMoment volume boundary order test))
        (distributionOrderBound order test)

    FiniteVolumeSchwingerEquicontinuous FiniteVolumeSchwingerPrecompact : Set
    finiteVolumeSchwingerEquicontinuousInput :
      FiniteVolumeSchwingerEquicontinuous
    finiteVolumeSchwingerPrecompactInput : FiniteVolumeSchwingerPrecompact

    selectedVolume : Nat → Volume
    TendsToInfinity : (Nat → Volume) → Set
    selectedVolumesTendToInfinityInput : TendsToInfinity selectedVolume
    limitFamily : SchwingerFamily
    SubsequenceSchwingerConverges :
      (Nat → Volume) → SchwingerFamily → Set
    subsequenceSchwingerConvergesInput :
      SubsequenceSchwingerConverges selectedVolume limitFamily

    ThermodynamicDiagonalSubsequence : Set
    thermodynamicDiagonalSubsequenceInput : ThermodynamicDiagonalSubsequence

    CompatibleThermodynamicLimitsCoincide ClusterExpansionInfiniteVolumeUnique
      InfiniteVolumeLimitUnique : Set
    compatibleThermodynamicLimitsCoincideInput :
      CompatibleThermodynamicLimitsCoincide
    clusterExpansionInfiniteVolumeUniqueInput :
      ClusterExpansionInfiniteVolumeUnique
    infiniteVolumeLimitUniqueInput : InfiniteVolumeLimitUnique

    boundaryDifference boundaryInfluence exponentialBoundaryBound :
      BoundaryCondition → BoundaryCondition → Bound
    boundaryConditionComparisonBoundInput : ∀ left right →
      LessEqual (boundaryDifference left right) (boundaryInfluence left right)
    boundaryInfluenceExponentiallySmallInput : ∀ left right →
      LessEqual (boundaryInfluence left right) (exponentialBoundaryBound left right)

open ThermodynamicAnalyticInputs public

finiteVolumePartitionFunctionPositive = finiteVolumePartitionFunctionPositiveInput
finiteVolumePartitionFunctionFinite = finiteVolumePartitionFunctionFiniteInput
uniformFiniteVolumeNormalization = uniformFiniteVolumeNormalizationInput
uniformSchwingerMomentBound = uniformSchwingerMomentBoundInput
uniformConnectedSchwingerBound = uniformConnectedSchwingerBoundInput
uniformDistributionOrder = uniformDistributionOrderInput
finiteVolumeSchwingerEquicontinuous = finiteVolumeSchwingerEquicontinuousInput
finiteVolumeSchwingerPrecompact = finiteVolumeSchwingerPrecompactInput
thermodynamicDiagonalSubsequence = thermodynamicDiagonalSubsequenceInput
subsequenceSchwingerConverges = subsequenceSchwingerConvergesInput
clusterExpansionInfiniteVolumeUnique = clusterExpansionInfiniteVolumeUniqueInput
compatibleThermodynamicLimitsCoincide =
  compatibleThermodynamicLimitsCoincideInput
infiniteVolumeLimitUnique = infiniteVolumeLimitUniqueInput
boundaryConditionComparisonBound = boundaryConditionComparisonBoundInput
boundaryInfluenceExponentiallySmall = boundaryInfluenceExponentiallySmallInput

infiniteVolumeSubsequenceExists :
  ∀ {Volume BoundaryCondition TestFunction Scalar Bound SchwingerFamily} →
  (d : ThermodynamicAnalyticInputs
    Volume BoundaryCondition TestFunction Scalar Bound SchwingerFamily) →
  Σ (Nat → Volume) (λ subsequence →
    TendsToInfinity d subsequence ×
    SubsequenceSchwingerConverges d subsequence (limitFamily d))
infiniteVolumeSubsequenceExists d =
  selectedVolume d ,Σ
    (selectedVolumesTendToInfinityInput d , subsequenceSchwingerConvergesInput d)

infiniteVolumeIndependentOfBoundaryConditions :
  ∀ {Volume BoundaryCondition TestFunction Scalar Bound SchwingerFamily} →
  (d : ThermodynamicAnalyticInputs
    Volume BoundaryCondition TestFunction Scalar Bound SchwingerFamily) →
  ∀ left right →
  LessEqual d (boundaryDifference d left right)
    (exponentialBoundaryBound d left right)
infiniteVolumeIndependentOfBoundaryConditions d left right =
  transitive d
    (boundaryConditionComparisonBoundInput d left right)
    (boundaryInfluenceExponentiallySmallInput d left right)

------------------------------------------------------------------------
-- Continuum compactness, OS0--OS5, physical observables and interaction.
------------------------------------------------------------------------

record ContinuumOSAnalyticInputs
    (Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing : Set) : Set₁ where
  field
    latticeFamily : Spacing → SchwingerFamily
    continuumFamily : SchwingerFamily
    selectedSpacing : Nat → Spacing
    distributionOrder : Nat

    LessEqual : Bound → Bound → Set
    absoluteValue : Scalar → Bound

    UniformContinuumSchwingerBounds UniformContinuumDistributionOrder
      RenormalizedObservableUniformBound : Set
    uniformContinuumSchwingerBoundsInput : UniformContinuumSchwingerBounds
    uniformContinuumDistributionOrderInput : UniformContinuumDistributionOrder
    renormalizedObservableUniformBoundInput : RenormalizedObservableUniformBound

    NuclearSpaceCompactnessForSchwingerFamily SchwingerFamilyPrecompact
      ContinuumDiagonalMomentExtraction : Set
    nuclearSpaceCompactnessForSchwingerFamilyInput :
      NuclearSpaceCompactnessForSchwingerFamily
    schwingerFamilyPrecompactInput : SchwingerFamilyPrecompact
    continuumDiagonalMomentExtractionInput : ContinuumDiagonalMomentExtraction

    SpacingsTendToZero : (Nat → Spacing) → Set
    spacingsTendToZeroInput : SpacingsTendToZero selectedSpacing
    ContinuumSchwingerSubsequenceConverges :
      (Nat → Spacing) → SchwingerFamily → Set
    continuumSchwingerSubsequenceConvergesInput :
      ContinuumSchwingerSubsequenceConverges selectedSpacing continuumFamily

    RenormalizationGroupContinuumUniqueness AllContinuumSubsequencesCoincide
      ContinuumLimitUnique : Set
    renormalizationGroupContinuumUniquenessInput :
      RenormalizationGroupContinuumUniqueness
    allContinuumSubsequencesCoincideInput : AllContinuumSubsequencesCoincide
    continuumLimitUniqueInput : ContinuumLimitUnique

    FiniteSpacingSchwingerRegularity RegularityClosedByDistributionalLimit
      OS0RegularityClosedUnderLimit : Set
    finiteSpacingSchwingerRegularityInput : FiniteSpacingSchwingerRegularity
    regularityClosedByDistributionalLimitInput :
      RegularityClosedByDistributionalLimit
    os0RegularityClosedUnderLimitInput : OS0RegularityClosedUnderLimit

    LatticeSymmetryApproximatesEuclideanGroup CovarianceDefectTendsToZero
      LatticeCovarianceConvergesToEuclideanCovariance : Set
    latticeSymmetryApproximatesEuclideanGroupInput :
      LatticeSymmetryApproximatesEuclideanGroup
    covarianceDefectTendsToZeroInput : CovarianceDefectTendsToZero
    latticeCovarianceConvergesToEuclideanCovarianceInput :
      LatticeCovarianceConvergesToEuclideanCovariance

    FiniteSpacingReflectionPositivity ReflectedQuadraticFormsConverge
      ReflectionPositiveConeClosed ReflectionPositivityClosedUnderSchwingerLimit : Set
    finiteSpacingReflectionPositivityInput : FiniteSpacingReflectionPositivity
    reflectedQuadraticFormsConvergeInput : ReflectedQuadraticFormsConverge
    reflectionPositiveConeClosedInput : ReflectionPositiveConeClosed
    reflectionPositivityClosedUnderSchwingerLimitInput :
      ReflectionPositivityClosedUnderSchwingerLimit

    FiniteSpacingPermutationSymmetry PermutationActionContinuous
      SchwingerSymmetryClosedUnderLimit : Set
    finiteSpacingPermutationSymmetryInput : FiniteSpacingPermutationSymmetry
    permutationActionContinuousInput : PermutationActionContinuous
    schwingerSymmetryClosedUnderLimitInput : SchwingerSymmetryClosedUnderLimit

    UniformConnectedClustering ClusteringRateUniformInSpacing
      ConnectedProductsConverge ClusteringClosedUnderSchwingerLimit : Set
    uniformConnectedClusteringInput : UniformConnectedClustering
    clusteringRateUniformInSpacingInput : ClusteringRateUniformInSpacing
    connectedProductsConvergeInput : ConnectedProductsConverge
    clusteringClosedUnderSchwingerLimitInput :
      ClusteringClosedUnderSchwingerLimit

    FiniteSpacingGrowthBound GrowthConstantsUniformInSpacing
      GrowthControlLowerSemicontinuous OSGrowthBoundClosedUnderLimit : Set
    finiteSpacingGrowthBoundInput : FiniteSpacingGrowthBound
    growthConstantsUniformInSpacingInput : GrowthConstantsUniformInSpacing
    growthControlLowerSemicontinuousInput : GrowthControlLowerSemicontinuous
    osGrowthBoundClosedUnderLimitInput : OSGrowthBoundClosedUnderLimit

    LatticeGaugeInvariantObservableConverges
      ContinuumObservableIndependentOfGaugeFixing
      ContinuumPhysicalObservableAlgebraClosed : Set
    latticeGaugeInvariantObservableConvergesInput :
      LatticeGaugeInvariantObservableConverges
    continuumObservableIndependentOfGaugeFixingInput :
      ContinuumObservableIndependentOfGaugeFixing
    continuumPhysicalObservableAlgebraClosedInput :
      ContinuumPhysicalObservableAlgebraClosed

    NonzeroContinuumObservable NonzeroTwoPointLimit
      ConnectedFourPointFunctionSurvives WickFactorizationFails : Set
    nonzeroContinuumObservableInput : NonzeroContinuumObservable
    nonzeroTwoPointLimitInput : NonzeroTwoPointLimit
    connectedFourPointFunctionSurvivesInput : ConnectedFourPointFunctionSurvives
    wickFactorizationFailsInput : WickFactorizationFails

open ContinuumOSAnalyticInputs public

uniformContinuumSchwingerBounds = uniformContinuumSchwingerBoundsInput
uniformContinuumDistributionOrder = uniformContinuumDistributionOrderInput
renormalizedObservableUniformBound = renormalizedObservableUniformBoundInput
nuclearSpaceCompactnessForSchwingerFamily =
  nuclearSpaceCompactnessForSchwingerFamilyInput
schwingerFamilyPrecompact = schwingerFamilyPrecompactInput
continuumDiagonalMomentExtraction = continuumDiagonalMomentExtractionInput
continuumSchwingerSubsequenceConverges =
  continuumSchwingerSubsequenceConvergesInput
renormalizationGroupContinuumUniqueness =
  renormalizationGroupContinuumUniquenessInput
allContinuumSubsequencesCoincide = allContinuumSubsequencesCoincideInput
continuumLimitUnique = continuumLimitUniqueInput
finiteSpacingSchwingerRegularity = finiteSpacingSchwingerRegularityInput
regularityClosedByDistributionalLimit =
  regularityClosedByDistributionalLimitInput
os0RegularityClosedUnderLimit = os0RegularityClosedUnderLimitInput
latticeSymmetryApproximatesEuclideanGroup =
  latticeSymmetryApproximatesEuclideanGroupInput
covarianceDefectTendsToZero = covarianceDefectTendsToZeroInput
latticeCovarianceConvergesToEuclideanCovariance =
  latticeCovarianceConvergesToEuclideanCovarianceInput
finiteSpacingReflectionPositivity = finiteSpacingReflectionPositivityInput
reflectedQuadraticFormsConverge = reflectedQuadraticFormsConvergeInput
reflectionPositiveConeClosed = reflectionPositiveConeClosedInput
reflectionPositivityClosedUnderSchwingerLimit =
  reflectionPositivityClosedUnderSchwingerLimitInput
finiteSpacingPermutationSymmetry = finiteSpacingPermutationSymmetryInput
permutationActionContinuous = permutationActionContinuousInput
schwingerSymmetryClosedUnderLimit = schwingerSymmetryClosedUnderLimitInput
uniformConnectedClustering = uniformConnectedClusteringInput
clusteringRateUniformInSpacing = clusteringRateUniformInSpacingInput
connectedProductsConverge = connectedProductsConvergeInput
clusteringClosedUnderSchwingerLimit = clusteringClosedUnderSchwingerLimitInput
finiteSpacingGrowthBound = finiteSpacingGrowthBoundInput
growthConstantsUniformInSpacing = growthConstantsUniformInSpacingInput
growthControlLowerSemicontinuous = growthControlLowerSemicontinuousInput
osGrowthBoundClosedUnderLimit = osGrowthBoundClosedUnderLimitInput
latticeGaugeInvariantObservableConverges =
  latticeGaugeInvariantObservableConvergesInput
continuumObservableIndependentOfGaugeFixing =
  continuumObservableIndependentOfGaugeFixingInput
continuumPhysicalObservableAlgebraClosed =
  continuumPhysicalObservableAlgebraClosedInput
nonzeroContinuumObservable = nonzeroContinuumObservableInput
nonzeroTwoPointLimit = nonzeroTwoPointLimitInput
connectedFourPointFunctionSurvives = connectedFourPointFunctionSurvivesInput
wickFactorizationFails = wickFactorizationFailsInput

continuumSubsequenceExists :
  ∀ {Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing} →
  (d : ContinuumOSAnalyticInputs
    Spacing TestFunction Observable Scalar Bound Distribution
    SchwingerFamily GaugeFixing) →
  Σ (Nat → Spacing) (λ subsequence →
    SpacingsTendToZero d subsequence ×
    ContinuumSchwingerSubsequenceConverges d subsequence (continuumFamily d))
continuumSubsequenceExists d =
  selectedSpacing d ,Σ
    (spacingsTendToZeroInput d , continuumSchwingerSubsequenceConvergesInput d)

record NonGaussianContinuumWitness
    {Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing : Set}
    (d : ContinuumOSAnalyticInputs
      Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing) : Set where
  constructor nonGaussianWitness
  field
    connectedFourPoint : ConnectedFourPointFunctionSurvives d
    failureOfWick : WickFactorizationFails d
open NonGaussianContinuumWitness public

nonGaussianContinuumWitness :
  ∀ {Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing} →
  (d : ContinuumOSAnalyticInputs
    Spacing TestFunction Observable Scalar Bound Distribution
    SchwingerFamily GaugeFixing) →
  NonGaussianContinuumWitness d
nonGaussianContinuumWitness d = nonGaussianWitness
  (connectedFourPointFunctionSurvivesInput d)
  (wickFactorizationFailsInput d)

record ContinuumTheoryNontrivial
    {Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing : Set}
    (d : ContinuumOSAnalyticInputs
      Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing) : Set where
  constructor interactingContinuum
  field
    nonzeroObservable : NonzeroContinuumObservable d
    nonzeroTwoPoint : NonzeroTwoPointLimit d
    nonGaussian : NonGaussianContinuumWitness d
open ContinuumTheoryNontrivial public

continuumTheoryNontrivial :
  ∀ {Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing} →
  (d : ContinuumOSAnalyticInputs
    Spacing TestFunction Observable Scalar Bound Distribution
    SchwingerFamily GaugeFixing) →
  ContinuumTheoryNontrivial d
continuumTheoryNontrivial d = interactingContinuum
  (nonzeroContinuumObservableInput d)
  (nonzeroTwoPointLimitInput d)
  (nonGaussianContinuumWitness d)

record ThermodynamicContinuumOSCertificate
    (Volume BoundaryCondition TestFunction Observable Scalar Bound Distribution
      SchwingerFamily Spacing GaugeFixing : Set) : Set₁ where
  field
    thermodynamic : ThermodynamicAnalyticInputs
      Volume BoundaryCondition TestFunction Scalar Bound SchwingerFamily
    continuum : ContinuumOSAnalyticInputs
      Spacing TestFunction Observable Scalar Bound Distribution
      SchwingerFamily GaugeFixing

open ThermodynamicContinuumOSCertificate public

thermodynamicExtractionAssemblyLevel : ProofLevel
thermodynamicExtractionAssemblyLevel = machineChecked

thermodynamicAnalyticInputLevel : ProofLevel
thermodynamicAnalyticInputLevel = conditional

continuumExtractionAssemblyLevel : ProofLevel
continuumExtractionAssemblyLevel = machineChecked

continuumAnalyticInputLevel : ProofLevel
continuumAnalyticInputLevel = conjectural

osLimitAssemblyLevel : ProofLevel
osLimitAssemblyLevel = machineChecked

osLimitAnalyticInputLevel : ProofLevel
osLimitAnalyticInputLevel = conjectural

continuumInteractionInputLevel : ProofLevel
continuumInteractionInputLevel = conjectural
