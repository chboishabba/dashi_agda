module DASHI.Physics.YangMills.BalabanThermodynamicContinuumOSAnalyticInhabitation where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Proof-relevant thermodynamic and continuum OS inhabitation owner.
------------------------------------------------------------------------

record ThermodynamicContinuumOSAnalyticInputs : Set₁ where
  field
    -- Finite-volume normalization and Schwinger estimates.
    FiniteVolumePartitionFunctionPositive : Set
    finiteVolumePartitionFunctionPositive :
      FiniteVolumePartitionFunctionPositive
    FiniteVolumePartitionFunctionFinite : Set
    finiteVolumePartitionFunctionFinite : FiniteVolumePartitionFunctionFinite
    UniformFiniteVolumeNormalization : Set
    uniformFiniteVolumeNormalization : UniformFiniteVolumeNormalization
    UniformSchwingerMomentBound : Set
    uniformSchwingerMomentBound : UniformSchwingerMomentBound
    UniformConnectedSchwingerBound : Set
    uniformConnectedSchwingerBound : UniformConnectedSchwingerBound
    UniformDistributionOrder : Set
    uniformDistributionOrder : UniformDistributionOrder

    -- Thermodynamic compactness and extraction.
    FiniteVolumeSchwingerEquicontinuous : Set
    finiteVolumeSchwingerEquicontinuous :
      FiniteVolumeSchwingerEquicontinuous
    FiniteVolumeSchwingerPrecompact : Set
    finiteVolumeSchwingerPrecompact : FiniteVolumeSchwingerPrecompact
    ThermodynamicDiagonalSubsequence : Set
    thermodynamicDiagonalSubsequence : ThermodynamicDiagonalSubsequence
    InfiniteVolumeSubsequenceExists : Set
    infiniteVolumeSubsequenceExists : InfiniteVolumeSubsequenceExists
    VolumesTendToInfinity : Set
    volumesTendToInfinity : VolumesTendToInfinity
    SubsequenceSchwingerConverges : Set
    subsequenceSchwingerConverges : SubsequenceSchwingerConverges

    -- Thermodynamic uniqueness and boundary conditions.
    ClusterExpansionInfiniteVolumeUnique : Set
    clusterExpansionInfiniteVolumeUnique :
      ClusterExpansionInfiniteVolumeUnique
    CompatibleThermodynamicLimitsCoincide : Set
    compatibleThermodynamicLimitsCoincide :
      CompatibleThermodynamicLimitsCoincide
    InfiniteVolumeLimitUnique : Set
    infiniteVolumeLimitUnique : InfiniteVolumeLimitUnique
    BoundaryInfluenceExponentiallySmall : Set
    boundaryInfluenceExponentiallySmall : BoundaryInfluenceExponentiallySmall
    BoundaryConditionComparisonBound : Set
    boundaryConditionComparisonBound : BoundaryConditionComparisonBound
    InfiniteVolumeIndependentOfBoundaryConditions : Set
    infiniteVolumeIndependentOfBoundaryConditions :
      InfiniteVolumeIndependentOfBoundaryConditions

    -- Uniform continuum bounds.
    UniformContinuumSchwingerBounds : Set
    uniformContinuumSchwingerBounds : UniformContinuumSchwingerBounds
    UniformContinuumDistributionOrder : Set
    uniformContinuumDistributionOrder : UniformContinuumDistributionOrder
    RenormalizedObservableUniformBound : Set
    renormalizedObservableUniformBound : RenormalizedObservableUniformBound

    -- Nuclear-space compactness and continuum extraction.
    NuclearSpaceCompactnessForSchwingerFamily : Set
    nuclearSpaceCompactnessForSchwingerFamily :
      NuclearSpaceCompactnessForSchwingerFamily
    SchwingerFamilyPrecompact : Set
    schwingerFamilyPrecompact : SchwingerFamilyPrecompact
    ContinuumDiagonalMomentExtraction : Set
    continuumDiagonalMomentExtraction : ContinuumDiagonalMomentExtraction
    ContinuumSubsequenceExists : Set
    continuumSubsequenceExists : ContinuumSubsequenceExists
    LatticeSpacingsTendToZero : Set
    latticeSpacingsTendToZero : LatticeSpacingsTendToZero
    ContinuumSchwingerSubsequenceConverges : Set
    continuumSchwingerSubsequenceConverges :
      ContinuumSchwingerSubsequenceConverges

    -- Continuum uniqueness.
    RenormalizationGroupContinuumUniqueness : Set
    renormalizationGroupContinuumUniqueness :
      RenormalizationGroupContinuumUniqueness
    AllContinuumSubsequencesCoincide : Set
    allContinuumSubsequencesCoincide : AllContinuumSubsequencesCoincide
    ContinuumLimitUnique : Set
    continuumLimitUnique : ContinuumLimitUnique

    -- OS0 regularity.
    FiniteSpacingSchwingerRegularity : Set
    finiteSpacingSchwingerRegularity : FiniteSpacingSchwingerRegularity
    RegularityClosedByDistributionalLimit : Set
    regularityClosedByDistributionalLimit :
      RegularityClosedByDistributionalLimit
    OS0RegularityClosedUnderLimit : Set
    os0RegularityClosedUnderLimit : OS0RegularityClosedUnderLimit

    -- OS1 Euclidean covariance.
    LatticeSymmetryApproximatesEuclideanGroup : Set
    latticeSymmetryApproximatesEuclideanGroup :
      LatticeSymmetryApproximatesEuclideanGroup
    CovarianceDefectTendsToZero : Set
    covarianceDefectTendsToZero : CovarianceDefectTendsToZero
    LatticeCovarianceConvergesToEuclideanCovariance : Set
    latticeCovarianceConvergesToEuclideanCovariance :
      LatticeCovarianceConvergesToEuclideanCovariance

    -- OS2 reflection positivity.
    FiniteSpacingReflectionPositivity : Set
    finiteSpacingReflectionPositivity : FiniteSpacingReflectionPositivity
    ReflectedQuadraticFormsConverge : Set
    reflectedQuadraticFormsConverge : ReflectedQuadraticFormsConverge
    ReflectionPositiveConeClosed : Set
    reflectionPositiveConeClosed : ReflectionPositiveConeClosed
    ReflectionPositivityClosedUnderSchwingerLimit : Set
    reflectionPositivityClosedUnderSchwingerLimit :
      ReflectionPositivityClosedUnderSchwingerLimit

    -- OS3 permutation symmetry.
    FiniteSpacingPermutationSymmetry : Set
    finiteSpacingPermutationSymmetry : FiniteSpacingPermutationSymmetry
    PermutationActionContinuous : Set
    permutationActionContinuous : PermutationActionContinuous
    SchwingerSymmetryClosedUnderLimit : Set
    schwingerSymmetryClosedUnderLimit : SchwingerSymmetryClosedUnderLimit

    -- OS4 clustering.
    UniformConnectedClustering : Set
    uniformConnectedClustering : UniformConnectedClustering
    ClusteringRateUniformInSpacing : Set
    clusteringRateUniformInSpacing : ClusteringRateUniformInSpacing
    ConnectedProductsConverge : Set
    connectedProductsConverge : ConnectedProductsConverge
    ClusteringClosedUnderSchwingerLimit : Set
    clusteringClosedUnderSchwingerLimit : ClusteringClosedUnderSchwingerLimit

    -- OS5 growth.
    FiniteSpacingGrowthBound : Set
    finiteSpacingGrowthBound : FiniteSpacingGrowthBound
    GrowthConstantsUniformInSpacing : Set
    growthConstantsUniformInSpacing : GrowthConstantsUniformInSpacing
    GrowthControlLowerSemicontinuous : Set
    growthControlLowerSemicontinuous : GrowthControlLowerSemicontinuous
    OSGrowthBoundClosedUnderLimit : Set
    osGrowthBoundClosedUnderLimit : OSGrowthBoundClosedUnderLimit

    -- Gauge-invariant physical observables.
    LatticeGaugeInvariantObservableConverges : Set
    latticeGaugeInvariantObservableConverges :
      LatticeGaugeInvariantObservableConverges
    ContinuumObservableIndependentOfGaugeFixing : Set
    continuumObservableIndependentOfGaugeFixing :
      ContinuumObservableIndependentOfGaugeFixing
    ContinuumPhysicalObservableAlgebraClosed : Set
    continuumPhysicalObservableAlgebraClosed :
      ContinuumPhysicalObservableAlgebraClosed

    -- Nonzero and non-Gaussian interaction witnesses.
    NonzeroContinuumObservable : Set
    nonzeroContinuumObservable : NonzeroContinuumObservable
    NonzeroTwoPointLimit : Set
    nonzeroTwoPointLimit : NonzeroTwoPointLimit
    ConnectedFourPointFunctionSurvives : Set
    connectedFourPointFunctionSurvives : ConnectedFourPointFunctionSurvives
    WickFactorizationFails : Set
    wickFactorizationFails : WickFactorizationFails
    NonGaussianContinuumWitness : Set
    nonGaussianContinuumWitness : NonGaussianContinuumWitness
    ContinuumTheoryNontrivial : Set
    continuumTheoryNontrivial : ContinuumTheoryNontrivial

open ThermodynamicContinuumOSAnalyticInputs public

thermodynamicAssemblyLevel : ProofLevel
thermodynamicAssemblyLevel = machineChecked

thermodynamicAnalyticInputLevel : ProofLevel
thermodynamicAnalyticInputLevel = conditional

continuumOSAssemblyLevel : ProofLevel
continuumOSAssemblyLevel = machineChecked

continuumOSAnalyticInputLevel : ProofLevel
continuumOSAnalyticInputLevel = conjectural
