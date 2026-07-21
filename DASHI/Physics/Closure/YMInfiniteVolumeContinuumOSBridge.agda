module DASHI.Physics.Closure.YMInfiniteVolumeContinuumOSBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Infinite-volume and continuum-limit theorem interface.
--
-- This module is intentionally a bridge layer.  It makes every implication
-- and every required uniformity hypothesis explicit, rather than promoting
-- compactness, uniqueness, OS closure, or interacting nontriviality from a
-- slogan.  In particular, continuum nontriviality requires both a nonzero
-- witness and a non-Gaussian connected-correlation witness.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

analyticInfiniteVolumeLimitDerivedInRepo : Bool
analyticInfiniteVolumeLimitDerivedInRepo = false

analyticContinuumOSLimitDerivedInRepo : Bool
analyticContinuumOSLimitDerivedInRepo = false

interactingContinuumTheoryDerivedInRepo : Bool
interactingContinuumTheoryDerivedInRepo = false

record FiniteVolumeSchwingerFamily : Set where
  constructor mkFiniteVolumeSchwingerFamily
  field
    volumeIndex : Nat
    boundaryCondition : String
    partitionFunction : String
    schwingerMoments : String

record VolumeUniformNormalizationEvidence
  (family : FiniteVolumeSchwingerFamily) : Set where
  constructor mkVolumeUniformNormalizationEvidence
  field
    normalizedPartitionFunction : String
    normalizationIndependentOfVolume : String

uniformFiniteVolumeNormalization :
  (family : FiniteVolumeSchwingerFamily) →
  VolumeUniformNormalizationEvidence family →
  VolumeUniformNormalizationEvidence family
uniformFiniteVolumeNormalization family evidence = evidence

record VolumeUniformSchwingerBoundEvidence
  (family : FiniteVolumeSchwingerFamily) : Set where
  constructor mkVolumeUniformSchwingerBoundEvidence
  field
    testFunctionSeminorm : String
    momentOrder : Nat
    commonMomentConstant : String
    boundUniformInVolume : String

uniformSchwingerMomentBound :
  (family : FiniteVolumeSchwingerFamily) →
  VolumeUniformSchwingerBoundEvidence family →
  VolumeUniformSchwingerBoundEvidence family
uniformSchwingerMomentBound family evidence = evidence

record ThermodynamicPrecompactnessEvidence
  (family : FiniteVolumeSchwingerFamily) : Set where
  constructor mkThermodynamicPrecompactnessEvidence
  field
    uniformNormalization : VolumeUniformNormalizationEvidence family
    uniformMoments : VolumeUniformSchwingerBoundEvidence family
    commonDistributionSpace : String
    tightnessOrEquicontinuity : String
    diagonalExtractionPrinciple : String

finiteVolumeSchwingerPrecompact :
  (family : FiniteVolumeSchwingerFamily) →
  ThermodynamicPrecompactnessEvidence family →
  ThermodynamicPrecompactnessEvidence family
finiteVolumeSchwingerPrecompact family evidence = evidence

record InfiniteVolumeSubsequenceEvidence
  (family : FiniteVolumeSchwingerFamily) : Set where
  constructor mkInfiniteVolumeSubsequenceEvidence
  field
    precompactness : ThermodynamicPrecompactnessEvidence family
    selectedVolumes : String
    volumesTendToInfinity : String
    limitingSchwingerFamily : String
    subsequenceConvergence : String

infiniteVolumeSubsequenceExists :
  (family : FiniteVolumeSchwingerFamily) →
  InfiniteVolumeSubsequenceEvidence family →
  InfiniteVolumeSubsequenceEvidence family
infiniteVolumeSubsequenceExists family evidence = evidence

record InfiniteVolumeUniquenessEvidence
  (family : FiniteVolumeSchwingerFamily) : Set where
  constructor mkInfiniteVolumeUniquenessEvidence
  field
    subsequence : InfiniteVolumeSubsequenceEvidence family
    clusterExpansionUniqueness : String
    compatibleLimitsCoincide : String

infiniteVolumeLimitUnique :
  (family : FiniteVolumeSchwingerFamily) →
  InfiniteVolumeUniquenessEvidence family →
  InfiniteVolumeUniquenessEvidence family
infiniteVolumeLimitUnique family evidence = evidence

record BoundaryConditionIndependenceEvidence
  (family : FiniteVolumeSchwingerFamily) : Set where
  constructor mkBoundaryConditionIndependenceEvidence
  field
    uniqueLimit : InfiniteVolumeUniquenessEvidence family
    boundaryInfluenceDecay : String
    comparisonAcrossBoundaryConditions : String
    sameInfiniteVolumeSchwingerFamily : String

infiniteVolumeIndependentOfBoundaryConditions :
  (family : FiniteVolumeSchwingerFamily) →
  BoundaryConditionIndependenceEvidence family →
  BoundaryConditionIndependenceEvidence family
infiniteVolumeIndependentOfBoundaryConditions family evidence = evidence

------------------------------------------------------------------------
-- Continuum family and compactness.

record LatticeSpacingSchwingerFamily : Set where
  constructor mkLatticeSpacingSchwingerFamily
  field
    latticeSpacingIndex : Nat
    latticeSpacingDescription : String
    infiniteVolumeInput : String
    renormalizedSchwingerDistributions : String

record UniformContinuumSchwingerBoundsEvidence
  (family : LatticeSpacingSchwingerFamily) : Set where
  constructor mkUniformContinuumSchwingerBoundsEvidence
  field
    commonTestFunctionSpace : String
    commonDistributionOrder : Nat
    commonSeminormBound : String
    boundUniformInLatticeSpacing : String

uniformContinuumSchwingerBounds :
  (family : LatticeSpacingSchwingerFamily) →
  UniformContinuumSchwingerBoundsEvidence family →
  UniformContinuumSchwingerBoundsEvidence family
uniformContinuumSchwingerBounds family evidence = evidence

record ContinuumPrecompactnessEvidence
  (family : LatticeSpacingSchwingerFamily) : Set where
  constructor mkContinuumPrecompactnessEvidence
  field
    uniformBounds : UniformContinuumSchwingerBoundsEvidence family
    nuclearSpaceCompactness : String
    diagonalMomentExtraction : String

schwingerFamilyPrecompact :
  (family : LatticeSpacingSchwingerFamily) →
  ContinuumPrecompactnessEvidence family →
  ContinuumPrecompactnessEvidence family
schwingerFamilyPrecompact family evidence = evidence

record ContinuumSubsequenceEvidence
  (family : LatticeSpacingSchwingerFamily) : Set where
  constructor mkContinuumSubsequenceEvidence
  field
    precompactness : ContinuumPrecompactnessEvidence family
    selectedSpacings : String
    spacingsTendToZero : String
    continuumSchwingerFamily : String
    subsequenceConvergence : String

continuumSubsequenceExists :
  (family : LatticeSpacingSchwingerFamily) →
  ContinuumSubsequenceEvidence family →
  ContinuumSubsequenceEvidence family
continuumSubsequenceExists family evidence = evidence

record ContinuumLimitUniquenessEvidence
  (family : LatticeSpacingSchwingerFamily) : Set where
  constructor mkContinuumLimitUniquenessEvidence
  field
    subsequence : ContinuumSubsequenceEvidence family
    renormalizationGroupUniqueness : String
    allContinuumSubsequencesCoincide : String

continuumLimitUnique :
  (family : LatticeSpacingSchwingerFamily) →
  ContinuumLimitUniquenessEvidence family →
  ContinuumLimitUniquenessEvidence family
continuumLimitUnique family evidence = evidence

------------------------------------------------------------------------
-- Closure of Osterwalder-Schrader properties under the selected limit.

record OS0RegularityLimitEvidence : Set where
  constructor mkOS0RegularityLimitEvidence
  field
    finiteSpacingRegularity : String
    uniformDistributionOrder : String
    regularityClosedByConvergence : String

os0RegularityClosedUnderLimit :
  OS0RegularityLimitEvidence → OS0RegularityLimitEvidence
os0RegularityClosedUnderLimit evidence = evidence

record OS1EuclideanCovarianceLimitEvidence : Set where
  constructor mkOS1EuclideanCovarianceLimitEvidence
  field
    latticeCovariance : String
    latticeSymmetryApproximatesEuclideanGroup : String
    covarianceErrorTendsToZero : String
    continuumEuclideanCovariance : String

latticeCovarianceConvergesToEuclideanCovariance :
  OS1EuclideanCovarianceLimitEvidence →
  OS1EuclideanCovarianceLimitEvidence
latticeCovarianceConvergesToEuclideanCovariance evidence = evidence

record OS2ReflectionPositivityLimitEvidence : Set where
  constructor mkOS2ReflectionPositivityLimitEvidence
  field
    finiteSpacingReflectionPositivity : String
    reflectedQuadraticFormsConverge : String
    positivityConeClosed : String

reflectionPositivityClosedUnderSchwingerLimit :
  OS2ReflectionPositivityLimitEvidence →
  OS2ReflectionPositivityLimitEvidence
reflectionPositivityClosedUnderSchwingerLimit evidence = evidence

record OS3PermutationSymmetryLimitEvidence : Set where
  constructor mkOS3PermutationSymmetryLimitEvidence
  field
    finiteSpacingPermutationSymmetry : String
    permutationActionContinuous : String
    symmetryPassesToLimit : String

schwingerSymmetryClosedUnderLimit :
  OS3PermutationSymmetryLimitEvidence →
  OS3PermutationSymmetryLimitEvidence
schwingerSymmetryClosedUnderLimit evidence = evidence

record OS4ClusteringLimitEvidence : Set where
  constructor mkOS4ClusteringLimitEvidence
  field
    uniformConnectedClustering : String
    decayRateUniformInSpacing : String
    connectedProductsConverge : String
    continuumClustering : String

clusteringClosedUnderSchwingerLimit :
  OS4ClusteringLimitEvidence → OS4ClusteringLimitEvidence
clusteringClosedUnderSchwingerLimit evidence = evidence

record OS5GrowthLimitEvidence : Set where
  constructor mkOS5GrowthLimitEvidence
  field
    finiteSpacingGrowthBound : String
    growthConstantsUniformInSpacing : String
    lowerSemicontinuityOfGrowthControl : String

osGrowthBoundClosedUnderLimit :
  OS5GrowthLimitEvidence → OS5GrowthLimitEvidence
osGrowthBoundClosedUnderLimit evidence = evidence

------------------------------------------------------------------------
-- Interacting nontriviality.
--
-- A merely nonzero two-point function is insufficient: a generalized free or
-- Gaussian theory can have one.  The required package therefore carries a
-- nonzero observable and a genuinely non-Gaussian connected cumulant (or an
-- equivalent failure of Wick factorisation), together with compatibility with
-- the same unique continuum limit.

record NonzeroContinuumWitness : Set where
  constructor mkNonzeroContinuumWitness
  field
    observable : String
    expectationOrTwoPointValue : String
    valueIsNonzero : String

record NonGaussianContinuumWitness : Set where
  constructor mkNonGaussianContinuumWitness
  field
    observableTuple : String
    connectedCumulantOrder : Nat
    connectedCumulantValue : String
    cumulantIsNonzero : String
    wickFactorisationFails : String

record ContinuumTheoryNontrivialEvidence : Set where
  constructor mkContinuumTheoryNontrivialEvidence
  field
    uniqueContinuumLimit : String
    nonzeroWitness : NonzeroContinuumWitness
    nonGaussianWitness : NonGaussianContinuumWitness
    witnessesSurviveRenormalizedLimit : String
    gaugeInvariantInterpretation : String

continuumTheoryNontrivial :
  ContinuumTheoryNontrivialEvidence →
  ContinuumTheoryNontrivialEvidence
continuumTheoryNontrivial evidence = evidence

continuumNontrivialityRulesOutZeroTheory :
  ContinuumTheoryNontrivialEvidence → NonzeroContinuumWitness
continuumNontrivialityRulesOutZeroTheory evidence =
  ContinuumTheoryNontrivialEvidence.nonzeroWitness evidence

continuumNontrivialityRulesOutGaussianTheory :
  ContinuumTheoryNontrivialEvidence → NonGaussianContinuumWitness
continuumNontrivialityRulesOutGaussianTheory evidence =
  ContinuumTheoryNontrivialEvidence.nonGaussianWitness evidence

------------------------------------------------------------------------
-- One explicit all-gates package.  This avoids accidentally invoking the OS
-- closure statements without the thermodynamic and continuum uniqueness
-- hypotheses that make them meaningful.

record InfiniteVolumeContinuumOSPackage : Set₁ where
  constructor mkInfiniteVolumeContinuumOSPackage
  field
    finiteVolumeFamily : FiniteVolumeSchwingerFamily
    volumeNormalization :
      VolumeUniformNormalizationEvidence finiteVolumeFamily
    volumeMomentBound :
      VolumeUniformSchwingerBoundEvidence finiteVolumeFamily
    thermodynamicPrecompactness :
      ThermodynamicPrecompactnessEvidence finiteVolumeFamily
    thermodynamicSubsequence :
      InfiniteVolumeSubsequenceEvidence finiteVolumeFamily
    thermodynamicUniqueness :
      InfiniteVolumeUniquenessEvidence finiteVolumeFamily
    boundaryIndependence :
      BoundaryConditionIndependenceEvidence finiteVolumeFamily

    spacingFamily : LatticeSpacingSchwingerFamily
    continuumBounds :
      UniformContinuumSchwingerBoundsEvidence spacingFamily
    continuumPrecompactness :
      ContinuumPrecompactnessEvidence spacingFamily
    continuumSubsequence :
      ContinuumSubsequenceEvidence spacingFamily
    continuumUniqueness :
      ContinuumLimitUniquenessEvidence spacingFamily

    os0 : OS0RegularityLimitEvidence
    os1 : OS1EuclideanCovarianceLimitEvidence
    os2 : OS2ReflectionPositivityLimitEvidence
    os3 : OS3PermutationSymmetryLimitEvidence
    os4 : OS4ClusteringLimitEvidence
    os5 : OS5GrowthLimitEvidence
    interactingNontriviality : ContinuumTheoryNontrivialEvidence

record YMInfiniteVolumeContinuumOSBridgeReceipt : Set₁ where
  constructor mkYMInfiniteVolumeContinuumOSBridgeReceipt
  field
    theoremPackage : InfiniteVolumeContinuumOSPackage
    analyticInfiniteVolumeStillOpen :
      analyticInfiniteVolumeLimitDerivedInRepo ≡ false
    analyticContinuumOSStillOpen :
      analyticContinuumOSLimitDerivedInRepo ≡ false
    interactingDerivationStillOpen :
      interactingContinuumTheoryDerivedInRepo ≡ false
    promotionRemainsClosed : clayYangMillsPromoted ≡ false

canonicalBridgeStatus :
  analyticInfiniteVolumeLimitDerivedInRepo ≡ false
canonicalBridgeStatus = refl

canonicalContinuumStatus :
  analyticContinuumOSLimitDerivedInRepo ≡ false
canonicalContinuumStatus = refl

canonicalInteractionStatus :
  interactingContinuumTheoryDerivedInRepo ≡ false
canonicalInteractionStatus = refl

canonicalPromotionStatus : clayYangMillsPromoted ≡ false
canonicalPromotionStatus = refl
