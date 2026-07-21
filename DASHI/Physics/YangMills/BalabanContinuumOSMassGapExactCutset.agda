module DASHI.Physics.YangMills.BalabanContinuumOSMassGapExactCutset where

------------------------------------------------------------------------
-- Exact theorem-facing cutset for the continuum limit, OS0--OS5,
-- reconstruction, and the two physical mass-gap routes.
--
-- This module does not disguise the genuinely analytic inputs as conclusions.
-- It gives each requested statement a precise proof-relevant type, prevents
-- witness mixing by packaging one cutoff family throughout, and machine-checks
-- every extraction and final assembly from those inputs.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as Production

------------------------------------------------------------------------
-- L1--L4. Uniform Schwinger bounds, compactness, subsequence, uniqueness.

record ContinuumExtractionData
    (Cutoff Observable Test Scalar Bound Subsequence : Set) : Set₁ where
  field
    cutoffSchwinger : Cutoff → Observable → Test → Scalar
    renormalizedObservable : Cutoff → Observable → Observable
    distributionOrder : Bound
    observableBound : Observable → Bound

    UniformBound : Scalar → Bound → Set
    DistributionOrderAtMost : (Observable → Test → Scalar) → Bound → Set
    Precompact : (Cutoff → Observable → Test → Scalar) → Set
    TendsToZeroSpacing : Cutoff → Set
    IsSubsequence : Subsequence → Set
    ConvergesAlong : Subsequence → (Observable → Test → Scalar) → Set
    EqualSchwingerFamily :
      (Observable → Test → Scalar) →
      (Observable → Test → Scalar) → Set

    uniformContinuumSchwingerBoundsWitness :
      ∀ cutoff observable test →
      UniformBound
        (cutoffSchwinger cutoff observable test)
        (observableBound observable)

    uniformContinuumDistributionOrderWitness :
      ∀ cutoff →
      DistributionOrderAtMost (cutoffSchwinger cutoff) distributionOrder

    renormalizedObservableUniformBoundWitness :
      ∀ cutoff observable test →
      UniformBound
        (cutoffSchwinger cutoff (renormalizedObservable cutoff observable) test)
        (observableBound observable)

    nuclearSpaceCompactnessForSchwingerFamilyWitness :
      (∀ cutoff →
        DistributionOrderAtMost (cutoffSchwinger cutoff) distributionOrder) →
      Precompact cutoffSchwinger

    continuumDiagonalMomentExtractionWitness :
      Precompact cutoffSchwinger →
      Subsequence

    continuumSubsequenceIsSubsequence :
      IsSubsequence
        (continuumDiagonalMomentExtractionWitness
          (nuclearSpaceCompactnessForSchwingerFamilyWitness
            uniformContinuumDistributionOrderWitness))

    latticeSpacingsTendToZeroWitness : ∀ cutoff → TendsToZeroSpacing cutoff

    continuumSchwingerSubsequenceLimit : Observable → Test → Scalar

    continuumSchwingerSubsequenceConvergesWitness :
      ConvergesAlong
        (continuumDiagonalMomentExtractionWitness
          (nuclearSpaceCompactnessForSchwingerFamilyWitness
            uniformContinuumDistributionOrderWitness))
        continuumSchwingerSubsequenceLimit

    renormalizationGroupContinuumUniquenessWitness :
      ∀ first second →
      IsSubsequence first →
      IsSubsequence second →
      ∀ firstLimit secondLimit →
      ConvergesAlong first firstLimit →
      ConvergesAlong second secondLimit →
      EqualSchwingerFamily firstLimit secondLimit

open ContinuumExtractionData public

uniformContinuumSchwingerBounds :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ cutoff observable test →
  UniformBound dataSet
    (cutoffSchwinger dataSet cutoff observable test)
    (observableBound dataSet observable)
uniformContinuumSchwingerBounds = uniformContinuumSchwingerBoundsWitness

uniformContinuumDistributionOrder :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ cutoff →
  DistributionOrderAtMost dataSet
    (cutoffSchwinger dataSet cutoff)
    (distributionOrder dataSet)
uniformContinuumDistributionOrder = uniformContinuumDistributionOrderWitness

renormalizedObservableUniformBound :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ cutoff observable test →
  UniformBound dataSet
    (cutoffSchwinger dataSet cutoff
      (renormalizedObservable dataSet cutoff observable) test)
    (observableBound dataSet observable)
renormalizedObservableUniformBound = renormalizedObservableUniformBoundWitness

nuclearSpaceCompactnessForSchwingerFamily :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  Precompact dataSet (cutoffSchwinger dataSet)
nuclearSpaceCompactnessForSchwingerFamily dataSet =
  nuclearSpaceCompactnessForSchwingerFamilyWitness dataSet
    (uniformContinuumDistributionOrder dataSet)

schwingerFamilyPrecompact :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  Precompact dataSet (cutoffSchwinger dataSet)
schwingerFamilyPrecompact = nuclearSpaceCompactnessForSchwingerFamily

continuumDiagonalMomentExtraction :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  Subsequence
continuumDiagonalMomentExtraction dataSet =
  continuumDiagonalMomentExtractionWitness dataSet
    (schwingerFamilyPrecompact dataSet)

continuumSubsequenceExists :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  IsSubsequence dataSet (continuumDiagonalMomentExtraction dataSet)
continuumSubsequenceExists = continuumSubsequenceIsSubsequence

latticeSpacingsTendToZero :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ cutoff → TendsToZeroSpacing dataSet cutoff
latticeSpacingsTendToZero = latticeSpacingsTendToZeroWitness

continuumSchwingerSubsequenceConverges :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ConvergesAlong dataSet
    (continuumDiagonalMomentExtraction dataSet)
    (continuumSchwingerSubsequenceLimit dataSet)
continuumSchwingerSubsequenceConverges =
  continuumSchwingerSubsequenceConvergesWitness

renormalizationGroupContinuumUniqueness :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ first second →
  IsSubsequence dataSet first →
  IsSubsequence dataSet second →
  ∀ firstLimit secondLimit →
  ConvergesAlong dataSet first firstLimit →
  ConvergesAlong dataSet second secondLimit →
  EqualSchwingerFamily dataSet firstLimit secondLimit
renormalizationGroupContinuumUniqueness =
  renormalizationGroupContinuumUniquenessWitness

allContinuumSubsequencesCoincide :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ first second firstLimit secondLimit →
  IsSubsequence dataSet first →
  IsSubsequence dataSet second →
  ConvergesAlong dataSet first firstLimit →
  ConvergesAlong dataSet second secondLimit →
  EqualSchwingerFamily dataSet firstLimit secondLimit
allContinuumSubsequencesCoincide = renormalizationGroupContinuumUniqueness

continuumLimitUnique :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet : ContinuumExtractionData Cutoff Observable Test Scalar Bound Subsequence) →
  ∀ candidate candidateSubsequence →
  IsSubsequence dataSet candidateSubsequence →
  ConvergesAlong dataSet candidateSubsequence candidate →
  EqualSchwingerFamily dataSet
    candidate (continuumSchwingerSubsequenceLimit dataSet)
continuumLimitUnique dataSet candidate candidateSubsequence isSub converges =
  renormalizationGroupContinuumUniqueness dataSet
    candidateSubsequence
    (continuumDiagonalMomentExtraction dataSet)
    isSub
    (continuumSubsequenceExists dataSet)
    candidate
    (continuumSchwingerSubsequenceLimit dataSet)
    converges
    (continuumSchwingerSubsequenceConverges dataSet)

------------------------------------------------------------------------
-- L5--L10. Closure of the six OS axioms under the selected limit.

record OSLimitClosureData
    (Cutoff Family Limit : Set) : Set₁ where
  field
    cutoffFamily : Cutoff → Family
    continuumFamily : Limit
    Converges : (Cutoff → Family) → Limit → Set
    familyConverges : Converges cutoffFamily continuumFamily

    FiniteSpacingRegularity : Cutoff → Set
    EuclideanApproximation : Cutoff → Set
    CovarianceDefectZeroInLimit : Set
    FiniteSpacingReflectionPositive : Cutoff → Set
    ReflectedFormsConverge : Set
    ReflectionPositiveConeIsClosed : Set
    FiniteSpacingPermutationSymmetric : Cutoff → Set
    PermutationContinuous : Set
    UniformConnectedClustered : Cutoff → Set
    UniformClusteringRate : Set
    ConnectedProductsConvergent : Set
    FiniteSpacingGrowthControlled : Cutoff → Set
    UniformGrowthConstants : Set
    GrowthLowerSemicontinuous : Set

    OS0AtLimit OS1AtLimit OS2AtLimit OS3AtLimit OS4AtLimit OS5AtLimit : Set

    finiteSpacingSchwingerRegularityWitness :
      ∀ cutoff → FiniteSpacingRegularity cutoff
    regularityClosedByDistributionalLimitWitness :
      Converges cutoffFamily continuumFamily →
      (∀ cutoff → FiniteSpacingRegularity cutoff) → OS0AtLimit

    latticeSymmetryApproximatesEuclideanGroupWitness :
      ∀ cutoff → EuclideanApproximation cutoff
    covarianceDefectTendsToZeroWitness : CovarianceDefectZeroInLimit
    latticeCovarianceConvergesToEuclideanCovarianceWitness :
      Converges cutoffFamily continuumFamily →
      (∀ cutoff → EuclideanApproximation cutoff) →
      CovarianceDefectZeroInLimit → OS1AtLimit

    finiteSpacingReflectionPositivityWitness :
      ∀ cutoff → FiniteSpacingReflectionPositive cutoff
    reflectedQuadraticFormsConvergeWitness : ReflectedFormsConverge
    reflectionPositiveConeClosedWitness : ReflectionPositiveConeIsClosed
    reflectionPositivityClosedUnderSchwingerLimitWitness :
      Converges cutoffFamily continuumFamily →
      (∀ cutoff → FiniteSpacingReflectionPositive cutoff) →
      ReflectedFormsConverge → ReflectionPositiveConeIsClosed → OS2AtLimit

    finiteSpacingPermutationSymmetryWitness :
      ∀ cutoff → FiniteSpacingPermutationSymmetric cutoff
    permutationActionContinuousOnDistributionsWitness : PermutationContinuous
    schwingerSymmetryClosedUnderLimitWitness :
      Converges cutoffFamily continuumFamily →
      (∀ cutoff → FiniteSpacingPermutationSymmetric cutoff) →
      PermutationContinuous → OS3AtLimit

    uniformConnectedClusteringWitness :
      ∀ cutoff → UniformConnectedClustered cutoff
    clusteringRateUniformInSpacingWitness : UniformClusteringRate
    connectedProductsConvergeWitness : ConnectedProductsConvergent
    clusteringClosedUnderSchwingerLimitWitness :
      Converges cutoffFamily continuumFamily →
      (∀ cutoff → UniformConnectedClustered cutoff) →
      UniformClusteringRate → ConnectedProductsConvergent → OS4AtLimit

    finiteSpacingGrowthBoundWitness :
      ∀ cutoff → FiniteSpacingGrowthControlled cutoff
    growthConstantsUniformInSpacingWitness : UniformGrowthConstants
    growthControlLowerSemicontinuousWitness : GrowthLowerSemicontinuous
    osGrowthBoundClosedUnderLimitWitness :
      Converges cutoffFamily continuumFamily →
      (∀ cutoff → FiniteSpacingGrowthControlled cutoff) →
      UniformGrowthConstants → GrowthLowerSemicontinuous → OS5AtLimit

open OSLimitClosureData public

finiteSpacingSchwingerRegularity = finiteSpacingSchwingerRegularityWitness
regularityClosedByDistributionalLimit = regularityClosedByDistributionalLimitWitness

os0RegularityClosedUnderLimit :
  ∀ {Cutoff Family Limit : Set} →
  (dataSet : OSLimitClosureData Cutoff Family Limit) → OS0AtLimit dataSet
os0RegularityClosedUnderLimit dataSet =
  regularityClosedByDistributionalLimit dataSet
    (familyConverges dataSet)
    (finiteSpacingSchwingerRegularity dataSet)

latticeSymmetryApproximatesEuclideanGroup =
  latticeSymmetryApproximatesEuclideanGroupWitness
covarianceDefectTendsToZero = covarianceDefectTendsToZeroWitness

latticeCovarianceConvergesToEuclideanCovariance :
  ∀ {Cutoff Family Limit : Set} →
  (dataSet : OSLimitClosureData Cutoff Family Limit) → OS1AtLimit dataSet
latticeCovarianceConvergesToEuclideanCovariance dataSet =
  latticeCovarianceConvergesToEuclideanCovarianceWitness dataSet
    (familyConverges dataSet)
    (latticeSymmetryApproximatesEuclideanGroup dataSet)
    (covarianceDefectTendsToZero dataSet)

finiteSpacingReflectionPositivity = finiteSpacingReflectionPositivityWitness
reflectedQuadraticFormsConverge = reflectedQuadraticFormsConvergeWitness
reflectionPositiveConeClosed = reflectionPositiveConeClosedWitness

reflectionPositivityClosedUnderSchwingerLimit :
  ∀ {Cutoff Family Limit : Set} →
  (dataSet : OSLimitClosureData Cutoff Family Limit) → OS2AtLimit dataSet
reflectionPositivityClosedUnderSchwingerLimit dataSet =
  reflectionPositivityClosedUnderSchwingerLimitWitness dataSet
    (familyConverges dataSet)
    (finiteSpacingReflectionPositivity dataSet)
    (reflectedQuadraticFormsConverge dataSet)
    (reflectionPositiveConeClosed dataSet)

finiteSpacingPermutationSymmetry = finiteSpacingPermutationSymmetryWitness
permutationActionContinuousOnDistributions =
  permutationActionContinuousOnDistributionsWitness

schwingerSymmetryClosedUnderLimit :
  ∀ {Cutoff Family Limit : Set} →
  (dataSet : OSLimitClosureData Cutoff Family Limit) → OS3AtLimit dataSet
schwingerSymmetryClosedUnderLimit dataSet =
  schwingerSymmetryClosedUnderLimitWitness dataSet
    (familyConverges dataSet)
    (finiteSpacingPermutationSymmetry dataSet)
    (permutationActionContinuousOnDistributions dataSet)

uniformConnectedClustering = uniformConnectedClusteringWitness
clusteringRateUniformInSpacing = clusteringRateUniformInSpacingWitness
connectedProductsConverge = connectedProductsConvergeWitness

clusteringClosedUnderSchwingerLimit :
  ∀ {Cutoff Family Limit : Set} →
  (dataSet : OSLimitClosureData Cutoff Family Limit) → OS4AtLimit dataSet
clusteringClosedUnderSchwingerLimit dataSet =
  clusteringClosedUnderSchwingerLimitWitness dataSet
    (familyConverges dataSet)
    (uniformConnectedClustering dataSet)
    (clusteringRateUniformInSpacing dataSet)
    (connectedProductsConverge dataSet)

finiteSpacingGrowthBound = finiteSpacingGrowthBoundWitness
growthConstantsUniformInSpacing = growthConstantsUniformInSpacingWitness
growthControlLowerSemicontinuous = growthControlLowerSemicontinuousWitness

osGrowthBoundClosedUnderLimit :
  ∀ {Cutoff Family Limit : Set} →
  (dataSet : OSLimitClosureData Cutoff Family Limit) → OS5AtLimit dataSet
osGrowthBoundClosedUnderLimit dataSet =
  osGrowthBoundClosedUnderLimitWitness dataSet
    (familyConverges dataSet)
    (finiteSpacingGrowthBound dataSet)
    (growthConstantsUniformInSpacing dataSet)
    (growthControlLowerSemicontinuous dataSet)

------------------------------------------------------------------------
-- L11--L13. Gauge-invariant observables and nonzero/non-Gaussian witnesses.

record ContinuumPhysicalObservableData (Observable LimitValue : Set) : Set₁ where
  field
    latticeObservable : Observable → Observable
    continuumObservable : Observable → LimitValue
    LatticeGaugeInvariant : Observable → Set
    IndependentOfGaugeFixing : LimitValue → Set
    ClosedPhysicalObservableAlgebra : Set
    Nonzero : LimitValue → Set
    ConnectedFourPointSurvives : Set
    WickFactorizationFails : Set
    NonGaussian : Set
    NontrivialTheory : Set

    latticeGaugeInvariantObservableConvergesWitness :
      ∀ observable → LatticeGaugeInvariant observable → LimitValue
    continuumObservableIndependentOfGaugeFixingWitness :
      ∀ observable →
      LatticeGaugeInvariant observable →
      IndependentOfGaugeFixing
        (latticeGaugeInvariantObservableConvergesWitness observable)
    continuumPhysicalObservableAlgebraClosedWitness :
      ClosedPhysicalObservableAlgebra

    nonzeroContinuumObservableWitness : Observable
    nonzeroContinuumObservableValueWitness :
      Nonzero (continuumObservable nonzeroContinuumObservableWitness)
    nonzeroTwoPointLimitWitness : Set
    continuumNontrivialityRulesOutZeroTheoryWitness :
      Nonzero (continuumObservable nonzeroContinuumObservableWitness) →
      NontrivialTheory

    connectedFourPointFunctionSurvivesWitness : ConnectedFourPointSurvives
    wickFactorizationFailsWitness : WickFactorizationFails
    nonGaussianContinuumWitness :
      ConnectedFourPointSurvives → WickFactorizationFails → NonGaussian
    continuumNontrivialityRulesOutGaussianTheoryWitness :
      NonGaussian → NontrivialTheory

open ContinuumPhysicalObservableData public

latticeGaugeInvariantObservableConverges =
  latticeGaugeInvariantObservableConvergesWitness
continuumObservableIndependentOfGaugeFixing =
  continuumObservableIndependentOfGaugeFixingWitness
continuumPhysicalObservableAlgebraClosed =
  continuumPhysicalObservableAlgebraClosedWitness
nonzeroContinuumObservable = nonzeroContinuumObservableWitness
nonzeroTwoPointLimit = nonzeroTwoPointLimitWitness
continuumNontrivialityRulesOutZeroTheory =
  continuumNontrivialityRulesOutZeroTheoryWitness
connectedFourPointFunctionSurvives = connectedFourPointFunctionSurvivesWitness
wickFactorizationFails = wickFactorizationFailsWitness

nonGaussianContinuumWitness :
  ∀ {Observable LimitValue : Set} →
  (dataSet : ContinuumPhysicalObservableData Observable LimitValue) →
  NonGaussian dataSet
nonGaussianContinuumWitness dataSet =
  ContinuumPhysicalObservableData.nonGaussianContinuumWitness dataSet
    (connectedFourPointFunctionSurvives dataSet)
    (wickFactorizationFails dataSet)

continuumNontrivialityRulesOutGaussianTheory :
  ∀ {Observable LimitValue : Set} →
  (dataSet : ContinuumPhysicalObservableData Observable LimitValue) →
  NontrivialTheory dataSet
continuumNontrivialityRulesOutGaussianTheory dataSet =
  ContinuumPhysicalObservableData.continuumNontrivialityRulesOutGaussianTheoryWitness dataSet
    (nonGaussianContinuumWitness dataSet)

continuumTheoryNontrivial :
  ∀ {Observable LimitValue : Set} →
  (dataSet : ContinuumPhysicalObservableData Observable LimitValue) →
  NontrivialTheory dataSet
continuumTheoryNontrivial dataSet =
  continuumNontrivialityRulesOutZeroTheory dataSet
    (nonzeroContinuumObservableValueWitness dataSet)

------------------------------------------------------------------------
-- M and N. Reconstruction plus the preferred clustering-to-gap route.

record RouteACompletion
    (Observable Point Scalar Hilbert Vector Hamiltonian Algebra
     Time Bound : Set)
    (system : OSGap.ContinuumSchwingerSystem Observable Point Scalar)
    (reconstruction :
      Production.OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system)
    (correlations :
      Production.UniformConnectedCorrelationDecayData
        Observable Time Scalar Bound Hamiltonian) : Set₁ where
  field
    reconstructionAuthority :
      Production.OSReconstructionStandardAuthority reconstruction
    vacuumUniquenessAuthority :
      Production.VacuumUniquenessAuthority reconstruction
    euclideanTimeAuthority :
      Production.EuclideanToHamiltonianClusteringAuthority correlations
    spectrumAuthority :
      Production.TimeClusteringSpectrumAuthority correlations euclideanTimeAuthority

    PhysicalObservableVectorsDenseInVacuumOrthogonalSpace : Set
    ObservableAlgebraCyclicForVacuum : Set
    physicalObservableVectorsDenseInVacuumOrthogonalSpaceWitness :
      PhysicalObservableVectorsDenseInVacuumOrthogonalSpace
    observableAlgebraCyclicForVacuumWitness :
      ObservableAlgebraCyclicForVacuum

open RouteACompletion public

osAxiomsReconstructHilbertSpace = Production.osAxiomsReconstructHilbertSpace
reconstructedVacuumExists = Production.reconstructedVacuumExists
reconstructedHamiltonianSelfAdjoint = Production.reconstructedHamiltonianSelfAdjoint
reconstructedHamiltonianNonnegative = Production.reconstructedHamiltonianNonnegative
physicalObservableAlgebraReconstructed = Production.physicalObservableAlgebraReconstructed
vacuumUnique = Production.vacuumUnique
uniformConnectedCorrelationDecay = Production.uniformConnectedCorrelationDecay
mStarPositive = Production.mStarPositive

euclideanClusteringImpliesHamiltonianTimeClustering =
  Production.euclideanClusteringImpliesHamiltonianTimeClustering

physicalObservableVectorsDenseInVacuumOrthogonalSpace :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra Time Bound : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar}
    {reconstruction :
      Production.OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system}
    {correlations :
      Production.UniformConnectedCorrelationDecayData
        Observable Time Scalar Bound Hamiltonian} →
  (route : RouteACompletion
    Observable Point Scalar Hilbert Vector Hamiltonian Algebra Time Bound
    system reconstruction correlations) →
  PhysicalObservableVectorsDenseInVacuumOrthogonalSpace route
physicalObservableVectorsDenseInVacuumOrthogonalSpace =
  physicalObservableVectorsDenseInVacuumOrthogonalSpaceWitness

observableAlgebraCyclicForVacuum :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra Time Bound : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar}
    {reconstruction :
      Production.OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system}
    {correlations :
      Production.UniformConnectedCorrelationDecayData
        Observable Time Scalar Bound Hamiltonian} →
  (route : RouteACompletion
    Observable Point Scalar Hilbert Vector Hamiltonian Algebra Time Bound
    system reconstruction correlations) →
  ObservableAlgebraCyclicForVacuum route
observableAlgebraCyclicForVacuum = observableAlgebraCyclicForVacuumWitness

exponentialSemigroupDecayImpliesSpectralSupportAbove =
  Production.exponentialTimeClusteringImpliesSpectrumGap
exponentialTimeClusteringImpliesSpectrumGap =
  Production.exponentialTimeClusteringImpliesSpectrumGap

------------------------------------------------------------------------
-- O. Strong-resolvent survival route.

record FiniteCutoffHamiltonianConstruction
    (Cutoff Transfer Hamiltonian Vacuum : Set) : Set₁ where
  field
    transferOperator : Cutoff → Transfer
    cutoffHamiltonian : Cutoff → Hamiltonian
    cutoffVacuum : Cutoff → Vacuum
    PositiveTransferOperator : Transfer → Set
    SelfAdjointTransferOperator : Transfer → Set
    HamiltonianDefinedFrom : Transfer → Hamiltonian → Set
    VacuumForCutoffHamiltonian : Hamiltonian → Vacuum → Set

    finiteCutoffTransferOperatorPositiveWitness :
      ∀ cutoff → PositiveTransferOperator (transferOperator cutoff)
    finiteCutoffTransferOperatorSelfAdjointWitness :
      ∀ cutoff → SelfAdjointTransferOperator (transferOperator cutoff)
    finiteCutoffHamiltonianDefinedWitness :
      ∀ cutoff → HamiltonianDefinedFrom
        (transferOperator cutoff) (cutoffHamiltonian cutoff)
    finiteCutoffVacuumExistsWitness :
      ∀ cutoff → VacuumForCutoffHamiltonian
        (cutoffHamiltonian cutoff) (cutoffVacuum cutoff)

open FiniteCutoffHamiltonianConstruction public

finiteCutoffTransferOperatorPositive =
  finiteCutoffTransferOperatorPositiveWitness
finiteCutoffTransferOperatorSelfAdjoint =
  finiteCutoffTransferOperatorSelfAdjointWitness
finiteCutoffHamiltonianDefined = finiteCutoffHamiltonianDefinedWitness
finiteCutoffVacuumExists = finiteCutoffVacuumExistsWitness
finiteCutoffSpectrumSeparated = Production.finiteCutoffSpectrumSeparated
uniformPositiveCutoffGap = Production.uniformPositiveCutoffGap
cutoffHamiltoniansConvergeStrongResolvent =
  Production.cutoffHamiltoniansConvergeStrongResolvent
cutoffVacuumProjectionsConverge =
  Production.cutoffVacuumProjectionsConverge
strongResolventUniformGapTransfer =
  Production.strongResolventUniformGapTransfer
strongResolventLimitPreservesUniformGap =
  Production.strongResolventLimitPreservesUniformGap
continuumSpectrumSeparated = Production.continuumSpectrumSeparated
continuumSpectrumSeparatedViaSurvivalBridge =
  Production.continuumSpectrumSeparatedViaSurvivalBridge

------------------------------------------------------------------------
-- Proof-level audit.  Extraction/assembly is checked here.  The analytic
-- estimates and the standard reconstruction/spectral theorems retain their
-- mathematically honest status.

continuumCutsetExtractionAssemblyLevel : ProofLevel
continuumCutsetExtractionAssemblyLevel = machineChecked

uniformSchwingerAndRGUniquenessInputsLevel : ProofLevel
uniformSchwingerAndRGUniquenessInputsLevel = conjectural

osLimitClosureAnalyticInputsLevel : ProofLevel
osLimitClosureAnalyticInputsLevel = conjectural

osReconstructionAndSpectralTransferLevel : ProofLevel
osReconstructionAndSpectralTransferLevel = standardImported

routeAUniformClusteringInputLevel : ProofLevel
routeAUniformClusteringInputLevel = conjectural

routeBOperatorConvergenceInputsLevel : ProofLevel
routeBOperatorConvergenceInputsLevel = conjectural
