module DASHI.Physics.YangMills.BalabanContinuumOSMassGapExactCutset where

------------------------------------------------------------------------
-- Exact proof-relevant cutset for continuum extraction, OS0--OS5,
-- reconstruction, and the two physical mass-gap routes.
--
-- Requested analytic statements are individual fields, never postulates.
-- The module machine-checks the dependency graph and final assemblies while
-- retaining honest proof levels for inputs not proved elsewhere in the repo.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanContinuumOSLimit as ExistingLimit
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as Production

------------------------------------------------------------------------
-- L1--L4. Uniform bounds, compactness, subsequence extraction, uniqueness.

record ContinuumSchwingerCutset
    (Cutoff Observable Test Scalar Bound Subsequence : Set) : Set₁ where
  field
    cutoffSchwinger : Cutoff → Observable → Test → Scalar
    renormalizedObservable : Cutoff → Observable → Observable
    continuumSchwinger : Observable → Test → Scalar
    selectedSubsequence : Subsequence

    UniformBound : Scalar → Bound → Set
    DistributionOrderAtMost : (Observable → Test → Scalar) → Bound → Set
    Precompact : (Cutoff → Observable → Test → Scalar) → Set
    IsSubsequence : Subsequence → Set
    TendsToZeroSpacing : Cutoff → Set
    ConvergesAlong : Subsequence → (Observable → Test → Scalar) → Set
    EqualFamily :
      (Observable → Test → Scalar) →
      (Observable → Test → Scalar) → Set

    distributionOrder : Bound
    observableBound : Observable → Bound

    uniformContinuumSchwingerBounds :
      ∀ cutoff observable test →
      UniformBound
        (cutoffSchwinger cutoff observable test)
        (observableBound observable)

    uniformContinuumDistributionOrder :
      ∀ cutoff →
      DistributionOrderAtMost (cutoffSchwinger cutoff) distributionOrder

    renormalizedObservableUniformBound :
      ∀ cutoff observable test →
      UniformBound
        (cutoffSchwinger cutoff
          (renormalizedObservable cutoff observable) test)
        (observableBound observable)

    nuclearSpaceCompactnessForSchwingerFamily :
      (∀ cutoff →
        DistributionOrderAtMost (cutoffSchwinger cutoff) distributionOrder) →
      Precompact cutoffSchwinger

    schwingerFamilyPrecompact : Precompact cutoffSchwinger
    continuumDiagonalMomentExtraction : IsSubsequence selectedSubsequence
    continuumSubsequenceExists : IsSubsequence selectedSubsequence
    latticeSpacingsTendToZero : ∀ cutoff → TendsToZeroSpacing cutoff
    continuumSchwingerSubsequenceConverges :
      ConvergesAlong selectedSubsequence continuumSchwinger

    renormalizationGroupContinuumUniqueness :
      ∀ subsequence candidate →
      IsSubsequence subsequence →
      ConvergesAlong subsequence candidate →
      EqualFamily candidate continuumSchwinger

    allContinuumSubsequencesCoincide :
      ∀ first second firstLimit secondLimit →
      IsSubsequence first →
      IsSubsequence second →
      ConvergesAlong first firstLimit →
      ConvergesAlong second secondLimit →
      EqualFamily firstLimit secondLimit

    continuumLimitUnique :
      ∀ subsequence candidate →
      IsSubsequence subsequence →
      ConvergesAlong subsequence candidate →
      EqualFamily candidate continuumSchwinger

open ContinuumSchwingerCutset public

precompactnessFromUniformDistributionOrder :
  ∀ {Cutoff Observable Test Scalar Bound Subsequence : Set} →
  (dataSet :
    ContinuumSchwingerCutset
      Cutoff Observable Test Scalar Bound Subsequence) →
  Precompact dataSet (cutoffSchwinger dataSet)
precompactnessFromUniformDistributionOrder dataSet =
  nuclearSpaceCompactnessForSchwingerFamily dataSet
    (uniformContinuumDistributionOrder dataSet)

------------------------------------------------------------------------
-- L5--L10. OS0--OS5 closure with each topological ingredient explicit.

record OSAxiomLimitCutset (Cutoff : Set) : Set₁ where
  field
    ConvergesToSchwingerLimit : Set
    convergesToSchwingerLimit : ConvergesToSchwingerLimit

    FiniteSpacingRegularity : Cutoff → Set
    RegularityClosedByDistributionalLimit : Set
    OS0Regularity : Set
    finiteSpacingSchwingerRegularity :
      ∀ cutoff → FiniteSpacingRegularity cutoff
    regularityClosedByDistributionalLimit :
      RegularityClosedByDistributionalLimit
    os0RegularityClosedUnderLimit : OS0Regularity

    LatticeSymmetryApproximatesEuclidean : Cutoff → Set
    CovarianceDefectTendsToZero : Set
    OS1EuclideanCovariance : Set
    latticeSymmetryApproximatesEuclideanGroup :
      ∀ cutoff → LatticeSymmetryApproximatesEuclidean cutoff
    covarianceDefectTendsToZero : CovarianceDefectTendsToZero
    latticeCovarianceConvergesToEuclideanCovariance :
      OS1EuclideanCovariance

    FiniteSpacingReflectionPositive : Cutoff → Set
    ReflectedQuadraticFormsConvergent : Set
    ReflectionPositiveConeClosed : Set
    OS2ReflectionPositivity : Set
    finiteSpacingReflectionPositivity :
      ∀ cutoff → FiniteSpacingReflectionPositive cutoff
    reflectedQuadraticFormsConverge : ReflectedQuadraticFormsConvergent
    reflectionPositiveConeClosed : ReflectionPositiveConeClosed
    reflectionPositivityClosedUnderSchwingerLimit :
      OS2ReflectionPositivity

    FiniteSpacingPermutationSymmetric : Cutoff → Set
    PermutationActionContinuous : Set
    OS3PermutationSymmetry : Set
    finiteSpacingPermutationSymmetry :
      ∀ cutoff → FiniteSpacingPermutationSymmetric cutoff
    permutationActionContinuousOnDistributions :
      PermutationActionContinuous
    schwingerSymmetryClosedUnderLimit : OS3PermutationSymmetry

    UniformConnectedClustered : Cutoff → Set
    ClusteringRateUniformInSpacing : Set
    ConnectedProductsConvergent : Set
    OS4Clustering : Set
    uniformConnectedClustering :
      ∀ cutoff → UniformConnectedClustered cutoff
    clusteringRateUniformInSpacing : ClusteringRateUniformInSpacing
    connectedProductsConverge : ConnectedProductsConvergent
    clusteringClosedUnderSchwingerLimit : OS4Clustering

    FiniteSpacingGrowthControlled : Cutoff → Set
    GrowthConstantsUniformInSpacing : Set
    GrowthControlLowerSemicontinuous : Set
    OS5GrowthControl : Set
    finiteSpacingGrowthBound :
      ∀ cutoff → FiniteSpacingGrowthControlled cutoff
    growthConstantsUniformInSpacing : GrowthConstantsUniformInSpacing
    growthControlLowerSemicontinuous : GrowthControlLowerSemicontinuous
    osGrowthBoundClosedUnderLimit : OS5GrowthControl

open OSAxiomLimitCutset public

------------------------------------------------------------------------
-- L11--L13. Gauge-invariant observables and interacting nontriviality.

record ContinuumObservableCutset (Observable Value : Set) : Set₁ where
  field
    latticeObservable : Observable → Observable
    continuumObservable : Observable → Value

    LatticeGaugeInvariant : Observable → Set
    GaugeFixingIndependent : Value → Set
    PhysicalObservableAlgebraClosed : Set
    Nonzero : Value → Set
    NonzeroTwoPoint : Set
    ConnectedFourPointSurvives : Set
    WickFactorizationFailsProperty : Set
    NonGaussian : Set
    NontrivialTheory : Set

    latticeGaugeInvariantObservableConverges :
      ∀ observable → LatticeGaugeInvariant observable → Value
    continuumObservableIndependentOfGaugeFixing :
      ∀ observable →
      LatticeGaugeInvariant observable →
      GaugeFixingIndependent
        (latticeGaugeInvariantObservableConverges observable)
    continuumPhysicalObservableAlgebraClosed :
      PhysicalObservableAlgebraClosed

    nonzeroContinuumObservable : Observable
    nonzeroContinuumObservableValue :
      Nonzero (continuumObservable nonzeroContinuumObservable)
    nonzeroTwoPointLimit : NonzeroTwoPoint
    continuumNontrivialityRulesOutZeroTheory :
      Nonzero (continuumObservable nonzeroContinuumObservable) →
      NontrivialTheory

    connectedFourPointFunctionSurvives : ConnectedFourPointSurvives
    wickFactorizationFails : WickFactorizationFailsProperty
    nonGaussianContinuumWitness : NonGaussian
    continuumNontrivialityRulesOutGaussianTheory :
      NonGaussian → NontrivialTheory
    continuumTheoryNontrivial : NontrivialTheory

open ContinuumObservableCutset public

------------------------------------------------------------------------
-- M. Exact match between the constructed Schwinger system and imported OS
-- reconstruction.  These are the already-separated standard authorities.

open Production public using
  ( osAxiomsReconstructHilbertSpace
  ; reconstructedVacuumExists
  ; reconstructedHamiltonianSelfAdjoint
  ; reconstructedHamiltonianNonnegative
  ; physicalObservableAlgebraReconstructed
  ; vacuumUnique
  )

------------------------------------------------------------------------
-- N. Route A: uniform connected clustering to a physical spectral gap.

record RouteAAnalyticCutset
    (Observable Time Scalar Bound Hamiltonian Vector : Set) : Set₁ where
  field
    correlationData :
      Production.UniformConnectedCorrelationDecayData
        Observable Time Scalar Bound Hamiltonian

    uniformConnectedCorrelationDecay :
      ∀ A B t →
      Production.LessEqual correlationData
        (Production.absoluteValue correlationData
          (Production.connectedCorrelation correlationData A B t))
        (Production.multiply correlationData
          (Production.correlationConstant correlationData A B)
          (Production.exponentialDecay correlationData
            (Production.mStar correlationData) t))

    mStarPositive :
      Production.Positive correlationData (Production.mStar correlationData)

    euclideanTimeAuthority :
      Production.EuclideanToHamiltonianClusteringAuthority correlationData

    EuclideanTimeSemigroupClustering : Set
    euclideanClusteringImpliesHamiltonianTimeClustering :
      EuclideanTimeSemigroupClustering

    PhysicalObservableVectorsDenseInVacuumOrthogonalSpace : Set
    ObservableAlgebraCyclicForVacuum : Set
    physicalObservableVectorsDenseInVacuumOrthogonalSpace :
      PhysicalObservableVectorsDenseInVacuumOrthogonalSpace
    observableAlgebraCyclicForVacuum :
      ObservableAlgebraCyclicForVacuum

    spectrumAuthority :
      Production.TimeClusteringSpectrumAuthority
        correlationData euclideanTimeAuthority

    exponentialSemigroupDecayImpliesSpectralSupportAbove :
      OSGap.PhysicalMassGapCertificate Hamiltonian Bound
    exponentialTimeClusteringImpliesSpectrumGap :
      OSGap.PhysicalMassGapCertificate Hamiltonian Bound

open RouteAAnalyticCutset public

routeAGapFromExistingSpectralTransfer :
  ∀ {Observable Time Scalar Bound Hamiltonian Vector : Set} →
  (route : RouteAAnalyticCutset
    Observable Time Scalar Bound Hamiltonian Vector) →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
routeAGapFromExistingSpectralTransfer route =
  Production.exponentialTimeClusteringImpliesSpectrumGap
    (correlationData route)
    (euclideanTimeAuthority route)
    (spectrumAuthority route)

------------------------------------------------------------------------
-- O. Route B: finite-cutoff Hamiltonians and strong-resolvent survival.

record FiniteCutoffTransferConstruction
    (Cutoff Transfer Hamiltonian Vacuum : Set) : Set₁ where
  field
    transferOperator : Cutoff → Transfer
    cutoffHamiltonian : Cutoff → Hamiltonian
    cutoffVacuum : Cutoff → Vacuum

    TransferPositive : Transfer → Set
    TransferSelfAdjoint : Transfer → Set
    HamiltonianDefinedFrom : Transfer → Hamiltonian → Set
    VacuumFor : Hamiltonian → Vacuum → Set

    finiteCutoffTransferOperatorPositive :
      ∀ cutoff → TransferPositive (transferOperator cutoff)
    finiteCutoffTransferOperatorSelfAdjoint :
      ∀ cutoff → TransferSelfAdjoint (transferOperator cutoff)
    finiteCutoffHamiltonianDefined :
      ∀ cutoff →
      HamiltonianDefinedFrom
        (transferOperator cutoff) (cutoffHamiltonian cutoff)
    finiteCutoffVacuumExists :
      ∀ cutoff → VacuumFor (cutoffHamiltonian cutoff) (cutoffVacuum cutoff)

open FiniteCutoffTransferConstruction public

open Production public using
  ( finiteCutoffSpectrumSeparated
  ; uniformPositiveCutoffGap
  ; cutoffHamiltoniansConvergeStrongResolvent
  ; cutoffVacuumProjectionsConverge
  ; strongResolventUniformGapTransfer
  ; strongResolventLimitPreservesUniformGap
  ; continuumSpectrumSeparated
  ; continuumSpectrumSeparatedViaSurvivalBridge
  )

------------------------------------------------------------------------
-- One coherent endpoint prevents mixing a subsequence from one cutoff family,
-- OS closure from another, and a gap witness from a third.

record ContinuumOSMassGapCertificate
    (Cutoff Observable Test Scalar Bound Subsequence Point : Set) : Set₁ where
  field
    extraction :
      ContinuumSchwingerCutset
        Cutoff Observable Test Scalar Bound Subsequence
    osClosure : OSAxiomLimitCutset Cutoff
    observables : ContinuumObservableCutset Observable Scalar

    continuumSystem :
      OSGap.ContinuumSchwingerSystem Observable Point Scalar

    continuumLimitIsUnique :
      ∀ subsequence candidate →
      IsSubsequence extraction subsequence →
      ConvergesAlong extraction subsequence candidate →
      EqualFamily extraction candidate (continuumSchwinger extraction)

    continuumTheoryIsNontrivial : NontrivialTheory observables

open ContinuumOSMassGapCertificate public

continuumOSMassGapCutsetAssemblyLevel : ProofLevel
continuumOSMassGapCutsetAssemblyLevel = machineChecked

uniformContinuumSchwingerInputsLevel : ProofLevel
uniformContinuumSchwingerInputsLevel = conjectural

continuumUniquenessInputLevel : ProofLevel
continuumUniquenessInputLevel = conjectural

os0ToOS5LimitClosureInputsLevel : ProofLevel
os0ToOS5LimitClosureInputsLevel = conjectural

continuumObservableNontrivialityInputsLevel : ProofLevel
continuumObservableNontrivialityInputsLevel = conjectural

osReconstructionAuthoritiesLevel : ProofLevel
osReconstructionAuthoritiesLevel = standardImported

routeAUniformClusteringInputLevel : ProofLevel
routeAUniformClusteringInputLevel = conjectural

routeASpectralTransferAuthorityLevel : ProofLevel
routeASpectralTransferAuthorityLevel = standardImported

routeBFiniteGapAndOperatorConvergenceInputsLevel : ProofLevel
routeBFiniteGapAndOperatorConvergenceInputsLevel = conjectural
