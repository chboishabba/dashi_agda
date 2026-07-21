module DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction where

------------------------------------------------------------------------
-- Named Osterwalder--Schrader reconstruction and physical mass-gap
-- production surface.
--
-- The standard functional-analytic theorems remain explicit imported
-- authorities.  Every requested reconstruction and spectral-transfer step is
-- nevertheless instantiated separately, so the final physical certificate can
-- no longer hide vacuum uniqueness, vacuum-projection convergence, or the
-- no-spectral-pollution argument inside one undifferentiated bridge.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanMassGapSurvival as Survival

------------------------------------------------------------------------
-- L. Osterwalder--Schrader reconstruction.

record OSReconstructionData
    (Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set)
    (system : OSGap.ContinuumSchwingerSystem Observable Point Scalar) : Set₁ where
  field
    reconstructedHilbertSpace : Hilbert
    reconstructedVacuum : Vector
    reconstructedHamiltonian : Hamiltonian
    reconstructedObservableAlgebra : Algebra

    SelfAdjoint : Hamiltonian → Set
    Nonnegative : Hamiltonian → Set
    VacuumVector : Hilbert → Vector → Set
    PhysicalObservableAlgebra : Algebra → Set
    VacuumFor : Hamiltonian → Vector → Set
    EqualVector : Vector → Vector → Set

    hilbertSpaceReconstructed : Set
    vacuumVectorExists :
      VacuumVector reconstructedHilbertSpace reconstructedVacuum
    hamiltonianSelfAdjoint :
      SelfAdjoint reconstructedHamiltonian
    hamiltonianNonnegative :
      Nonnegative reconstructedHamiltonian
    observableAlgebraPhysical :
      PhysicalObservableAlgebra reconstructedObservableAlgebra
    reconstructedVacuumIsVacuum :
      VacuumFor reconstructedHamiltonian reconstructedVacuum

open OSReconstructionData public

record OSReconstructionStandardAuthority
    {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet :
      OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) : Set₁ where
  field
    osAxiomsReconstruct :
      OSGap.OS0Regularity system →
      OSGap.OS1EuclideanCovariance system →
      OSGap.OS2ReflectionPositivity system →
      OSGap.OS3PermutationSymmetry system →
      OSGap.OS4Clustering system →
      OSGap.OS5GrowthControl system →
      Set

    reconstructionWitness :
      osAxiomsReconstruct
        (OSGap.os0 system)
        (OSGap.os1 system)
        (OSGap.os2 system)
        (OSGap.os3 system)
        (OSGap.os4 system)
        (OSGap.os5 system)

open OSReconstructionStandardAuthority public

-- L1. The complete OS axiom package reconstructs the selected Hilbert-space
-- realization.
osAxiomsReconstructHilbertSpace :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet :
    OSReconstructionData
      Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) →
  OSReconstructionStandardAuthority dataSet →
  Set
osAxiomsReconstructHilbertSpace dataSet authority =
  osAxiomsReconstruct authority
    (OSGap.os0 _)
    (OSGap.os1 _)
    (OSGap.os2 _)
    (OSGap.os3 _)
    (OSGap.os4 _)
    (OSGap.os5 _)

-- L2. The reconstructed cyclic vector exists.
reconstructedVacuumExists :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet :
    OSReconstructionData
      Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) →
  VacuumVector dataSet
    (reconstructedHilbertSpace dataSet)
    (reconstructedVacuum dataSet)
reconstructedVacuumExists = vacuumVectorExists

-- L3. The reconstructed Hamiltonian is self-adjoint and nonnegative.
reconstructedHamiltonianSelfAdjoint :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet :
    OSReconstructionData
      Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) →
  SelfAdjoint dataSet (reconstructedHamiltonian dataSet)
reconstructedHamiltonianSelfAdjoint = hamiltonianSelfAdjoint

reconstructedHamiltonianNonnegative :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet :
    OSReconstructionData
      Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) →
  Nonnegative dataSet (reconstructedHamiltonian dataSet)
reconstructedHamiltonianNonnegative = hamiltonianNonnegative

-- L4. Gauge-invariant Euclidean observables descend to the physical algebra.
physicalObservableAlgebraReconstructed :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet :
    OSReconstructionData
      Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) →
  PhysicalObservableAlgebra dataSet
    (reconstructedObservableAlgebra dataSet)
physicalObservableAlgebraReconstructed = observableAlgebraPhysical

record VacuumUniquenessAuthority
    {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar}
    (dataSet :
      OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) : Set₁ where
  field
    vacuumUniquenessTransfer :
      ∀ candidate →
      VacuumFor dataSet (reconstructedHamiltonian dataSet) candidate →
      EqualVector dataSet candidate (reconstructedVacuum dataSet)

open VacuumUniquenessAuthority public

-- L5. Clustering/ergodicity supplies uniqueness of the reconstructed vacuum.
vacuumUnique :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra : Set}
    {system : OSGap.ContinuumSchwingerSystem Observable Point Scalar} →
  (dataSet :
    OSReconstructionData
      Observable Point Scalar Hilbert Vector Hamiltonian Algebra system) →
  VacuumUniquenessAuthority dataSet →
  ∀ candidate →
  VacuumFor dataSet (reconstructedHamiltonian dataSet) candidate →
  EqualVector dataSet candidate (reconstructedVacuum dataSet)
vacuumUnique dataSet authority = vacuumUniquenessTransfer authority

------------------------------------------------------------------------
-- M-A. Uniform Euclidean clustering to Hamiltonian spectral gap.

record UniformConnectedCorrelationDecayData
    (Observable Time Scalar Bound Hamiltonian : Set) : Set₁ where
  field
    connectedCorrelation : Observable → Observable → Time → Scalar
    absoluteValue : Scalar → Bound
    multiply : Bound → Bound → Bound
    exponentialDecay : Bound → Time → Bound
    LessEqual : Bound → Bound → Set

    correlationConstant : Observable → Observable → Bound
    mStar : Bound
    Positive : Bound → Set
    mStarPositive : Positive mStar

    hamiltonian : Hamiltonian

    uniformConnectedCorrelationDecayWitness :
      ∀ A B t →
      LessEqual
        (absoluteValue (connectedCorrelation A B t))
        (multiply
          (correlationConstant A B)
          (exponentialDecay mStar t))

open UniformConnectedCorrelationDecayData public

-- M-A1. Uniform exponential decay of connected correlations.
uniformConnectedCorrelationDecay :
  ∀ {Observable Time Scalar Bound Hamiltonian : Set} →
  (dataSet :
    UniformConnectedCorrelationDecayData
      Observable Time Scalar Bound Hamiltonian) →
  ∀ A B t →
  LessEqual dataSet
    (absoluteValue dataSet (connectedCorrelation dataSet A B t))
    (multiply dataSet
      (correlationConstant dataSet A B)
      (exponentialDecay dataSet (mStar dataSet) t))
uniformConnectedCorrelationDecay = uniformConnectedCorrelationDecayWitness

record EuclideanToHamiltonianClusteringAuthority
    {Observable Time Scalar Bound Hamiltonian : Set}
    (dataSet :
      UniformConnectedCorrelationDecayData
        Observable Time Scalar Bound Hamiltonian) : Set₁ where
  field
    HamiltonianTimeClustering : Hamiltonian → Bound → Set
    euclideanToTimeClusteringTransfer :
      (∀ A B t →
        LessEqual dataSet
          (absoluteValue dataSet (connectedCorrelation dataSet A B t))
          (multiply dataSet
            (correlationConstant dataSet A B)
            (exponentialDecay dataSet (mStar dataSet) t))) →
      HamiltonianTimeClustering (hamiltonian dataSet) (mStar dataSet)

open EuclideanToHamiltonianClusteringAuthority public

-- M-A2. OS reconstruction transfers Euclidean-time decay to semigroup decay.
euclideanClusteringImpliesHamiltonianTimeClustering :
  ∀ {Observable Time Scalar Bound Hamiltonian : Set} →
  (dataSet :
    UniformConnectedCorrelationDecayData
      Observable Time Scalar Bound Hamiltonian) →
  (authority : EuclideanToHamiltonianClusteringAuthority dataSet) →
  HamiltonianTimeClustering authority
    (hamiltonian dataSet)
    (mStar dataSet)
euclideanClusteringImpliesHamiltonianTimeClustering dataSet authority =
  euclideanToTimeClusteringTransfer authority
    (uniformConnectedCorrelationDecay dataSet)

record TimeClusteringSpectrumAuthority
    {Observable Time Scalar Bound Hamiltonian : Set}
    (dataSet :
      UniformConnectedCorrelationDecayData
        Observable Time Scalar Bound Hamiltonian)
    (timeAuthority : EuclideanToHamiltonianClusteringAuthority dataSet) : Set₁ where
  field
    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    timeClusteringToSpectrumGap :
      HamiltonianTimeClustering timeAuthority
        (hamiltonian dataSet)
        (mStar dataSet) →
      SpectrumSeparatedBy (hamiltonian dataSet) (mStar dataSet)

open TimeClusteringSpectrumAuthority public

-- M-A3. Exponential Hamiltonian-time clustering excludes spectrum in (0,m*).
exponentialTimeClusteringImpliesSpectrumGap :
  ∀ {Observable Time Scalar Bound Hamiltonian : Set} →
  (dataSet :
    UniformConnectedCorrelationDecayData
      Observable Time Scalar Bound Hamiltonian) →
  (timeAuthority : EuclideanToHamiltonianClusteringAuthority dataSet) →
  (spectrumAuthority :
    TimeClusteringSpectrumAuthority dataSet timeAuthority) →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
exponentialTimeClusteringImpliesSpectrumGap
    dataSet timeAuthority spectrumAuthority = record
  { hamiltonian = hamiltonian dataSet
  ; gap = mStar dataSet
  ; Positive = Positive dataSet
  ; gapPositive = mStarPositive dataSet
  ; SpectrumAboveVacuumGap =
      SpectrumSeparatedBy spectrumAuthority
        (hamiltonian dataSet)
        (mStar dataSet)
  ; spectrumAboveVacuumGap =
      timeClusteringToSpectrumGap spectrumAuthority
        (euclideanClusteringImpliesHamiltonianTimeClustering
          dataSet timeAuthority)
  }

------------------------------------------------------------------------
-- M-B. Uniform cutoff spectral gaps to continuum spectral separation.

record CutoffSpectralLimitData
    (Cutoff Hamiltonian Bound Projection : Set) : Set₁ where
  field
    cutoffHamiltonian : Cutoff → Hamiltonian
    continuumHamiltonian : Hamiltonian
    cutoffGap : Cutoff → Bound
    mStar : Bound

    Positive : Bound → Set
    LessEqual : Bound → Bound → Set
    mStarPositive : Positive mStar

    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    finiteCutoffSeparation : ∀ cutoff →
      SpectrumSeparatedBy
        (cutoffHamiltonian cutoff)
        (cutoffGap cutoff)
    commonPositiveGap : ∀ cutoff →
      LessEqual mStar (cutoffGap cutoff)

    StrongResolventConvergesTo :
      (Cutoff → Hamiltonian) → Hamiltonian → Set
    strongResolventConvergence :
      StrongResolventConvergesTo cutoffHamiltonian continuumHamiltonian

    cutoffVacuumProjection : Cutoff → Projection
    continuumVacuumProjection : Projection
    VacuumProjectionsConvergeTo :
      (Cutoff → Projection) → Projection → Set
    vacuumProjectionConvergence :
      VacuumProjectionsConvergeTo
        cutoffVacuumProjection continuumVacuumProjection

open CutoffSpectralLimitData public

-- M-B1. Each finite-cutoff Hamiltonian is separated above its vacuum.
finiteCutoffSpectrumSeparated :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  ∀ cutoff →
  SpectrumSeparatedBy dataSet
    (cutoffHamiltonian dataSet cutoff)
    (cutoffGap dataSet cutoff)
finiteCutoffSpectrumSeparated = finiteCutoffSeparation

-- M-B2. One strictly positive lower bound works for all cutoffs.
uniformPositiveCutoffGap :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  ∀ cutoff →
  LessEqual dataSet (mStar dataSet) (cutoffGap dataSet cutoff)
uniformPositiveCutoffGap = commonPositiveGap

-- M-B3. The cutoff Hamiltonians converge in strong-resolvent topology.
cutoffHamiltoniansConvergeStrongResolvent :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  StrongResolventConvergesTo dataSet
    (cutoffHamiltonian dataSet)
    (continuumHamiltonian dataSet)
cutoffHamiltoniansConvergeStrongResolvent = strongResolventConvergence

-- M-B4. The isolated vacuum eigenspaces converge as projections.
cutoffVacuumProjectionsConverge :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  VacuumProjectionsConvergeTo dataSet
    (cutoffVacuumProjection dataSet)
    (continuumVacuumProjection dataSet)
cutoffVacuumProjectionsConverge = vacuumProjectionConvergence

record StrongResolventNoPollutionAuthority
    {Cutoff Hamiltonian Bound Projection : Set}
    (dataSet :
      CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) : Set₁ where
  field
    strongResolventUniformGapTransfer :
      StrongResolventConvergesTo dataSet
        (cutoffHamiltonian dataSet)
        (continuumHamiltonian dataSet) →
      VacuumProjectionsConvergeTo dataSet
        (cutoffVacuumProjection dataSet)
        (continuumVacuumProjection dataSet) →
      (∀ cutoff →
        SpectrumSeparatedBy dataSet
          (cutoffHamiltonian dataSet cutoff)
          (cutoffGap dataSet cutoff)) →
      (∀ cutoff →
        LessEqual dataSet (mStar dataSet) (cutoffGap dataSet cutoff)) →
      SpectrumSeparatedBy dataSet
        (continuumHamiltonian dataSet)
        (mStar dataSet)

open StrongResolventNoPollutionAuthority public

-- M-B5. Strong-resolvent convergence plus convergence of the isolated vacuum
-- projection prevents spectral pollution below m*.
strongResolventLimitPreservesUniformGap :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  StrongResolventNoPollutionAuthority dataSet →
  SpectrumSeparatedBy dataSet
    (continuumHamiltonian dataSet)
    (mStar dataSet)
strongResolventLimitPreservesUniformGap dataSet authority =
  strongResolventUniformGapTransfer authority
    (cutoffHamiltoniansConvergeStrongResolvent dataSet)
    (cutoffVacuumProjectionsConverge dataSet)
    (finiteCutoffSpectrumSeparated dataSet)
    (uniformPositiveCutoffGap dataSet)

-- M-B6. Continuum physical gap certificate.
continuumSpectrumSeparated :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  StrongResolventNoPollutionAuthority dataSet →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
continuumSpectrumSeparated dataSet authority = record
  { hamiltonian = continuumHamiltonian dataSet
  ; gap = mStar dataSet
  ; Positive = Positive dataSet
  ; gapPositive = mStarPositive dataSet
  ; SpectrumAboveVacuumGap =
      SpectrumSeparatedBy dataSet
        (continuumHamiltonian dataSet)
        (mStar dataSet)
  ; spectrumAboveVacuumGap =
      strongResolventLimitPreservesUniformGap dataSet authority
  }

-- Adapter into the older BalabanMassGapSurvival bridge.  The bridge now starts
-- from the fully exposed M-B1--M-B5 package rather than silently absorbing the
-- projection-convergence hypothesis.
toUniformCutoffGapData :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection →
  Survival.UniformCutoffGapData Cutoff Hamiltonian Bound
toUniformCutoffGapData dataSet = record
  { cutoffHamiltonian = cutoffHamiltonian dataSet
  ; cutoffGap = cutoffGap dataSet
  ; lowerGap = mStar dataSet
  ; Positive = Positive dataSet
  ; LessEqual = LessEqual dataSet
  ; positiveLowerGap = mStarPositive dataSet
  ; lowerBoundUniform = uniformPositiveCutoffGap dataSet
  ; SpectrumSeparatedBy = SpectrumSeparatedBy dataSet
  ; cutoffSpectrumSeparated = finiteCutoffSpectrumSeparated dataSet
  }

toGapSurvivesContinuumAuthority :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  StrongResolventNoPollutionAuthority dataSet →
  Survival.GapSurvivesContinuumAuthority (toUniformCutoffGapData dataSet)
toGapSurvivesContinuumAuthority dataSet authority = record
  { continuumHamiltonian = continuumHamiltonian dataSet
  ; uniformGapTransfer = λ lowerBounds cutoffGaps →
      strongResolventUniformGapTransfer authority
        (cutoffHamiltoniansConvergeStrongResolvent dataSet)
        (cutoffVacuumProjectionsConverge dataSet)
        cutoffGaps
        lowerBounds
  }

continuumSpectrumSeparatedViaSurvivalBridge :
  ∀ {Cutoff Hamiltonian Bound Projection : Set} →
  (dataSet :
    CutoffSpectralLimitData Cutoff Hamiltonian Bound Projection) →
  (authority : StrongResolventNoPollutionAuthority dataSet) →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
continuumSpectrumSeparatedViaSurvivalBridge dataSet authority =
  Survival.survivingPhysicalMassGap
    (toUniformCutoffGapData dataSet)
    (toGapSurvivesContinuumAuthority dataSet authority)

------------------------------------------------------------------------
-- Proof-level ledger.

osHilbertReconstructionAuthorityLevel : ProofLevel
osHilbertReconstructionAuthorityLevel = standardImported

osReconstructionExtractionLevel : ProofLevel
osReconstructionExtractionLevel = machineChecked

vacuumUniquenessAuthorityLevel : ProofLevel
vacuumUniquenessAuthorityLevel = standardImported

uniformConnectedCorrelationDecayInputLevel : ProofLevel
uniformConnectedCorrelationDecayInputLevel = conjectural

euclideanTimeClusteringTransferLevel : ProofLevel
euclideanTimeClusteringTransferLevel = standardImported

clusteringSpectrumTransferLevel : ProofLevel
clusteringSpectrumTransferLevel = standardImported

finiteCutoffSpectrumInputLevel : ProofLevel
finiteCutoffSpectrumInputLevel = conjectural

uniformPositiveCutoffGapInputLevel : ProofLevel
uniformPositiveCutoffGapInputLevel = conjectural

strongResolventConvergenceInputLevel : ProofLevel
strongResolventConvergenceInputLevel = conjectural

vacuumProjectionConvergenceInputLevel : ProofLevel
vacuumProjectionConvergenceInputLevel = conjectural

strongResolventNoPollutionAuthorityLevel : ProofLevel
strongResolventNoPollutionAuthorityLevel = standardImported

massGapProductionAssemblyLevel : ProofLevel
massGapProductionAssemblyLevel = machineChecked
