module DASHI.Physics.YangMills.BalabanUniformPhysicalMassGapAnalyticInhabitation where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Proof-relevant OS reconstruction and uniform physical mass-gap owner.
------------------------------------------------------------------------

record UniformPhysicalMassGapAnalyticInputs : Set₁ where
  field
    -- Osterwalder--Schrader reconstruction.
    OSAxiomsReconstructHilbertSpace : Set
    osAxiomsReconstructHilbertSpace : OSAxiomsReconstructHilbertSpace
    ReconstructedVacuumExists : Set
    reconstructedVacuumExists : ReconstructedVacuumExists
    ReconstructedHamiltonianSelfAdjoint : Set
    reconstructedHamiltonianSelfAdjoint :
      ReconstructedHamiltonianSelfAdjoint
    ReconstructedHamiltonianNonnegative : Set
    reconstructedHamiltonianNonnegative :
      ReconstructedHamiltonianNonnegative
    PhysicalObservableAlgebraReconstructed : Set
    physicalObservableAlgebraReconstructed :
      PhysicalObservableAlgebraReconstructed
    VacuumUnique : Set
    vacuumUnique : VacuumUnique

    -- Preferred Route A: clustering to spectral gap.
    UniformConnectedCorrelationDecay : Set
    uniformConnectedCorrelationDecay : UniformConnectedCorrelationDecay
    MStarPositive : Set
    mStarPositive : MStarPositive
    PhysicalObservableVectorsDenseInVacuumOrthogonalSpace : Set
    physicalObservableVectorsDenseInVacuumOrthogonalSpace :
      PhysicalObservableVectorsDenseInVacuumOrthogonalSpace
    ObservableAlgebraCyclicForVacuum : Set
    observableAlgebraCyclicForVacuum : ObservableAlgebraCyclicForVacuum
    EuclideanClusteringImpliesHamiltonianTimeClustering : Set
    euclideanClusteringImpliesHamiltonianTimeClustering :
      EuclideanClusteringImpliesHamiltonianTimeClustering
    ExponentialSemigroupDecayImpliesSpectralSupportAbove : Set
    exponentialSemigroupDecayImpliesSpectralSupportAbove :
      ExponentialSemigroupDecayImpliesSpectralSupportAbove
    ExponentialTimeClusteringImpliesSpectrumGap : Set
    exponentialTimeClusteringImpliesSpectrumGap :
      ExponentialTimeClusteringImpliesSpectrumGap

    -- Alternative Route B: cutoff gaps and no spectral pollution.
    FiniteCutoffTransferOperatorPositive : Set
    finiteCutoffTransferOperatorPositive :
      FiniteCutoffTransferOperatorPositive
    FiniteCutoffTransferOperatorSelfAdjoint : Set
    finiteCutoffTransferOperatorSelfAdjoint :
      FiniteCutoffTransferOperatorSelfAdjoint
    FiniteCutoffHamiltonianDefined : Set
    finiteCutoffHamiltonianDefined : FiniteCutoffHamiltonianDefined
    FiniteCutoffVacuumExists : Set
    finiteCutoffVacuumExists : FiniteCutoffVacuumExists
    FiniteCutoffSpectrumSeparated : Set
    finiteCutoffSpectrumSeparated : FiniteCutoffSpectrumSeparated
    UniformPositiveCutoffGap : Set
    uniformPositiveCutoffGap : UniformPositiveCutoffGap
    CutoffHamiltoniansConvergeStrongResolvent : Set
    cutoffHamiltoniansConvergeStrongResolvent :
      CutoffHamiltoniansConvergeStrongResolvent
    CutoffVacuumProjectionsConverge : Set
    cutoffVacuumProjectionsConverge : CutoffVacuumProjectionsConverge
    VacuumMultiplicityStable : Set
    vacuumMultiplicityStable : VacuumMultiplicityStable
    StrongResolventUniformGapTransfer : Set
    strongResolventUniformGapTransfer : StrongResolventUniformGapTransfer
    StrongResolventLimitPreservesUniformGap : Set
    strongResolventLimitPreservesUniformGap :
      StrongResolventLimitPreservesUniformGap
    ContinuumSpectrumSeparated : Set
    continuumSpectrumSeparated : ContinuumSpectrumSeparated
    ContinuumSpectrumSeparatedViaSurvivalBridge : Set
    continuumSpectrumSeparatedViaSurvivalBridge :
      ContinuumSpectrumSeparatedViaSurvivalBridge

open UniformPhysicalMassGapAnalyticInputs public

osReconstructionAuthorityLevel : ProofLevel
osReconstructionAuthorityLevel = standardImported

osReconstructionExtractionLevel : ProofLevel
osReconstructionExtractionLevel = machineChecked

routeAAssemblyLevel : ProofLevel
routeAAssemblyLevel = machineChecked

routeAAnalyticInputLevel : ProofLevel
routeAAnalyticInputLevel = conjectural

routeASpectralTransferLevel : ProofLevel
routeASpectralTransferLevel = standardImported

routeBAssemblyLevel : ProofLevel
routeBAssemblyLevel = machineChecked

routeBAnalyticInputLevel : ProofLevel
routeBAnalyticInputLevel = conjectural

noSpectralPollutionTransferLevel : ProofLevel
noSpectralPollutionTransferLevel = standardImported
