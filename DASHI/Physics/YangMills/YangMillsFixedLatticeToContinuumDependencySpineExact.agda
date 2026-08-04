module DASHI.Physics.YangMills.YangMillsFixedLatticeToContinuumDependencySpineExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- P. K. Mitter,
-- "The Exact Renormalization Group",
-- contribution to the Encyclopedia of Mathematical Physics (2006).
-- arXiv:math-ph/0505008. No DOI assigned in the cited manuscript.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- PURPOSE
-- Replace one opaque global endpoint token by the exact dependency ladder
-- required after local Step V.  The records below do not import a Yang--Mills
-- construction.  They force fixed-lattice uniqueness, LSI, clustering and gap
-- control to precede cross-scale Cauchy estimates, thermodynamic limits,
-- cutoff removal, OS reconstruction and the physical SI mass-gap statement.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.BalabanP06PhysicalModelLeafLightweightExact as P06
import DASHI.Physics.YangMills.BalabanP11LightweightCanonicalPaymentExact as P11
import DASHI.Physics.YangMills.BalabanP33P10Gate4DependencySpineExact as Local
import DASHI.Physics.YangMills.YangMillsRGParitySISpineExact as Endpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

record FixedLatticeDLRLSIGapPackage
    {leaf : P06.P06LightweightPhysicalModelLeaf}
    (p11 : P11.P11LightweightCanonicalPayment leaf)
    (local : Local.Gate4SevenPackageSpine) : Set₁ where
  field
    Specification DLRState Observable Scalar : Set

    stepVWeightedShellBoundFeedsPolymerCriterion : Set
    stepVWeightedShellBoundFeedsPolymerCriterionEvidence :
      stepVWeightedShellBoundFeedsPolymerCriterion

    polymerCriterionImpliesDLRSmallness : Set
    polymerCriterionImpliesDLRSmallnessEvidence :
      polymerCriterionImpliesDLRSmallness

    dlrSmallnessImpliesFiniteVolumeUniqueness : Set
    dlrSmallnessImpliesFiniteVolumeUniquenessEvidence :
      dlrSmallnessImpliesFiniteVolumeUniqueness

    dlrSmallnessImpliesUniformLogSobolevInequality : Set
    dlrSmallnessImpliesUniformLogSobolevInequalityEvidence :
      dlrSmallnessImpliesUniformLogSobolevInequality

    uniformLSIImpliesExponentialClustering : Set
    uniformLSIImpliesExponentialClusteringEvidence :
      uniformLSIImpliesExponentialClustering

    reflectionPositivityAtFixedLatticeSpacing : Set
    reflectionPositivityAtFixedLatticeSpacingEvidence :
      reflectionPositivityAtFixedLatticeSpacing

    clusteringAndReflectionPositivityImplyFixedLatticeGap : Set
    clusteringAndReflectionPositivityImplyFixedLatticeGapEvidence :
      clusteringAndReflectionPositivityImplyFixedLatticeGap

    gapUniformInFiniteVolume : Set
    gapUniformInFiniteVolumeEvidence : gapUniformInFiniteVolume

    localGate4InputsAreTheSameAsClusterInputs : Set
    localGate4InputsAreTheSameAsClusterInputsEvidence :
      localGate4InputsAreTheSameAsClusterInputs

    theoremBoundary : String

open FixedLatticeDLRLSIGapPackage public

record CrossScaleRGControlPackage
    {leaf : P06.P06LightweightPhysicalModelLeaf}
    {p11 : P11.P11LightweightCanonicalPayment leaf}
    {local : Local.Gate4SevenPackageSpine}
    (fixed : FixedLatticeDLRLSIGapPackage p11 local) : Set₁ where
  field
    Scale EffectiveAction InfluenceKernel Scalar : Set

    crossScaleInfluenceSummable : Set
    crossScaleInfluenceSummableEvidence :
      crossScaleInfluenceSummable

    oneStepEffectiveActionDifferenceBound : Set
    oneStepEffectiveActionDifferenceBoundEvidence :
      oneStepEffectiveActionDifferenceBound

    effectiveActionsCauchyAcrossScales : Set
    effectiveActionsCauchyAcrossScalesEvidence :
      effectiveActionsCauchyAcrossScales

    clusteringConstantsStableAcrossScales : Set
    clusteringConstantsStableAcrossScalesEvidence :
      clusteringConstantsStableAcrossScales

    spectralGapLowerBoundStableAcrossScales : Set
    spectralGapLowerBoundStableAcrossScalesEvidence :
      spectralGapLowerBoundStableAcrossScales

    renormalizedCouplingsRemainInControlledDomain : Set
    renormalizedCouplingsRemainInControlledDomainEvidence :
      renormalizedCouplingsRemainInControlledDomain

    theoremBoundary : String

open CrossScaleRGControlPackage public

record ThermodynamicAndCutoffLimitPackage
    {leaf : P06.P06LightweightPhysicalModelLeaf}
    {p11 : P11.P11LightweightCanonicalPayment leaf}
    {local : Local.Gate4SevenPackageSpine}
    {fixed : FixedLatticeDLRLSIGapPackage p11 local}
    (crossScale : CrossScaleRGControlPackage fixed) : Set₁ where
  field
    FiniteVolumeMeasure InfiniteVolumeMeasure CutoffMeasure : Set

    finiteVolumeMeasuresTight : Set
    finiteVolumeMeasuresTightEvidence : finiteVolumeMeasuresTight

    thermodynamicSubsequenceExists : Set
    thermodynamicSubsequenceExistsEvidence :
      thermodynamicSubsequenceExists

    dlrUniquenessIdentifiesAllThermodynamicSubsequences : Set
    dlrUniquenessIdentifiesAllThermodynamicSubsequencesEvidence :
      dlrUniquenessIdentifiesAllThermodynamicSubsequences

    thermodynamicLimitExistsAndIsUnique : Set
    thermodynamicLimitExistsAndIsUniqueEvidence :
      thermodynamicLimitExistsAndIsUnique

    cutoffFamilyTight : Set
    cutoffFamilyTightEvidence : cutoffFamilyTight

    continuumSubsequenceExists : Set
    continuumSubsequenceExistsEvidence : continuumSubsequenceExists

    schemeComparisonTelescopes : Set
    schemeComparisonTelescopesEvidence : schemeComparisonTelescopes

    cutoffRemovalUniqueOrSchemeIndependent : Set
    cutoffRemovalUniqueOrSchemeIndependentEvidence :
      cutoffRemovalUniqueOrSchemeIndependent

    clusteringAndGapUniformUnderBothLimits : Set
    clusteringAndGapUniformUnderBothLimitsEvidence :
      clusteringAndGapUniformUnderBothLimits

    theoremBoundary : String

open ThermodynamicAndCutoffLimitPackage public

record OsterwalderSchraderPhysicalGapPackage
    {leaf : P06.P06LightweightPhysicalModelLeaf}
    {p11 : P11.P11LightweightCanonicalPayment leaf}
    {local : Local.Gate4SevenPackageSpine}
    {fixed : FixedLatticeDLRLSIGapPackage p11 local}
    {crossScale : CrossScaleRGControlPackage fixed}
    (limits : ThermodynamicAndCutoffLimitPackage crossScale)
    (Scalar : Set) : Set₁ where
  field
    SchwingerFamily HilbertSpace Hamiltonian Vacuum : Set

    os0Regularity : Set
    os0RegularityEvidence : os0Regularity

    os1EuclideanCovariance : Set
    os1EuclideanCovarianceEvidence : os1EuclideanCovariance

    os2ReflectionPositivity : Set
    os2ReflectionPositivityEvidence : os2ReflectionPositivity

    os3PermutationSymmetry : Set
    os3PermutationSymmetryEvidence : os3PermutationSymmetry

    os4Clustering : Set
    os4ClusteringEvidence : os4Clustering

    osReconstructionProducesHilbertSpaceAndHamiltonian : Set
    osReconstructionProducesHilbertSpaceAndHamiltonianEvidence :
      osReconstructionProducesHilbertSpaceAndHamiltonian

    euclideanDecayTransfersToPositiveSpectralGap : Set
    euclideanDecayTransfersToPositiveSpectralGapEvidence :
      euclideanDecayTransfersToPositiveSpectralGap

    latticeGapNormalizationMatchesContinuumInverseLength : Set
    latticeGapNormalizationMatchesContinuumInverseLengthEvidence :
      latticeGapNormalizationMatchesContinuumInverseLength

    inverseLengthConvertedToPositiveSIMass : Set
    inverseLengthConvertedToPositiveSIMassEvidence :
      inverseLengthConvertedToPositiveSIMass

    existingParityAndSIEndpoint :
      Endpoint.YangMillsParitySISpine Scalar

    endpointUsesTheSameLimitAndGapConstruction : Set
    endpointUsesTheSameLimitAndGapConstructionEvidence :
      endpointUsesTheSameLimitAndGapConstruction

    theoremBoundary : String

open OsterwalderSchraderPhysicalGapPackage public

record YangMillsFixedLatticeToContinuumSpine : Set₁ where
  field
    lightweightLeaf : P06.P06LightweightPhysicalModelLeaf
    p11 : P11.P11LightweightCanonicalPayment lightweightLeaf
    local : Local.Gate4SevenPackageSpine
    fixedLattice : FixedLatticeDLRLSIGapPackage p11 local
    crossScale : CrossScaleRGControlPackage fixedLattice
    limits : ThermodynamicAndCutoffLimitPackage crossScale
    Scalar : Set
    osAndPhysicalGap :
      OsterwalderSchraderPhysicalGapPackage limits Scalar

    noLocalEstimateReplacedByGlobalInterface : Set
    noLocalEstimateReplacedByGlobalInterfaceEvidence :
      noLocalEstimateReplacedByGlobalInterface

    noLatticeGapRelabelledAsPhysicalMassWithoutScaling : Set
    noLatticeGapRelabelledAsPhysicalMassWithoutScalingEvidence :
      noLatticeGapRelabelledAsPhysicalMassWithoutScaling

    theoremBoundary : String

open YangMillsFixedLatticeToContinuumSpine public

fixedLatticeDependencyInterfaceLevel : ProofLevel
fixedLatticeDependencyInterfaceLevel = machineChecked

crossScaleAndLimitDependencyInterfaceLevel : ProofLevel
crossScaleAndLimitDependencyInterfaceLevel = machineChecked

osPhysicalGapDependencyInterfaceLevel : ProofLevel
osPhysicalGapDependencyInterfaceLevel = machineChecked

physicalFixedLatticeGapInputsLevel : ProofLevel
physicalFixedLatticeGapInputsLevel = conditional

physicalCrossScaleAndLimitInputsLevel : ProofLevel
physicalCrossScaleAndLimitInputsLevel = conditional

physicalOSAndSIMassGapInputsLevel : ProofLevel
physicalOSAndSIMassGapInputsLevel = conditional
