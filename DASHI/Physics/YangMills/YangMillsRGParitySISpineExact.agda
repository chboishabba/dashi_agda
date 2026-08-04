module DASHI.Physics.YangMills.YangMillsRGParitySISpineExact where

------------------------------------------------------------------------
-- PROVENANCE
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
-- Edgar Buckingham,
-- "On Physically Similar Systems; Illustrations of the Use of Dimensional
-- Equations", Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- PURPOSE
-- Carry physical involution invariance and SI-dimensional meaning as explicit
-- invariants through RG, thermodynamic limit, cutoff removal and OS
-- reconstruction.  These invariants refine but do not replace reflection
-- positivity, clustering or spectral-gap analysis.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.PhysicalInvolutionParityExact as Parity
import DASHI.Physics.YangMills.BalabanGate4ParityIntegrationExact as Gate4
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as SIEndpoint
open import DASHI.Physics.YangMills.CompactLieProofLevel

record RGParityPreservation : Set₁ where
  field
    FineField CoarseField Activity : Set

    fineInvolution : Parity.Involution FineField
    coarseInvolution : Parity.Involution CoarseField

    blockAverageCommutesWithInvolution : Set
    blockAverageCommutesWithInvolutionEvidence :
      blockAverageCommutesWithInvolution

    fluctuationIntegrationPreservesEvenness : Set
    fluctuationIntegrationPreservesEvennessEvidence :
      fluctuationIntegrationPreservesEvenness

    localizationPreservesParity : Set
    localizationPreservesParityEvidence :
      localizationPreservesParity

    exponentiationPreservesParity : Set
    exponentiationPreservesParityEvidence :
      exponentiationPreservesParity

    rOperationPreservesParity : Set
    rOperationPreservesParityEvidence : rOperationPreservesParity

    renormalizedActionInvolutionInvariant : Set
    renormalizedActionInvolutionInvariantEvidence :
      renormalizedActionInvolutionInvariant

open RGParityPreservation public

record ThermodynamicParityPreservation : Set₁ where
  field
    FiniteVolumeMeasure InfiniteVolumeMeasure Observable Scalar : Set

    finiteVolumeMeasureInvolutionInvariant : Set
    finiteVolumeMeasureInvolutionInvariantEvidence :
      finiteVolumeMeasureInvolutionInvariant

    tightLimitPreservesInvariance : Set
    tightLimitPreservesInvarianceEvidence :
      tightLimitPreservesInvariance

    dlrKernelInvolutionCovariant : Set
    dlrKernelInvolutionCovariantEvidence :
      dlrKernelInvolutionCovariant

    uniqueDLRStateInvolutionInvariant : Set
    uniqueDLRStateInvolutionInvariantEvidence :
      uniqueDLRStateInvolutionInvariant

    oddObservableExpectationZero : Set
    oddObservableExpectationZeroEvidence :
      oddObservableExpectationZero

open ThermodynamicParityPreservation public

record ContinuumParityPreservation : Set₁ where
  field
    LatticeReflection ContinuumReflection SchwingerFamily : Set

    latticeReflectionConvergesToContinuumReflection : Set
    latticeReflectionConvergesToContinuumReflectionEvidence :
      latticeReflectionConvergesToContinuumReflection

    schwingerFunctionsReflectionCovariant : Set
    schwingerFunctionsReflectionCovariantEvidence :
      schwingerFunctionsReflectionCovariant

    oddSchwingerComponentsVanish : Set
    oddSchwingerComponentsVanishEvidence :
      oddSchwingerComponentsVanish

    hypercubicParityExtendsToO4Reflection : Set
    hypercubicParityExtendsToO4ReflectionEvidence :
      hypercubicParityExtendsToO4Reflection

open ContinuumParityPreservation public

record OSParityAndGapEndpoint (Scalar : Set) : Set₁ where
  field
    HilbertSpace Hamiltonian Vacuum ReflectionOperator : Set

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

    reflectionOperatorInvolutive : Set
    reflectionOperatorInvolutiveEvidence :
      reflectionOperatorInvolutive

    reflectionOperatorIsometric : Set
    reflectionOperatorIsometricEvidence : reflectionOperatorIsometric

    evenOddHilbertSubspaces : Set
    evenOddHilbertSubspacesEvidence : evenOddHilbertSubspaces

    hamiltonianCommutesWithParity : Set
    hamiltonianCommutesWithParityEvidence :
      hamiltonianCommutesWithParity

    vacuumParityInvariant : Set
    vacuumParityInvariantEvidence : vacuumParityInvariant

    oddFieldVacuumExpectationZero : Set
    oddFieldVacuumExpectationZeroEvidence :
      oddFieldVacuumExpectationZero

    siScales : SIEndpoint.YangMillsGapScales Scalar
    siMassGap : SIEndpoint.SIYangMillsMassGap Scalar siScales

    euclideanClusteringImpliesSpectralGap : Set
    euclideanClusteringImpliesSpectralGapEvidence :
      euclideanClusteringImpliesSpectralGap

    theoremBoundary : String

open OSParityAndGapEndpoint public

record YangMillsParitySISpine (Scalar : Set) : Set₁ where
  field
    gate4 : Gate4.Gate4ParityPackage
    rg : RGParityPreservation
    thermodynamic : ThermodynamicParityPreservation
    continuum : ContinuumParityPreservation
    osEndpoint : OSParityAndGapEndpoint Scalar

    parityNeverSubstitutesForOSPositivity : Set
    parityNeverSubstitutesForOSPositivityEvidence :
      parityNeverSubstitutesForOSPositivity

    inverseLengthToSIConversionExplicit : Set
    inverseLengthToSIConversionExplicitEvidence :
      inverseLengthToSIConversionExplicit

open YangMillsParitySISpine public

rgParitySpineInterfaceLevel : ProofLevel
rgParitySpineInterfaceLevel = machineChecked

thermodynamicAndContinuumParityInterfaceLevel : ProofLevel
thermodynamicAndContinuumParityInterfaceLevel = machineChecked

osParityAndSIGapInterfaceLevel : ProofLevel
osParityAndSIGapInterfaceLevel = machineChecked

physicalRGParityPreservationLevel : ProofLevel
physicalRGParityPreservationLevel = conditional

physicalLimitAndOSHypothesesLevel : ProofLevel
physicalLimitAndOSHypothesesLevel = conditional
