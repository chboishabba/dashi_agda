module DASHI.Physics.YangMills.BalabanOSMassGapClosure where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions", Communications in Mathematical
-- Physics 31 (1973), 83--112. DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", second edition,
-- Springer, 1987. DOI: 10.1007/978-1-4612-4728-9.
--
-- DASHI CONTRIBUTION
--
-- Continuum Osterwalder--Schrader and mass-gap closure surfaces.
-- OS reconstruction and the abstract clustering-to-Hamiltonian-gap mechanism
-- are standard imported mathematics.  The source-specific Yang--Mills work is
-- deliberately kept separate:
--
--   * construct one continuum Schwinger family;
--   * prove the OS axioms for THAT family;
--   * retain an interacting/non-Gaussian witness for THAT family;
--   * prove cutoff-uniform physical clustering for THAT family.
--
-- In particular, reconstruction does not manufacture nontriviality and an
-- auxiliary RG-chain gap is not accepted as a physical Hamiltonian gap.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

record ContinuumSchwingerSystem
    (Observable Point Scalar : Set) : Set₁ where
  field
    schwinger : Observable → Point → Point → Scalar

    OS0Regularity : Set
    OS1EuclideanCovariance : Set
    OS2ReflectionPositivity : Set
    OS3PermutationSymmetry : Set
    OS4Clustering : Set
    OS5GrowthControl : Set

    os0 : OS0Regularity
    os1 : OS1EuclideanCovariance
    os2 : OS2ReflectionPositivity
    os3 : OS3PermutationSymmetry
    os4 : OS4Clustering
    os5 : OS5GrowthControl

open ContinuumSchwingerSystem public

record InteractingContinuumWitness
    (Observable Point Scalar : Set)
    (system : ContinuumSchwingerSystem Observable Point Scalar) : Set₁ where
  field
    Witness : Set
    witness : Witness

open InteractingContinuumWitness public

record OSReconstructionAuthority
    (Observable Point Scalar : Set)
    (system : ContinuumSchwingerSystem Observable Point Scalar) : Set₁ where
  field
    HilbertSpace : Set
    Hamiltonian : Set
    Vacuum : Set
    WightmanTheory : Set

    hilbertSpace : HilbertSpace
    hamiltonian : Hamiltonian
    vacuum : Vacuum
    wightmanTheory : WightmanTheory

open OSReconstructionAuthority public

record UniformClusteringData
    (Observable Point Bound : Set) : Set₁ where
  field
    connectedCorrelationBound : Observable → Point → Bound
    massParameter : Bound
    Positive : Bound → Set
    positiveMassParameter : Positive massParameter
    UniformInCutoff : Set
    uniformInCutoff : UniformInCutoff

open UniformClusteringData public

record PhysicalMassGapCertificate
    (Hamiltonian Bound : Set) : Set₁ where
  field
    hamiltonian : Hamiltonian
    gap : Bound
    Positive : Bound → Set
    gapPositive : Positive gap
    SpectrumAboveVacuumGap : Set
    spectrumAboveVacuumGap : SpectrumAboveVacuumGap

open PhysicalMassGapCertificate public

record ClusteringToGapAuthority
    (Observable Point Bound Hamiltonian : Set)
    (clustering : UniformClusteringData Observable Point Bound) : Set₁ where
  field
    transferHamiltonian : Hamiltonian
    SpectrumAboveVacuumGap : Set
    spectrumAboveVacuumGap : SpectrumAboveVacuumGap

open ClusteringToGapAuthority public

clusteringToPhysicalMassGap :
  ∀ {Observable Point Bound Hamiltonian : Set} →
  (clustering : UniformClusteringData Observable Point Bound) →
  ClusteringToGapAuthority Observable Point Bound Hamiltonian clustering →
  PhysicalMassGapCertificate Hamiltonian Bound
clusteringToPhysicalMassGap clustering authority = record
  { hamiltonian = transferHamiltonian authority
  ; gap = massParameter clustering
  ; Positive = Positive clustering
  ; gapPositive = positiveMassParameter clustering
  ; SpectrumAboveVacuumGap = SpectrumAboveVacuumGap authority
  ; spectrumAboveVacuumGap = spectrumAboveVacuumGap authority
  }

record NontrivialPhysicalMassGapCertificate
    (Observable Point Scalar Hamiltonian Bound : Set)
    (system : ContinuumSchwingerSystem Observable Point Scalar) : Set₁ where
  field
    interacting : InteractingContinuumWitness Observable Point Scalar system
    massGap : PhysicalMassGapCertificate Hamiltonian Bound

open NontrivialPhysicalMassGapCertificate public

assembleNontrivialPhysicalMassGap :
  ∀ {Observable Point Scalar Hamiltonian Bound : Set}
    {system : ContinuumSchwingerSystem Observable Point Scalar} →
  InteractingContinuumWitness Observable Point Scalar system →
  PhysicalMassGapCertificate Hamiltonian Bound →
  NontrivialPhysicalMassGapCertificate
    Observable Point Scalar Hamiltonian Bound system
assembleNontrivialPhysicalMassGap interacting gapCertificate = record
  { interacting = interacting
  ; massGap = gapCertificate
  }

osReconstructionLevel : ProofLevel
osReconstructionLevel = standardImported

continuumOSAxiomsLevel : ProofLevel
continuumOSAxiomsLevel = conditional

continuumInteractingWitnessLevel : ProofLevel
continuumInteractingWitnessLevel = conditional

clusteringToGapTransferLevel : ProofLevel
clusteringToGapTransferLevel = standardImported

physicalMassGapInputLevel : ProofLevel
physicalMassGapInputLevel = conditional

nontrivialPhysicalGapAssemblyLevel : ProofLevel
nontrivialPhysicalGapAssemblyLevel = machineChecked
