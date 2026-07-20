module DASHI.Physics.YangMills.BalabanOSMassGapClosure where

------------------------------------------------------------------------
-- Continuum Osterwalder--Schrader and mass-gap closure surfaces.
-- OS reconstruction is standard imported mathematics.  The uniform continuum
-- hypotheses and the positive physical gap remain explicit frontier inputs.
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

osReconstructionLevel : ProofLevel
osReconstructionLevel = standardImported

continuumOSAxiomsLevel : ProofLevel
continuumOSAxiomsLevel = conjectural

clusteringToGapTransferLevel : ProofLevel
clusteringToGapTransferLevel = standardImported

physicalMassGapInputLevel : ProofLevel
physicalMassGapInputLevel = conjectural
