{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSOSReconstructedHamiltonianGapExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as Gap
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OS

------------------------------------------------------------------------
-- ROUTE-S S3 / USE THE RICH OS RECONSTRUCTION PRODUCER DIRECTLY.
--
-- The historical R281/R331 route carried an arbitrary predicate asserting that
-- a selected spectral/decay coordinate belonged to the reconstructed H.
-- The richer OS production lane already exposes the standard theorem in the
-- right direction:
--
--   Euclidean connected decay
--     -> Hamiltonian-time clustering
--     -> spectrum separated above the vacuum.
--
-- Here the Hamiltonian in the correlation object is definitionally the
-- reconstructedHamiltonian of the SAME OSReconstructionData.  There is no
-- post-hoc Hamiltonian equality or arbitrary SpectrumOfReconstructedHamiltonian
-- predicate.
------------------------------------------------------------------------

record ReconstructedHamiltonianRouteSInputs
    (Observable Point Scalar Hilbert Vector Hamiltonian Algebra Bound : Set)
    {system : Gap.ContinuumSchwingerSystem Observable Point Scalar}
    (reconstruction :
      OS.OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system)
    : Set₁ where
  field
    correlationDecay :
      OS.UniformConnectedCorrelationDecayData
        Observable Nat Scalar Bound Hamiltonian

    decayUsesReconstructedHamiltonian :
      OS.hamiltonian correlationDecay
      ≡ OS.reconstructedHamiltonian reconstruction

    euclideanTimeAuthority :
      OS.EuclideanToHamiltonianClusteringAuthority correlationDecay

    spectrumAuthority :
      OS.TimeClusteringSpectrumAuthority
        correlationDecay euclideanTimeAuthority

open ReconstructedHamiltonianRouteSInputs public

routeSPhysicalGapOnDecayHamiltonian :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra Bound}
    {system : Gap.ContinuumSchwingerSystem Observable Point Scalar}
    {reconstruction :
      OS.OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system} →
  ReconstructedHamiltonianRouteSInputs
    Observable Point Scalar Hilbert Vector Hamiltonian Algebra Bound
    reconstruction →
  Gap.PhysicalMassGapCertificate Hamiltonian Bound
routeSPhysicalGapOnDecayHamiltonian inputs =
  OS.exponentialTimeClusteringImpliesSpectrumGap
    (correlationDecay inputs)
    (euclideanTimeAuthority inputs)
    (spectrumAuthority inputs)

sameReconstructedHamiltonianIsExplicit :
  ∀ {Observable Point Scalar Hilbert Vector Hamiltonian Algebra Bound}
    {system : Gap.ContinuumSchwingerSystem Observable Point Scalar}
    {reconstruction :
      OS.OSReconstructionData
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra system}
    (inputs :
      ReconstructedHamiltonianRouteSInputs
        Observable Point Scalar Hilbert Vector Hamiltonian Algebra Bound
        reconstruction) →
  Gap.hamiltonian (routeSPhysicalGapOnDecayHamiltonian inputs)
  ≡ OS.reconstructedHamiltonian reconstruction
sameReconstructedHamiltonianIsExplicit inputs =
  decayUsesReconstructedHamiltonian inputs

routeSOSReconstructedHamiltonianGapCompilerLevel : ProofLevel
routeSOSReconstructedHamiltonianGapCompilerLevel = machineChecked

routeSEuclideanToHamiltonianTransferLevel : ProofLevel
routeSEuclideanToHamiltonianTransferLevel =
  OS.euclideanTimeClusteringTransferLevel

routeSHamiltonianClusteringToSpectrumLevel : ProofLevel
routeSHamiltonianClusteringToSpectrumLevel =
  OS.clusteringSpectrumTransferLevel
