module DASHI.Unified.GRQuantumContinuumAuthorities where

open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Unified.GRQuantumProofTerms
open import DASHI.Unified.GRQuantumStrictProofTerms
import DASHI.Empirical.GRQuantumCorrespondenceBoundary as Empirical

------------------------------------------------------------------------
-- Minimal strict authority cutset for terminal assembly.
--
-- Every field is an actual theorem payload or closure witness.  This record is
-- the exact common target for imported standard mathematics, DASHI-specific
-- continuum limits, and empirical validation.  No canonical inhabitant is
-- supplied in this repository tranche.

record GRQuantumContinuumAuthorityCutset : Set₁ where
  field
    generalQuadraticUniqueness : QuadraticUniquenessProof

    continuumCausalLorentz : ChainAntichainLorentzProof
    continuumCausalLorentzClosed :
      ChainAntichainLorentzClosed continuumCausalLorentz

    cliffordUniversalCompletion : CliffordUniversalProof
    strictCliffordUniversalCompletion : StrictCliffordUniversalProof
    cliffordSurfacesCoherent : Set
    cliffordSurfacesCoherentProof : cliffordSurfacesCoherent

    strictSpinDoubleCover : StrictSpinDoubleCoverProof

    continuumWaveCCR : WaveLiftCCRProof
    continuumWaveCCRClosed : WaveLiftCCRClosed continuumWaveCCR

    continuumEinstein : EinsteinTensorProof
    continuumEinsteinClosed : EinsteinTensorClosed continuumEinstein

    continuumConstraints : ConstraintAlgebraProof
    continuumConstraintsClosed :
      ConstraintAlgebraClosed continuumConstraints

    continuumUVSpectrum : UVSpectralProof
    continuumUVSpectrumClosed : UVSpectralClosed continuumUVSpectrum

    sharedSubstrateRecovery : SharedSubstrateRecovery
    physicalCorrespondence : Empirical.PhysicalGRQuantumCorrespondence
open GRQuantumContinuumAuthorityCutset public

------------------------------------------------------------------------
-- Compatibility-level proposition terminal assembled from the strict cutset.
-- The generic fields in the earlier record are instantiated by the concrete
-- shared-substrate and empirical records carried by the cutset.

propositionTerminalFromAuthorityCutset :
  GRQuantumContinuumAuthorityCutset → TerminalGRQuantumProof
propositionTerminalFromAuthorityCutset authority =
  record
    { quadratic = generalQuadraticUniqueness authority
    ; causalLorentz = continuumCausalLorentz authority
    ; causalLorentzClosed = continuumCausalLorentzClosed authority
    ; clifford = cliffordUniversalCompletion authority
    ; spinCover = StrictSpinDoubleCoverProof.base
        (strictSpinDoubleCover authority)
    ; waveCCR = continuumWaveCCR authority
    ; waveCCRClosed = continuumWaveCCRClosed authority
    ; einstein = continuumEinstein authority
    ; einsteinClosed = continuumEinsteinClosed authority
    ; constraints = continuumConstraints authority
    ; constraintsClosed = continuumConstraintsClosed authority
    ; uvSpectrum = continuumUVSpectrum authority
    ; uvSpectrumClosed = continuumUVSpectrumClosed authority
    ; oneUnderlyingSubstrate = SharedSubstrateRecovery
    ; oneUnderlyingSubstrateProof = sharedSubstrateRecovery authority
    ; quantumReadingRecovered = SharedSubstrateRecovery
    ; quantumReadingRecoveredProof = sharedSubstrateRecovery authority
    ; generalRelativisticReadingRecovered = SharedSubstrateRecovery
    ; generalRelativisticReadingRecoveredProof =
        sharedSubstrateRecovery authority
    ; empiricalCorrespondenceSupplied =
        Empirical.PhysicalGRQuantumCorrespondence
    ; empiricalCorrespondenceSuppliedProof = physicalCorrespondence authority
    }

strictTerminalFromAuthorityCutset :
  GRQuantumContinuumAuthorityCutset → StrictTerminalGRQuantumProof
strictTerminalFromAuthorityCutset authority =
  record
    { propositionTerminal = propositionTerminalFromAuthorityCutset authority
    ; strictClifford = strictCliffordUniversalCompletion authority
    ; strictSpinCover = strictSpinDoubleCover authority
    ; sharedSubstrate = sharedSubstrateRecovery authority
    ; empiricalCorrespondence = physicalCorrespondence authority
    }

------------------------------------------------------------------------
-- The finite/model bundle does not manufacture this cutset.  This function is
-- intentionally only the identity once an authority producer supplies it.

continuumAuthorityRequired :
  GRQuantumContinuumAuthorityCutset → GRQuantumContinuumAuthorityCutset
continuumAuthorityRequired authority = authority
