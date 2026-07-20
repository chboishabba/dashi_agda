module DASHI.Unified.GRQuantumContinuumAuthorities where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Unified.GRQuantumProofTerms
open import DASHI.Unified.GRQuantumStrictProofTerms
import DASHI.Empirical.GRQuantumCorrespondenceBoundary as Empirical

------------------------------------------------------------------------
-- Minimal strict authority cutset for terminal assembly.

record GRQuantumContinuumAuthorityCutset : Set₁ where
  field
    generalQuadraticUniqueness : QuadraticUniquenessProof

    continuumCausalLorentz : ChainAntichainLorentzProof
    continuumCausalLorentzClosed :
      ChainAntichainLorentzClosed continuumCausalLorentz

    cliffordUniversalCompletion : CliffordUniversalProof
    strictCliffordUniversalCompletion : StrictCliffordUniversalProof
    cliffordSurfaceCoherence :
      CliffordSurfaceCoherence
        cliffordUniversalCompletion
        strictCliffordUniversalCompletion

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
-- The older generic recovery fields remain compatibility tokens; actual typed
-- recovery and empirical evidence live in the strict terminal object.

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
    ; oneUnderlyingSubstrate = ⊤
    ; oneUnderlyingSubstrateProof = tt
    ; quantumReadingRecovered = ⊤
    ; quantumReadingRecoveredProof = tt
    ; generalRelativisticReadingRecovered = ⊤
    ; generalRelativisticReadingRecoveredProof = tt
    ; empiricalCorrespondenceSupplied = ⊤
    ; empiricalCorrespondenceSuppliedProof = tt
    }

strictTerminalFromAuthorityCutset :
  GRQuantumContinuumAuthorityCutset → StrictTerminalGRQuantumProof
strictTerminalFromAuthorityCutset authority =
  record
    { propositionTerminal = propositionTerminalFromAuthorityCutset authority
    ; strictClifford = strictCliffordUniversalCompletion authority
    ; cliffordCoherence = cliffordSurfaceCoherence authority
    ; strictSpinCover = strictSpinDoubleCover authority
    ; spinCoverAgreement = refl
    ; sharedSubstrate = sharedSubstrateRecovery authority
    ; empiricalCorrespondence = physicalCorrespondence authority
    }

------------------------------------------------------------------------
-- The finite/model bundle does not manufacture this cutset.

continuumAuthorityRequired :
  GRQuantumContinuumAuthorityCutset → GRQuantumContinuumAuthorityCutset
continuumAuthorityRequired authority = authority
