module DASHI.Physics.YangMills.YMClayCanonicalEndgameValidation where

-- RED contract: the preferred post-#987 route must construct the physical
-- mass-gap certificate from the live R387 transfer-gap core plus one explicit
-- physical spectral interpretation, then expose a Lean-parity endpoint shape.

import DASHI.Physics.YangMills.YMClayR387PhysicalMassGapCertificateExact as R387Physical
import DASHI.Physics.YangMills.YMClayCanonicalMassGapConclusionExact as Endgame

open R387Physical
open Endgame

physicalSpectralInterpretationAvailable :
  ∀ {Observable Energy Bound Hamiltonian}
    (spectrum :
      DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact.ReconstructedClusteringSpectrum
        Observable Energy Bound) →
  Set₁
physicalSpectralInterpretationAvailable {Hamiltonian = Hamiltonian} spectrum =
  R387PhysicalSpectralInterpretation spectrum Hamiltonian

canonicalConclusionAvailable :
  ∀ Hamiltonian Vacuum Gap → Set₁
canonicalConclusionAvailable = CanonicalMassGapConclusion

physicalCertificateCompilerPresent : Set
physicalCertificateCompilerPresent = PhysicalCertificateCompilerPresent

canonicalEndgameCompilerPresent : Set
canonicalEndgameCompilerPresent = CanonicalEndgameCompilerPresent
