module DASHI.Physics.Plasma.MagneticConfinementExperimentalAuthorityBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement

------------------------------------------------------------------------
-- MAGNETIC-CONFINEMENT EXPERIMENTAL AUTHORITY
--
-- Reuses the same citation-vs-artifact boundary used by the collider/CMS/LHCb
-- lanes.  A publication can identify a result; promotion of a measured field,
-- reconstructed equilibrium, transport coefficient or fusion-performance
-- observable requires its own artifact authority.
------------------------------------------------------------------------

record MagneticConfinementExperimentalAuthority
  (state : Confinement.MagneticConfinementState) : Set₁ where
  constructor magnetic-confinement-experimental-authority
  field
    machineConfigurationAuthority : Authority.CitationAuthorityBoundary
    magneticsArtifactAuthority : Authority.ArtifactAuthorityBoundary
    equilibriumReconstructionAuthority : Authority.ArtifactAuthorityBoundary
    transportArtifactAuthority : Authority.ArtifactAuthorityBoundary
    fusionPerformanceArtifactAuthority : Authority.ArtifactAuthorityBoundary

open MagneticConfinementExperimentalAuthority public

record MagneticConfinementAuthorityBoundary : Set where
  constructor magnetic-confinement-authority-boundary
  field
    citationAuthorityEqualsArtifactAuthority : Bool
    citationAuthorityEqualsArtifactAuthorityIsFalse :
      citationAuthorityEqualsArtifactAuthority ≡ false

    equilibriumCitationAloneSuppliesReconstructionArtifact : Bool
    equilibriumCitationAloneSuppliesReconstructionArtifactIsFalse :
      equilibriumCitationAloneSuppliesReconstructionArtifact ≡ false

    transportCitationAloneSuppliesMeasuredTransport : Bool
    transportCitationAloneSuppliesMeasuredTransportIsFalse :
      transportCitationAloneSuppliesMeasuredTransport ≡ false

    performanceCitationAloneSuppliesFusionPerformance : Bool
    performanceCitationAloneSuppliesFusionPerformanceIsFalse :
      performanceCitationAloneSuppliesFusionPerformance ≡ false

    colliderAuthorityDisciplineReusableWithoutColliderDynamics : Bool
    colliderAuthorityDisciplineReusableWithoutColliderDynamicsIsTrue :
      colliderAuthorityDisciplineReusableWithoutColliderDynamics ≡ true

canonicalMagneticConfinementAuthorityBoundary :
  MagneticConfinementAuthorityBoundary
canonicalMagneticConfinementAuthorityBoundary =
  magnetic-confinement-authority-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
