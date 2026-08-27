module DASHI.Governance.FirstNationsOwnedEvidenceContractExact where

open import DASHI.Core.Prelude
import DASHI.Governance.IndigenousAuthoritySourceRegistryExact as Sources
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Envelope

------------------------------------------------------------------------
-- FIRST NATIONS EVIDENCE AUTHORITY: COMPATIBILITY / ROUTING BOUNDARY
--
-- Structural calibration:
-- - FNIGC OCAP®: Ownership, Control, Access, Possession; specifically First
--   Nations. Stable institutional source; no DOI asserted.
-- - Carroll et al. 2020, CARE Principles for Indigenous Data Governance,
--   DOI 10.5334/dsj-2020-043.
-- - Local Contexts TK Labels: Provenance / Protocol / Permission families;
--   stable institutional source, no DOI asserted.
--
-- IMPORTANT CORRECTION: provenance/ownership alone does NOT authorize every
-- situated, land-management or normative use.  The richer
-- IndigenousAuthorityEnvelopeExact carries governance, protocol and permission
-- separately.  This module retains the older provenance/use vocabulary only as
-- a compatibility surface for clearly bounded routes.
------------------------------------------------------------------------

data EvidenceProvenance : Set where
  firstNationsOwned
  firstNationsCoAuthored
  firstNationsInstitutional
  externalHistoricalReconstruction
  externalSecondaryInterpretation
  : EvidenceProvenance

data EvidenceUse : Set where
  bibliographicBackground
  comparativeContext
  situatedKnowledgeAuthority
  landManagementAuthority
  normativeAuthority
  : EvidenceUse

-- Only low-authority background/comparison routes are inhabited here.
-- Higher-authority uses must use the richer envelope/protocol/permission
-- machinery rather than provenance alone.
data AuthorizedFor : EvidenceProvenance → EvidenceUse → Set where
  externalHistoricalBackground :
    AuthorizedFor externalHistoricalReconstruction bibliographicBackground
  externalHistoricalComparison :
    AuthorizedFor externalHistoricalReconstruction comparativeContext
  externalSecondaryBackground :
    AuthorizedFor externalSecondaryInterpretation bibliographicBackground
  externalSecondaryComparison :
    AuthorizedFor externalSecondaryInterpretation comparativeContext

ownedProvenanceAloneDoesNotAuthorizeSituatedKnowledge :
  AuthorizedFor firstNationsOwned situatedKnowledgeAuthority → ⊥
ownedProvenanceAloneDoesNotAuthorizeSituatedKnowledge ()

ownedProvenanceAloneDoesNotAuthorizeLandManagement :
  AuthorizedFor firstNationsOwned landManagementAuthority → ⊥
ownedProvenanceAloneDoesNotAuthorizeLandManagement ()

ownedProvenanceAloneDoesNotAuthorizeNormativeAuthority :
  AuthorizedFor firstNationsOwned normativeAuthority → ⊥
ownedProvenanceAloneDoesNotAuthorizeNormativeAuthority ()

externalHistorianDoesNotBecomeSituatedAuthority :
  AuthorizedFor externalHistoricalReconstruction situatedKnowledgeAuthority → ⊥
externalHistorianDoesNotBecomeSituatedAuthority ()

externalHistorianDoesNotBecomeLandManagementAuthority :
  AuthorizedFor externalHistoricalReconstruction landManagementAuthority → ⊥
externalHistorianDoesNotBecomeLandManagementAuthority ()

externalSecondaryDoesNotBecomeNormativeAuthority :
  AuthorizedFor externalSecondaryInterpretation normativeAuthority → ⊥
externalSecondaryDoesNotBecomeNormativeAuthority ()

record EvidenceRoute : Set₁ where
  constructor evidenceRoute
  field
    provenance : EvidenceProvenance
    use : EvidenceUse
    authorization : AuthorizedFor provenance use

externalHistoricalBackgroundRoute : EvidenceRoute
externalHistoricalBackgroundRoute =
  evidenceRoute externalHistoricalReconstruction bibliographicBackground
    externalHistoricalBackground

careSource : Sources.SourceReference
careSource = Sources.care2020

ocapSource : Sources.SourceReference
ocapSource = Sources.ocapFNIGC

localContextsSource : Sources.SourceReference
localContextsSource = Sources.localContextsTK

record FirstNationsEvidenceBoundary : Set where
  constructor firstNationsEvidenceBoundary
  field
    provenanceAloneDeterminesPermission : Bool
    provenanceAloneDeterminesPermissionIsFalse : provenanceAloneDeterminesPermission ≡ false
    ownershipAloneSelfAuthorizesNormativeUse : Bool
    ownershipAloneSelfAuthorizesNormativeUseIsFalse :
      ownershipAloneSelfAuthorizesNormativeUse ≡ false
    externalReconstructionSelfAuthorizesSituatedKnowledge : Bool
    externalReconstructionSelfAuthorizesSituatedKnowledgeIsFalse :
      externalReconstructionSelfAuthorizesSituatedKnowledge ≡ false
    externalReconstructionSelfAuthorizesLandManagement : Bool
    externalReconstructionSelfAuthorizesLandManagementIsFalse :
      externalReconstructionSelfAuthorizesLandManagement ≡ false
    externalSecondarySourceSelfAuthorizesNormativeClaim : Bool
    externalSecondarySourceSelfAuthorizesNormativeClaimIsFalse :
      externalSecondarySourceSelfAuthorizesNormativeClaim ≡ false
    ocapIsUniversalAllIndigenousFramework : Bool
    ocapIsUniversalAllIndigenousFrameworkIsFalse :
      ocapIsUniversalAllIndigenousFramework ≡ false

canonicalFirstNationsEvidenceBoundary : FirstNationsEvidenceBoundary
canonicalFirstNationsEvidenceBoundary =
  firstNationsEvidenceBoundary false refl false refl false refl false refl false refl false refl
