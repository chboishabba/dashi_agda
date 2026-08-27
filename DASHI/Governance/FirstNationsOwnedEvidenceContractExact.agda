module DASHI.Governance.FirstNationsOwnedEvidenceContractExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FIRST NATIONS-OWNED EVIDENCE AUTHORITY CONTRACT
--
-- This is an authority/governance owner only.  It contains no substantive
-- claim about any First Nations knowledge system, land practice or community.
-- Its purpose is to prevent an external reconstruction, however useful as
-- background, from being silently promoted into First Nations epistemic
-- authority.
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

data AuthorizedFor : EvidenceProvenance → EvidenceUse → Set where
  ownedSituatedKnowledge :
    AuthorizedFor firstNationsOwned situatedKnowledgeAuthority
  ownedLandManagement :
    AuthorizedFor firstNationsOwned landManagementAuthority
  ownedNormative :
    AuthorizedFor firstNationsOwned normativeAuthority
  coauthoredSituatedKnowledge :
    AuthorizedFor firstNationsCoAuthored situatedKnowledgeAuthority
  coauthoredLandManagement :
    AuthorizedFor firstNationsCoAuthored landManagementAuthority
  institutionalSituatedKnowledge :
    AuthorizedFor firstNationsInstitutional situatedKnowledgeAuthority
  institutionalLandManagement :
    AuthorizedFor firstNationsInstitutional landManagementAuthority
  externalHistoricalBackground :
    AuthorizedFor externalHistoricalReconstruction bibliographicBackground
  externalHistoricalComparison :
    AuthorizedFor externalHistoricalReconstruction comparativeContext
  externalSecondaryBackground :
    AuthorizedFor externalSecondaryInterpretation bibliographicBackground
  externalSecondaryComparison :
    AuthorizedFor externalSecondaryInterpretation comparativeContext

externalHistorianDoesNotBecomeSituatedAuthority :
  AuthorizedFor externalHistoricalReconstruction situatedKnowledgeAuthority → ⊥
externalHistorianDoesNotBecomeSituatedAuthority ()

externalHistorianDoesNotBecomeLandManagementAuthority :
  AuthorizedFor externalHistoricalReconstruction landManagementAuthority → ⊥
externalHistorianDoesNotBecomeLandManagementAuthority ()

externalSecondaryDoesNotBecomeNormativeAuthority :
  AuthorizedFor externalSecondaryInterpretation normativeAuthority → ⊥
externalSecondaryDoesNotBecomeNormativeAuthority ()

------------------------------------------------------------------------
-- A claim route must carry the authority actually used.
------------------------------------------------------------------------

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

record FirstNationsEvidenceBoundary : Set where
  constructor firstNationsEvidenceBoundary
  field
    externalReconstructionEqualsFirstNationsOwnedEvidence : Bool
    externalReconstructionEqualsFirstNationsOwnedEvidenceIsFalse :
      externalReconstructionEqualsFirstNationsOwnedEvidence ≡ false
    externalReconstructionSelfAuthorizesSituatedKnowledge : Bool
    externalReconstructionSelfAuthorizesSituatedKnowledgeIsFalse :
      externalReconstructionSelfAuthorizesSituatedKnowledge ≡ false
    externalReconstructionSelfAuthorizesLandManagement : Bool
    externalReconstructionSelfAuthorizesLandManagementIsFalse :
      externalReconstructionSelfAuthorizesLandManagement ≡ false
    externalSecondarySourceSelfAuthorizesNormativeClaim : Bool
    externalSecondarySourceSelfAuthorizesNormativeClaimIsFalse :
      externalSecondarySourceSelfAuthorizesNormativeClaim ≡ false
    sourceOwnershipAndClaimUseAreSeparatelyTyped : Bool
    sourceOwnershipAndClaimUseAreSeparatelyTypedIsTrue :
      sourceOwnershipAndClaimUseAreSeparatelyTyped ≡ true

canonicalFirstNationsEvidenceBoundary : FirstNationsEvidenceBoundary
canonicalFirstNationsEvidenceBoundary =
  firstNationsEvidenceBoundary false refl false refl false refl false refl true refl
