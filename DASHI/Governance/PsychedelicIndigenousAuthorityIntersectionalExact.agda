module DASHI.Governance.PsychedelicIndigenousAuthorityIntersectionalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous
import DASHI.Governance.DrugGovernanceIntersectionalAuthorityExact as Intersectional
import DASHI.Biology.KluverFormConstantPsychedelicBoundaryExact as Kluver

------------------------------------------------------------------------
-- PSYCHEDELIC x INDIGENOUS AUTHORITY x INTERSECTIONAL BOUNDARY
--
-- Biomedical psychedelic science, neural phenomenology, Indigenous ceremonial
-- knowledge and commercial extraction are different authority surfaces.
-- Indigenous knowledge is not a generic content reservoir available whenever
-- biomedical research discovers a related molecule or phenomenology.
------------------------------------------------------------------------

data PsychedelicKnowledgeSurface : Set where
  biomedicalClinicalSurface
  neurophenomenologySurface
  indigenousCeremonialKnowledgeSurface
  commercialExtractionSurface
  publicPolicySurface
  : PsychedelicKnowledgeSurface

data AuthorityRequirement : Set where
  clinicalEvidenceAuthority
  participantConsentAuthority
  communityGovernanceAuthority
  culturalProtocolAuthority
  sovereignPermissionAuthority
  benefitSharingAuthority
  intellectualPropertyAuthority
  ecologicalStewardshipAuthority
  : AuthorityRequirement

record PsychedelicAuthorityRoute : Set where
  constructor psychedelicAuthorityRoute
  field
    surface : PsychedelicKnowledgeSurface
    requiredAuthority : AuthorityRequirement
    provenanceReference : String
    permissionReference : String
    benefitReference : String
    authorityTransferBySimilarity : Bool
    authorityTransferBySimilarityIsFalse :
      authorityTransferBySimilarity ≡ false

open PsychedelicAuthorityRoute public

indigenousCeremonialRoute : PsychedelicAuthorityRoute
indigenousCeremonialRoute = psychedelicAuthorityRoute
  indigenousCeremonialKnowledgeSurface
  sovereignPermissionAuthority
  "community/origin provenance remains explicit"
  "community protocol / sovereign permission required"
  "benefit-sharing and reciprocity remain independent obligations"
  false refl

biomedicalRoute : PsychedelicAuthorityRoute
biomedicalRoute = psychedelicAuthorityRoute
  biomedicalClinicalSurface
  clinicalEvidenceAuthority
  "biomedical trial/source provenance"
  "participant/research permissions"
  "clinical benefit/risk governance"
  false refl

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

intersectionalBoundary : Intersectional.DrugGovernanceIntersectionalBoundary
intersectionalBoundary = Intersectional.canonicalDrugGovernanceIntersectionalBoundary

kluverBoundary : Kluver.KluverPsychedelicBoundary
kluverBoundary = Kluver.canonicalKluverPsychedelicBoundary

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ClinicalEfficacyPromotesCeremonialPermission : Set where

data IndigenousUsePromotesCommercialPropertyRight : Set where

data FormConstantPromotesIndigenousMeaning : Set where

data PublishedDescriptionPromotesCommunityConsent : Set where

clinicalEfficacyDoesNotPromoteCeremonialPermission :
  ClinicalEfficacyPromotesCeremonialPermission → ⊥
clinicalEfficacyDoesNotPromoteCeremonialPermission ()

indigenousUseDoesNotPromoteCommercialPropertyRight :
  IndigenousUsePromotesCommercialPropertyRight → ⊥
indigenousUseDoesNotPromoteCommercialPropertyRight ()

formConstantDoesNotPromoteIndigenousMeaning :
  FormConstantPromotesIndigenousMeaning → ⊥
formConstantDoesNotPromoteIndigenousMeaning ()

publishedDescriptionDoesNotPromoteCommunityConsent :
  PublishedDescriptionPromotesCommunityConsent → ⊥
publishedDescriptionDoesNotPromoteCommunityConsent ()

record PsychedelicIndigenousIntersectionalBoundary : Set where
  constructor psychedelicIndigenousIntersectionalBoundary
  field
    psychedelicScienceMayRequireMultipleAuthoritySurfaces : Bool
    psychedelicScienceMayRequireMultipleAuthoritySurfacesIsTrue :
      psychedelicScienceMayRequireMultipleAuthoritySurfaces ≡ true
    biomedicalApprovalCreatesIndigenousPermission : Bool
    biomedicalApprovalCreatesIndigenousPermissionIsFalse :
      biomedicalApprovalCreatesIndigenousPermission ≡ false
    neuralPhenomenologyDeterminesCeremonialMeaning : Bool
    neuralPhenomenologyDeterminesCeremonialMeaningIsFalse :
      neuralPhenomenologyDeterminesCeremonialMeaning ≡ false
    commercializationAutomaticallyOwnsTraditionalKnowledge : Bool
    commercializationAutomaticallyOwnsTraditionalKnowledgeIsFalse :
      commercializationAutomaticallyOwnsTraditionalKnowledge ≡ false
    equityAndEpistemicJusticeRemainIndependentAxes : Bool
    equityAndEpistemicJusticeRemainIndependentAxesIsTrue :
      equityAndEpistemicJusticeRemainIndependentAxes ≡ true

canonicalPsychedelicIndigenousIntersectionalBoundary :
  PsychedelicIndigenousIntersectionalBoundary
canonicalPsychedelicIndigenousIntersectionalBoundary =
  psychedelicIndigenousIntersectionalBoundary
    true refl
    false refl
    false refl
    false refl
    true refl
