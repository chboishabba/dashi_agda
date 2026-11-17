module DASHI.Unified.GovernedLegalWorkflowSourceGenealogyTOERegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Unified.GovernedLegalWorkflowSourceGenealogyTOEExact as Handoff
import DASHI.Unified.GovernedLegalWorkflowTOEBridgeExact as Legal
import DASHI.Unified.PNFSourceBoundaryTOEExact as Source
import DASHI.Unifier as Unifier

legalHandoffIsCanonical :
  Handoff.legalWorkflowInvariantHandoff
    Handoff.canonicalGovernedLegalWorkflowSourceGenealogyHandoff
  ≡ Legal.canonicalGovernedLegalWorkflowTOEInvariantHandoff
legalHandoffIsCanonical = refl

sourceBoundaryIsCanonical :
  Handoff.pnfSourceBoundaryReceipt
    Handoff.canonicalGovernedLegalWorkflowSourceGenealogyHandoff
  ≡ Source.canonicalPNFSourceBoundaryTOEReceipt
sourceBoundaryIsCanonical = refl

perceivedIndependenceAliasIsExact :
  Source.PerceivedIndependenceMeansActualIndependence → ⊥
perceivedIndependenceAliasIsExact =
  Handoff.toePerceivedIndependenceDoesNotCreateLegalProvenanceIndependence

repetitionAliasIsExact :
  Source.RepetitionMeansIndependentEvidence → ⊥
repetitionAliasIsExact =
  Handoff.toeRepetitionDoesNotCreateIndependentLegalEvidence

commonSourceAliasIsExact :
  Source.CommonSourceMeansNoEvidence → ⊥
commonSourceAliasIsExact =
  Handoff.toeCommonSourceDependenceDoesNotEraseLegalEvidence

externalSourceTruthAliasIsExact :
  Legal.ExternalSourceClaimImpliesTruthAdmitted → ⊥
externalSourceTruthAliasIsExact =
  Handoff.toeExternalSourceMultiplicityDoesNotAdmitTruth

authorityTruthAliasIsExact :
  Legal.LegalAuthorityCreatesTruthStatus → ⊥
authorityTruthAliasIsExact =
  Handoff.toeLegalAuthorityStillDoesNotCreateTruthAfterGenealogy

reviewApplicabilityAliasIsExact :
  Legal.AcceptedStatusPaysApplicability → ⊥
reviewApplicabilityAliasIsExact =
  Handoff.toeReviewedGenealogyDoesNotPayApplicability

admissionAuthorityAliasIsExact :
  Legal.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
admissionAuthorityAliasIsExact =
  Handoff.toeGenealogyAdmissionDoesNotBecomeLegalSourceAuthority

unifierHandoffIsCanonical :
  Unifier.unifierGovernedLegalWorkflowSourceGenealogyHandoff
  ≡ Handoff.canonicalGovernedLegalWorkflowSourceGenealogyHandoff
unifierHandoffIsCanonical = refl

unifierPerceivedIndependenceAliasIsExact :
  Source.PerceivedIndependenceMeansActualIndependence → ⊥
unifierPerceivedIndependenceAliasIsExact =
  Unifier.unifierLegalPerceivedIndependenceDoesNotCreateProvenanceIndependence

unifierRepetitionAliasIsExact :
  Source.RepetitionMeansIndependentEvidence → ⊥
unifierRepetitionAliasIsExact =
  Unifier.unifierLegalRepetitionDoesNotCreateIndependentEvidence

unifierCommonSourceAliasIsExact :
  Source.CommonSourceMeansNoEvidence → ⊥
unifierCommonSourceAliasIsExact =
  Unifier.unifierLegalCommonSourceDoesNotEraseEvidence
    
candidateSourceAuthorityAliasIsExact :
  Legal.CandidateSourceIsAuthoritative → ⊥
candidateSourceAuthorityAliasIsExact =
  Handoff.toeGenealogyCandidateSourceDoesNotCreateLegalAuthority

sameLegalSystemAuthorityAliasIsExact :
  Legal.SameLegalSystemAutomaticallyMeansAuthority → ⊥
sameLegalSystemAuthorityAliasIsExact =
  Handoff.toeGenealogySameLegalSystemDoesNotCreateLegalAuthority

currentValidityApplicabilityAliasIsExact :
  Legal.CurrentValidityAutomaticallyMeansApplicability → ⊥
currentValidityApplicabilityAliasIsExact =
  Handoff.toeGenealogyCurrentValidityDoesNotCreateApplicability

documentRoleAuthorityAliasIsExact :
  Legal.DocumentRoleSuppliesLegalSourceAuthority → ⊥
documentRoleAuthorityAliasIsExact =
  Handoff.toeGenealogyDocumentRoleDoesNotCreateLegalAuthority
