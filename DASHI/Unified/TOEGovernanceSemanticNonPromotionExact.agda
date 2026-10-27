module DASHI.Unified.TOEGovernanceSemanticNonPromotionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.TetralemmaBridge as Tetralemma
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.ControlCardCore as Control
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Education.DigitalESDNormativeStandardsAtlasExact as Standards
import DASHI.Interop.SensibLawSemanticPromotionPolicy as SensibLaw

------------------------------------------------------------------------
-- TOE GOVERNANCE HANDOFF.
--
-- This module reuses existing owners.
-- It does not define a new truth lattice.
-- It does not define a new authority system.
-- It does not define a new standards system.
-- It imports the Digital ESD standards atlas without editing that surface.
--
-- Actionstep is retained only as an external workflow label here.
-- No Actionstep label or workflow state creates legal authority.
------------------------------------------------------------------------

toeGovernanceStandards : List Standards.StandardLens
toeGovernanceStandards =
  Standards.iso9001-2026
  ∷ Standards.isoIEC42001-2023
  ∷ Standards.isoIEC27001-2022
  ∷ Standards.isoIEC27701-2025
  ∷ Standards.isoIEC23894-2023
  ∷ Standards.iso9241-110-2020
  ∷ Standards.nistAIRMF10
  ∷ Standards.itil4
  ∷ Standards.sixSigmaDMAIC
  ∷ []

actionstepWorkflowBoundary : Authority.AuthorityNonPromotionBundle
actionstepWorkflowBoundary =
  Authority.mkClosedAuthorityNonPromotionBundle
    "Actionstep external workflow label does not create legal, truth, theorem, runtime, or external authority"

actionstepLegalAuthorityClosed :
  Authority.legalAuthorityFlag actionstepWorkflowBoundary ≡ false
actionstepLegalAuthorityClosed =
  Authority.legalAuthorityFlagIsFalse actionstepWorkflowBoundary

actionstepAnyAuthorityClosed :
  Authority.promotesAnyAuthority actionstepWorkflowBoundary ≡ false
actionstepAnyAuthorityClosed =
  Authority.promotesAnyAuthorityIsFalse actionstepWorkflowBoundary

sensibLawLegalAuthorityClosed :
  Authority.legalAuthorityFlag SensibLaw.semanticPromotionAuthorityBoundary ≡ false
sensibLawLegalAuthorityClosed =
  SensibLaw.semantic-promotion-legal-authority-closed

sensibLawAnyAuthorityClosed :
  Authority.promotesAnyAuthority SensibLaw.semanticPromotionAuthorityBoundary ≡ false
sensibLawAnyAuthorityClosed =
  SensibLaw.semantic-promotion-all-authority-closed

heuristicOnlyCannotPromote :
  ∀ heuristic-for heuristic-against target source →
  SensibLaw.promote
    (SensibLaw.heuristicCandidate
      heuristic-for heuristic-against target source)
  ≡ Tetralemma.neither
heuristicOnlyCannotPromote =
  SensibLaw.heuristic-only-abstains

standardMentionCannotCreateConformity :
  Standards.StandardMentionCreatesConformity → ⊥
standardMentionCannotCreateConformity =
  Standards.standardMentionDoesNotCreateConformity

claimedConformityCannotCreateCertification :
  Standards.ClaimedConformityCreatesCertifiedConformity → ⊥
claimedConformityCannotCreateCertification =
  Standards.claimedConformityDoesNotCreateCertifiedConformity

citationCannotCreateProof :
  Attribution.CitationCreatesProof → ⊥
citationCannotCreateProof =
  Attribution.citationDoesNotCreateProof

citationCannotCreateAuthority :
  Attribution.CitationCreatesDomainAuthority → ⊥
citationCannotCreateAuthority =
  Attribution.citationDoesNotCreateAuthority

record GovernancePreconditions : Set₁ where
  field
    semanticPolicy : SensibLaw.SemanticPromotionPolicySurface
    orchestrationSurface : Control.ControlCardSurface
    standardsLenses : List Standards.StandardLens
    attributionInvariant : Attribution.AttributionSnowballBoundary
    actionstepBoundary : Authority.AuthorityNonPromotionBundle
open GovernancePreconditions public

canonicalGovernancePreconditions : GovernancePreconditions
canonicalGovernancePreconditions =
  record
    { semanticPolicy = SensibLaw.semanticPromotionPolicySurface
    ; orchestrationSurface = Control.canonicalControlCardSurface
    ; standardsLenses = toeGovernanceStandards
    ; attributionInvariant = Attribution.canonicalAttributionSnowballBoundary
    ; actionstepBoundary = actionstepWorkflowBoundary
    }

record GovernancePostconditions : Set₁ where
  field
    heuristicEvidenceCannotPromote :
      ∀ heuristic-for heuristic-against target source →
      SensibLaw.promote
        (SensibLaw.heuristicCandidate
          heuristic-for heuristic-against target source)
      ≡ Tetralemma.neither

    semanticGateLegalAuthorityClosed :
      Authority.legalAuthorityFlag SensibLaw.semanticPromotionAuthorityBoundary
      ≡ false

    semanticGateAllAuthorityClosed :
      Authority.promotesAnyAuthority SensibLaw.semanticPromotionAuthorityBoundary
      ≡ false

    actionstepWorkflowLegalAuthorityClosed :
      Authority.legalAuthorityFlag actionstepWorkflowBoundary ≡ false

    actionstepWorkflowAllAuthorityClosed :
      Authority.promotesAnyAuthority actionstepWorkflowBoundary ≡ false

    standardsMentionDoesNotCreateConformity :
      Standards.StandardMentionCreatesConformity → ⊥

    standardsClaimDoesNotCreateCertification :
      Standards.ClaimedConformityCreatesCertifiedConformity → ⊥

    sourceCitationDoesNotCreateProof :
      Attribution.CitationCreatesProof → ⊥

    sourceCitationDoesNotCreateAuthority :
      Attribution.CitationCreatesDomainAuthority → ⊥
open GovernancePostconditions public

canonicalGovernancePostconditions : GovernancePostconditions
canonicalGovernancePostconditions =
  record
    { heuristicEvidenceCannotPromote = heuristicOnlyCannotPromote
    ; semanticGateLegalAuthorityClosed = sensibLawLegalAuthorityClosed
    ; semanticGateAllAuthorityClosed = sensibLawAnyAuthorityClosed
    ; actionstepWorkflowLegalAuthorityClosed = actionstepLegalAuthorityClosed
    ; actionstepWorkflowAllAuthorityClosed = actionstepAnyAuthorityClosed
    ; standardsMentionDoesNotCreateConformity = standardMentionCannotCreateConformity
    ; standardsClaimDoesNotCreateCertification = claimedConformityCannotCreateCertification
    ; sourceCitationDoesNotCreateProof = citationCannotCreateProof
    ; sourceCitationDoesNotCreateAuthority = citationCannotCreateAuthority
    }

record TOEGovernanceZKPFrame : Set₁ where
  field
    objective : String
    risk : String
    contract : String
    state : String
    lattice : String
    policy : String
    governance : String
    failure : String
    preconditions : GovernancePreconditions
    invariants : GovernancePostconditions
    postcondition : String
    architectureReading : String
open TOEGovernanceZKPFrame public

canonicalTOEGovernanceZKPFrame : TOEGovernanceZKPFrame
canonicalTOEGovernanceZKPFrame =
  record
    { objective =
        "Connect legal and compliance governance evidence to the TOE without semantic or authority promotion"
    ; risk =
        "A workflow label, heuristic hint, standards reference, citation, or compliance artifact is mistaken for legal truth or authority"
    ; contract =
        "Reuse the SensibLaw structural promotion gate, ControlCard fail-closed orchestration, authority non-promotion core, standards lenses, and attribution invariant"
    ; state =
        "Candidates retain structural evidence, heuristic evidence, provenance, workflow context, standards references, and authority boundaries as separate coordinates"
    ; lattice =
        "The existing tetralemma is the only canonical semantic promotion lattice used by this handoff"
    ; policy =
        "Heuristic evidence cannot promote. Standards references do not certify conformity. Citations do not create proof or authority"
    ; governance =
        "TOE imports exact governance receipts. External workflow systems remain adapters. Domain authority requires a separate accepted artifact"
    ; failure =
        "Any direct workflow-label, heuristic, citation, or standards-reference promotion to legal authority violates this handoff"
    ; preconditions = canonicalGovernancePreconditions
    ; invariants = canonicalGovernancePostconditions
    ; postcondition =
        "The TOE can consume governance evidence while legal, truth, theorem, runtime, empirical, and external authority remain fail-closed unless separately supplied"
    ; architectureReading =
        "C4 and PlantUML may describe component and handoff structure. Diagrams are documentation only and do not create proof authority"
    }

record TOEGovernanceHandoff : Set₁ where
  field
    frame : TOEGovernanceZKPFrame
    semanticPolicy : SensibLaw.SemanticPromotionPolicySurface
    controlSurface : Control.ControlCardSurface
    authorityBoundary : Authority.AuthorityNonPromotionBundle
    standards : List Standards.StandardLens
    attributionBoundary : Attribution.AttributionSnowballBoundary
    postconditions : GovernancePostconditions
open TOEGovernanceHandoff public

canonicalTOEGovernanceHandoff : TOEGovernanceHandoff
canonicalTOEGovernanceHandoff =
  record
    { frame = canonicalTOEGovernanceZKPFrame
    ; semanticPolicy = SensibLaw.semanticPromotionPolicySurface
    ; controlSurface = Control.canonicalControlCardSurface
    ; authorityBoundary = SensibLaw.semanticPromotionAuthorityBoundary
    ; standards = toeGovernanceStandards
    ; attributionBoundary = Attribution.canonicalAttributionSnowballBoundary
    ; postconditions = canonicalGovernancePostconditions
    }
