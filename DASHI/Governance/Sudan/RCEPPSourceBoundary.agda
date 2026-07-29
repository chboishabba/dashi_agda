module DASHI.Governance.Sudan.RCEPPSourceBoundary where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Source provenance for the Sudanese Revolutionary Charter.
--
-- Collective author/source:
--   Sudanese Resistance Committees and signatory revolutionary forces,
--   The Revolutionary Charter for Establishing People's Power,
--   English edition dated 11 January 2023.
--   DOI: no DOI is assigned in the supplied edition.
--
-- The supplied PDF is treated as a source document.  This module accepts the
-- citation identity only; it does not assert legal operation, universal popular
-- endorsement, translation perfection or machine-readable artifact authority.
------------------------------------------------------------------------

record RCEPPSourceReceipt : Set where
  constructor rceppSourceReceipt
  field
    collectiveAuthor : String
    title : String
    editionDate : String
    languageEdition : String
    sourceKind : String
    doi : String
    doiAssigned : Bool
    suppliedPageCount : Nat
    authorshipIsCollective : Bool
    translationAuthoritativeClaimed : Bool
    legalOperationClaimed : Bool
    universalEndorsementClaimed : Bool

open RCEPPSourceReceipt public

canonicalRCEPPSourceReceipt : RCEPPSourceReceipt
canonicalRCEPPSourceReceipt =
  rceppSourceReceipt
    "Sudanese Resistance Committees and signatory revolutionary forces (collective authorship as represented by the document)"
    "The Revolutionary Charter for Establishing People's Power"
    "11 January 2023"
    "English edition supplied to this formalisation"
    "political charter / transitional constitutional programme"
    "No DOI assigned in the supplied edition"
    false
    51
    true
    false
    false
    false

canonicalRCEPPCitationBoundary : Authority.CitationAuthorityBoundary
canonicalRCEPPCitationBoundary =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "RCEPP-2023-01-11-English-supplied"
    "Sudanese Resistance Committees and signatory revolutionary forces, The Revolutionary Charter for Establishing People's Power, 11 January 2023; no DOI assigned in supplied edition."
    true
    false
    false
    ("Citation identity is accepted for source anchoring only"
      ∷ "The repository does not carry an authenticated machine-readable charter artifact"
      ∷ "Citation authority is not legal, constitutional or popular-legitimacy authority"
      ∷ [])

canonicalRCEPPCitationHasNoArtifact :
  Authority.CitationAuthorityNoArtifact
canonicalRCEPPCitationHasNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    canonicalRCEPPCitationBoundary
    refl
    refl
    refl

record RCEPPSourceBoundary : Set where
  constructor rceppSourceBoundary
  field
    citationIdentified : Bool
    sourceInterpretationSeparated : Bool
    typedModelSeparated : Bool
    legalAuthorityPromoted : Bool
    politicalAuthorityPromoted : Bool
    empiricalSuccessClaimed : Bool
    translationFinalityClaimed : Bool

canonicalRCEPPSourceBoundary : RCEPPSourceBoundary
canonicalRCEPPSourceBoundary =
  rceppSourceBoundary
    true
    true
    true
    false
    false
    false
    false

canonicalRCEPPSourceGenericReceipt :
  GenericReceipt.GenericReceipt
canonicalRCEPPSourceGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "RCEPP source provenance boundary"
    "DASHI.Governance.Sudan.RCEPPSourceBoundary"
    "canonicalRCEPPSourceReceipt"
    "anchors collective author, title, date, supplied English edition, page count and absent DOI while separating citation authority from artifact and legal authority"
    "translation verification, signatory registry, legal operation, popular endorsement and authenticated machine-readable artifact remain external"
    "agda -i . DASHI/Governance/Sudan/RCEPPSourceBoundary.agda"
