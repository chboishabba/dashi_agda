module DASHI.Culture.CulturalTriadGovernanceIntegration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Culture.CulturalTriadOperatorBoundary as Triad
import DASHI.Culture.CulturalProvenanceBoundaryCore as Provenance
import DASHI.Promotion.ExplanationAuthorityBoundaryCore as Explanation
import DASHI.Promotion.AuthorityBoundaryCore as Authority

record CulturalTriadGovernanceIntegration : Set where
  constructor mkCulturalTriadGovernanceIntegration
  field
    label : String
    provenanceBoundary : Provenance.CulturalProvenanceBoundary
    explanationBoundary : Explanation.ExplanationAuthorityBoundary
    culturalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    legalAuthorityReceipt : Authority.AuthorityBoundaryReceipt
    candidateTriadRoute : Triad.CulturalTriadOperatorRoute
    neutralTriadBlocked : Bool
    theologyPromotionBlocked : Bool
    monocultureCompressionBlocked : Bool
    enemyCodingDominationBlocked : Bool
    politicalAuthorityBlocked : Bool
    legalAuthorityBlocked : Bool
    integrationHolds : Bool
    integrationHoldsIsTrue : integrationHolds ≡ true

open CulturalTriadGovernanceIntegration public

canonicalCulturalTriadGovernanceIntegration : CulturalTriadGovernanceIntegration
canonicalCulturalTriadGovernanceIntegration =
  mkCulturalTriadGovernanceIntegration
    "cultural triad governance integration"
    Provenance.canonicalCulturalProvenanceBoundary
    Explanation.canonicalExplanationAuthorityBoundary
    Authority.canonicalCulturalAuthorityBoundaryReceipt
    Authority.canonicalLegalAuthorityBoundaryReceipt
    Triad.candidateOnlyTriadOperatorRoute
    true true true true true true true refl
