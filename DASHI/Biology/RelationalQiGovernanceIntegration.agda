module DASHI.Biology.RelationalQiGovernanceIntegration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.RelationalQiBodyMemoryBridge as Qi
import DASHI.Culture.CulturalProvenanceBoundaryCore as Provenance
import DASHI.Promotion.ExplanationAuthorityBoundaryCore as Explanation

record RelationalQiGovernanceIntegration : Set where
  constructor mkRelationalQiGovernanceIntegration
  field
    label : String
    relationalRegistry : Qi.RelationalQiBridgeRegistry
    relationalRegistryIsCanonical : relationalRegistry ≡ Qi.canonicalRelationalQiBridgeRegistry
    provenanceBoundary : Provenance.CulturalProvenanceBoundary
    explanationBoundary : Explanation.ExplanationAuthorityBoundary
    noExtractionInherited : Bool
    noLivingPracticeSubstitutionInherited : Bool
    noUniversalisationInherited : Bool
    noEmpiricalCaptureInherited : Bool
    relationCarrierIsNotSubstance : Bool
    integrationHolds : Bool
    integrationHoldsIsTrue : integrationHolds ≡ true

open RelationalQiGovernanceIntegration public

canonicalRelationalQiGovernanceIntegration : RelationalQiGovernanceIntegration
canonicalRelationalQiGovernanceIntegration =
  mkRelationalQiGovernanceIntegration
    "relational Qi governance integration"
    Qi.canonicalRelationalQiBridgeRegistry refl
    Provenance.canonicalCulturalProvenanceBoundary
    Explanation.canonicalExplanationAuthorityBoundary
    true true true true true true refl
