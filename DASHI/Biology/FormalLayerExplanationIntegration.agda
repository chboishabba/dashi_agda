module DASHI.Biology.FormalLayerExplanationIntegration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.FormalLayerExplanationBoundary as BiologyExplanation
import DASHI.Promotion.ExplanationAuthorityBoundaryCore as Shared

record FormalLayerExplanationIntegration : Set where
  constructor mkFormalLayerExplanationIntegration
  field
    label : String
    biologyBoundary : BiologyExplanation.ReaderComprehensionBoundary
    biologyBoundaryIsCanonical : biologyBoundary ≡ BiologyExplanation.canonicalReaderComprehensionBoundary
    sharedBoundary : Shared.ExplanationAuthorityBoundary
    guideProofSeparated : Bool
    proofAuthoritySeparated : Bool
    narrativeDoesNotPromoteAuthority : Bool
    typedStructureDoesNotPromoteEmpiricalTruth : Bool
    integrationHolds : Bool
    integrationHoldsIsTrue : integrationHolds ≡ true

open FormalLayerExplanationIntegration public

canonicalFormalLayerExplanationIntegration : FormalLayerExplanationIntegration
canonicalFormalLayerExplanationIntegration =
  mkFormalLayerExplanationIntegration
    "formal layer explanation integration"
    BiologyExplanation.canonicalReaderComprehensionBoundary refl
    Shared.canonicalExplanationAuthorityBoundary
    true true true true true refl
