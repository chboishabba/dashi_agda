module DASHI.Cognition.Teleodynamics.TeleodynamicAttentionAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.MultiResolutionAttentionFutureSufficiencyExact as Multi
import DASHI.Cognition.Teleodynamics.TeleodynamicsPrincipiaTwoExact as T

------------------------------------------------------------------------
-- TELEODYNAMIC ATTENTION ADAPTER
--
-- Michels' aboutness/control scalar is not definitionally an LLM attention
-- profile, representation resolution, accessibility breadth, or query selector.
------------------------------------------------------------------------

record TeleodynamicAttentionAdapter : Set where
  constructor teleodynamicAttentionAdapter
  field
    aboutnessControlLabel : String
    representationResolutionLabel : String
    accessibilityBreadthLabel : String
    querySelectionLabel : String
    localResidualLabel : String

record TeleodynamicAttentionBoundary : Set where
  constructor teleodynamicAttentionBoundary
  field
    aboutnessEqualsResolution : Bool
    aboutnessEqualsAccessibility : Bool
    aboutnessEqualsQuerySelector : Bool
    sourceAboutnessCreatesSemanticSufficiency : Bool
    multiResolutionOwnerReused : Bool

open TeleodynamicAttentionBoundary public

canonicalTeleodynamicAttentionBoundary : TeleodynamicAttentionBoundary
canonicalTeleodynamicAttentionBoundary =
  teleodynamicAttentionBoundary false false false false true

canonicalTeleodynamicAttentionAdapter : TeleodynamicAttentionAdapter
canonicalTeleodynamicAttentionAdapter =
  teleodynamicAttentionAdapter
    "Principia-II aboutness/control coordinate"
    "LLM representation resolution"
    "LLM accessibility breadth"
    "query-indexed selector"
    "fine local residual"
