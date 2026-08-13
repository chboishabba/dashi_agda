module DASHI.Cognition.PNF.MultiResolutionAttentionFutureSufficiencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source boundary.
--
-- DeepSeek-AI, "DeepSeek-V4: Towards Highly Efficient Million-Token Context
-- Intelligence", arXiv:2606.19348v1 (2026).  No DOI is asserted here.
--
-- This module does not claim to formalize DeepSeek-V4 itself.  It extracts the
-- mathematically relevant architecture pattern: global compression, query-
-- indexed accessibility, and a fine local residual are independent coordinates.
------------------------------------------------------------------------

deepSeekV4Author : String
deepSeekV4Author = "DeepSeek-AI"

deepSeekV4Title : String
deepSeekV4Title = "DeepSeek-V4: Towards Highly Efficient Million-Token Context Intelligence"

deepSeekV4ArXiv : String
deepSeekV4ArXiv = "arXiv:2606.19348v1"

data RepresentationResolution : Set where
  fineResolution mediumResolution coarseResolution : RepresentationResolution

data AccessibilityBreadth : Set where
  narrowAccessibility broadAccessibility : AccessibilityBreadth

record AttentionProfile : Set where
  constructor attentionProfile
  field
    resolution : RepresentationResolution
    accessibility : AccessibilityBreadth

open AttentionProfile public

-- Type-separated architecture profiles: these record the two independent axes,
-- not performance or semantic authority.
csaProfile : AttentionProfile
csaProfile = attentionProfile mediumResolution narrowAccessibility

hcaProfile : AttentionProfile
hcaProfile = attentionProfile coarseResolution broadAccessibility

csaAndHcaDifferInResolution : resolution csaProfile ≡ resolution hcaProfile → ⊥
csaAndHcaDifferInResolution ()

csaAndHcaDifferInAccessibility : accessibility csaProfile ≡ accessibility hcaProfile → ⊥
csaAndHcaDifferInAccessibility ()

------------------------------------------------------------------------
-- General theorem: coarse global carrier + query-selected medium carrier +
-- fine local residual is future/consumer sufficient whenever every fine
-- observation factors through that three-part representation.
------------------------------------------------------------------------

record MultiResolutionConsumerSystem
    (Fine Coarse Selected Local Query Observation : Set) : Set₁ where
  constructor multiResolutionConsumerSystem
  field
    compressGlobal : Fine → Coarse
    selectForQuery : Query → Coarse → Selected
    localResidual : Fine → Local
    observeFine : Query → Fine → Observation
    observeCompressed : Query → Selected → Local → Observation
    factorsForEveryQuery :
      (query : Query) → (fine : Fine) →
      observeFine query fine
      ≡ observeCompressed query
          (selectForQuery query (compressGlobal fine))
          (localResidual fine)

open MultiResolutionConsumerSystem public

sameRetainedCarrierImpliesSameConsumerObservation :
  ∀ {Fine Coarse Selected Local Query Observation}
    (system : MultiResolutionConsumerSystem
      Fine Coarse Selected Local Query Observation)
    (query : Query)
    {left right : Fine} →
  compressGlobal system left ≡ compressGlobal system right →
  localResidual system left ≡ localResidual system right →
  observeFine system query left ≡ observeFine system query right
sameRetainedCarrierImpliesSameConsumerObservation system query {left} {right}
  coarseEqual localEqual
  with coarseEqual | localEqual
... | refl | refl =
  trans
    (factorsForEveryQuery system query left)
    (sym (factorsForEveryQuery system query right))

------------------------------------------------------------------------
-- Query family theorem.  This is the exact finite form of the desired
-- multi-resolution future-sufficiency criterion: equality of the retained
-- global/local carrier implies equality for every admissible consumer query.
------------------------------------------------------------------------

record MultiResolutionFutureSufficient
    {Fine Coarse Selected Local Query Observation : Set}
    (system : MultiResolutionConsumerSystem
      Fine Coarse Selected Local Query Observation)
    : Set₁ where
  constructor multiResolutionFutureSufficient
  field
    retainedKernelSafe :
      ∀ {left right : Fine} →
      compressGlobal system left ≡ compressGlobal system right →
      localResidual system left ≡ localResidual system right →
      (query : Query) →
      observeFine system query left ≡ observeFine system query right

open MultiResolutionFutureSufficient public

factorizationCertifiesMultiResolutionFutureSufficiency :
  ∀ {Fine Coarse Selected Local Query Observation}
    (system : MultiResolutionConsumerSystem
      Fine Coarse Selected Local Query Observation) →
  MultiResolutionFutureSufficient system
factorizationCertifiesMultiResolutionFutureSufficiency system =
  multiResolutionFutureSufficient
    (λ coarseEqual localEqual query →
      sameRetainedCarrierImpliesSameConsumerObservation
        system query coarseEqual localEqual)

------------------------------------------------------------------------
-- Boundary: access is not retention.  A selector may hide a represented item
-- without proving that the item was absent from the compressed carrier.
------------------------------------------------------------------------

record RepresentedButInaccessible
    {Fine Coarse Selected Query : Set}
    (compress : Fine → Coarse)
    (select : Query → Coarse → Selected)
    : Set₁ where
  constructor representedButInaccessible
  field
    left right : Fine
    query : Query
    representedDifferently : compress left ≡ compress right → ⊥
    selectedIdentically : select query (compress left) ≡ select query (compress right)

open RepresentedButInaccessible public
