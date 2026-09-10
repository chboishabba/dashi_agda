module DASHI.Astronomy.LocalGroupAttributionRelationshipExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupVirtualObservatoryFirstLightSourceExact
open import DASHI.Astronomy.LocalGroupObservationFrameProvenanceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Attribution edges remain separate from scientific-source edges.
------------------------------------------------------------------------

data AttributionRelation : Set where
  postedBy : AttributionRelation
  attachedTo : AttributionRelation
  projectClaimBy : AttributionRelation
  citesScientificSource : AttributionRelation
  independentlyVerifiedBy : AttributionRelation

record AttributionEdge : Set where
  constructor attributionEdge
  field
    relation : AttributionRelation
    edgeSourceLabel : String
    edgeTargetLabel : String
    note : String

open AttributionEdge public

firstLightAttributionEdges : List AttributionEdge
firstLightAttributionEdges =
  attributionEdge postedBy
    "Virtual Observatory first-light post"
    "Poppie / NOUS"
    "visible display attribution from supplied private-post screenshot, 2026-09-07 23:38"
  ∷ attributionEdge attachedTo
    "first-light.png"
    "Virtual Observatory first-light post"
    "attached rendering; CDN delivery URL is not promoted to canonical private-post locator"
  ∷ attributionEdge projectClaimBy
    "Virtual Observatory first-light benchmark summary"
    "Poppie / NOUS"
    "poster/project attribution; does not transfer authorship of cited papers"
  ∷ attributionEdge citesScientificSource
    "LMC six-component benchmark claim"
    "Kallivayalil et al. 2013"
    "comparison-source relationship"
  ∷ attributionEdge citesScientificSource
    "Sagittarius phase-space benchmark claim"
    "Vasiliev, Belokurov, Erkal 2021"
    "comparison-source relationship"
  ∷ attributionEdge citesScientificSource
    "Sgr A* proper-motion benchmark claim"
    "Reid and Brunthaler 2020"
    "comparison-source relationship"
  ∷ attributionEdge citesScientificSource
    "Local Group census reconstruction claim"
    "McConnachie 2012"
    "catalogue/comparison-source relationship"
  ∷ []

postAttributionTransfersPaperAuthorship : Bool
postAttributionTransfersPaperAuthorship = false

postAttributionTransfersPaperAuthorshipIsFalse :
  postAttributionTransfersPaperAuthorship ≡ false
postAttributionTransfersPaperAuthorshipIsFalse = refl

citationTransfersProjectAuthorshipToPaperAuthors : Bool
citationTransfersProjectAuthorshipToPaperAuthors = false

citationTransfersProjectAuthorshipToPaperAuthorsIsFalse :
  citationTransfersProjectAuthorshipToPaperAuthors ≡ false
citationTransfersProjectAuthorshipToPaperAuthorsIsFalse = refl
