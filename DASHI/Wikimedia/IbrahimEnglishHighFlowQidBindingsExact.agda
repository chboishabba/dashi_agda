module DASHI.Wikimedia.IbrahimEnglishHighFlowQidBindingsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas

------------------------------------------------------------------------
-- IBRAHIM HIGH-FLOW QID BINDINGS
--
-- These bindings reuse the existing ScientificReferenceEntity/QidResolution
-- layer.  They are not a second QID ontology.
--
-- Identity checks performed 2026-09-10 against Wikidata:
-- Community  Q177634
-- State      Q7275
-- Science    Q336
-- Health care Q31207
-- Fossil fuel Q12748
-- Philosophy Q5891
--
-- QID identity remains external metadata only: it creates no source truth,
-- theorem identity, proof authority, or historical Ibrahim-edge identity.
------------------------------------------------------------------------

communityEntity : Atlas.ScientificReferenceEntity
communityEntity =
  Atlas.verified "community" Atlas.conceptEntity "Q177634"
    "Wikidata identity checked 2026-09-10"

stateEntity : Atlas.ScientificReferenceEntity
stateEntity =
  Atlas.verified "state" Atlas.conceptEntity "Q7275"
    "Wikidata polity/state identity checked 2026-09-10"

scienceEntity : Atlas.ScientificReferenceEntity
scienceEntity =
  Atlas.verified "science" Atlas.conceptEntity "Q336"
    "Wikidata identity checked 2026-09-10"

healthCareEntity : Atlas.ScientificReferenceEntity
healthCareEntity =
  Atlas.verified "health care" Atlas.conceptEntity "Q31207"
    "Wikidata identity checked 2026-09-10"

fossilFuelEntity : Atlas.ScientificReferenceEntity
fossilFuelEntity =
  Atlas.verified "fossil fuel" Atlas.conceptEntity "Q12748"
    "Wikidata identity checked 2026-09-10"

philosophyEntity : Atlas.ScientificReferenceEntity
philosophyEntity =
  Atlas.verified "philosophy" Atlas.conceptEntity "Q5891"
    "Wikidata identity checked 2026-09-10"

knowledgeEntity : Atlas.ScientificReferenceEntity
knowledgeEntity =
  Atlas.verified "knowledge" Atlas.conceptEntity "Q9081"
    "Wikidata identity checked 2026-09-10; current EN Science first conceptual link"

------------------------------------------------------------------------
-- Explicit boundary witness.
------------------------------------------------------------------------

record IbrahimHighFlowQidBoundary : Set where
  constructor ibrahim-high-flow-qid-boundary
  field
    canonicalEntityTypeReused : Bool
    unresolvedStateStillAvailable : Bool
    qidCreatesProofAuthority : Bool
    qidCreatesSourceTruth : Bool
    qidCreatesHistoricalFirstLinkEdge : Bool
open IbrahimHighFlowQidBoundary public

canonicalIbrahimHighFlowQidBoundary : IbrahimHighFlowQidBoundary
canonicalIbrahimHighFlowQidBoundary =
  ibrahim-high-flow-qid-boundary true true false false false

data QidCreatesHistoricalFirstLinkEdge : Set where

qidDoesNotCreateHistoricalEdge : QidCreatesHistoricalFirstLinkEdge → ⊥
qidDoesNotCreateHistoricalEdge ()
