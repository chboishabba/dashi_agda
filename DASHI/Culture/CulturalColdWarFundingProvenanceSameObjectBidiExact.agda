module DASHI.Culture.CulturalColdWarFundingProvenanceSameObjectBidiExact where

open import DASHI.Core.Prelude

import DASHI.Culture.CulturalInstitutionalAmplificationCoreExact as Core

------------------------------------------------------------------------
-- SAME-OBJECT FUNDING / CIRCULATION OBSERVATION
--
-- Every coordinate below is indexed by the same literal work.  This prevents
-- composition of a funding receipt for one work with circulation or reception
-- evidence about another work.
------------------------------------------------------------------------

postulate
  Exhibition : Set
  WorkInExhibition : Core.Work → Exhibition → Set
  ExhibitionOrganiser : Exhibition → Core.Institution → Set
  ExhibitionFunding : Exhibition → Core.Funder → Set
  ExhibitionVenue : Exhibition → Core.Venue → Set
  ExhibitionAudience : Exhibition → Core.Audience → Set
  ExhibitionTime : Exhibition → Core.HistoricalTime → Set

record SameExhibitionColdWarObservation
    (work : Core.Work)
    (exhibition : Exhibition) : Set₁ where
  constructor same-exhibition-cold-war-observation
  field
    institution : Core.Institution
    funder : Core.Funder
    venue : Core.Venue
    audience : Core.Audience
    time : Core.HistoricalTime
    contains : WorkInExhibition work exhibition
    organiser : ExhibitionOrganiser exhibition institution
    funding : ExhibitionFunding exhibition funder
    exhibitionVenue : ExhibitionVenue exhibition venue
    exhibitionAudience : ExhibitionAudience exhibition audience
    exhibitionTime : ExhibitionTime exhibition time
    selected : Core.InstitutionalSelection institution work
    circulated : Core.CirculationReceipt institution work venue time
    received : Core.ReceptionReceipt work audience

open SameExhibitionColdWarObservation public

sameObservationProducesAmplification :
  ∀ {work exhibition} →
  (obs : SameExhibitionColdWarObservation work exhibition) →
  Core.FundingReceipt (funder obs) (institution obs) →
  Core.AmplificationEvent work
sameObservationProducesAmplification obs fundingReceipt =
  Core.amplification-event
    (institution obs)
    (funder obs)
    (venue obs)
    (audience obs)
    (time obs)
    (selected obs)
    fundingReceipt
    (circulated obs)
    (received obs)

------------------------------------------------------------------------
-- Typed provenance path.
------------------------------------------------------------------------

postulate HistoricalActor : Set

data ProvenanceEdge : HistoricalActor → HistoricalActor → Set where
  directFunding : ∀ {source recipient} → ProvenanceEdge source recipient
  passThroughFunding : ∀ {source recipient} → ProvenanceEdge source recipient

infixr 5 _∷_
data ProvenancePath : HistoricalActor → HistoricalActor → Set where
  here : ∀ {actor} → ProvenancePath actor actor
  _∷_ : ∀ {source middle target} →
        ProvenanceEdge source middle →
        ProvenancePath middle target →
        ProvenancePath source target

provenancePathCompose :
  ∀ {a b c} → ProvenancePath a b → ProvenancePath b c → ProvenancePath a c
provenancePathCompose here right = right
provenancePathCompose (edge ∷ rest) right = edge ∷ provenancePathCompose rest right

------------------------------------------------------------------------
-- Path existence is not production direction.
------------------------------------------------------------------------

data ProvenancePathCreatesArtistDirection
    (source target : HistoricalActor) : Set where

data ProvenancePathCreatesWorkProduction
    (source target : HistoricalActor)
    (work : Core.Work) : Set where

provenancePathDoesNotCreateArtistDirection :
  ∀ {source target} →
  ProvenancePathCreatesArtistDirection source target → ⊥
provenancePathDoesNotCreateArtistDirection ()

provenancePathDoesNotCreateWorkProduction :
  ∀ {source target work} →
  ProvenancePathCreatesWorkProduction source target work → ⊥
provenancePathDoesNotCreateWorkProduction ()

record CulturalColdWarFundingProvenanceBoundary : Set where
  constructor cultural-cold-war-funding-provenance-boundary
  field
    sameLiteralWorkIndexesObservation : Bool
    provenanceIsPathStructured : Bool
    fundingPathAutomaticallyMeansArtistDirection : Bool
    fundingPathAutomaticallyMeansWorkProduction : Bool

canonicalCulturalColdWarFundingProvenanceBoundary :
  CulturalColdWarFundingProvenanceBoundary
canonicalCulturalColdWarFundingProvenanceBoundary =
  cultural-cold-war-funding-provenance-boundary true true false false
