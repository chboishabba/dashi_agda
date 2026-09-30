module DASHI.Governance.TrumpTerritorialSymbolismSourceBoundary2026Exact where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- TRUMP TERRITORIAL SYMBOLISM, 2026
--
-- A social-media map is a documented symbolic/political act.  It is not by
-- itself a treaty, statute, executive annexation instrument, military order or
-- settled U.S. policy.
------------------------------------------------------------------------

trumpMapReuters2026 : Source.AttributedSource
trumpMapReuters2026 = Source.mkNoDOISource
  "Reuters"
  "Iceland summons US ambassador after Trump posts map showing island under American flag"
  "Reuters report carried by Investing.com"
  "2026-09-08"
  "https://www.investing.com/news/world-news/iceland-summons-us-ambassador-after-trump-posts-map-showing-island-under-american-flag-4890870"
  Source.newsSource
  "secondary report that Trump posted a map depicting the U.S., Canada, Greenland, Iceland, Mexico, Central America and Caribbean areas under the U.S. flag; Iceland summoned the U.S. ambassador"
  Source.publicAttribution

greenlandReuters2026 : Source.AttributedSource
greenlandReuters2026 = Source.mkNoDOISource
  "Reuters"
  "Trump, sharing leaked texts and AI mock-ups, vows 'no going back' on Greenland"
  "Reuters"
  "2026-01-20"
  "https://www.reuters.com/business/davos/us-treasury-secretary-bessent-brushes-off-hysteria-over-greenland-2026-01-20/"
  Source.newsSource
  "secondary report on Trump's Greenland territorial rhetoric and AI-generated symbolic imagery; does not convert imagery into enacted territorial law"
  Source.publicAttribution

data TerritorialSpeechAct : Set where
  mapPost : TerritorialSpeechAct
  annexationRhetoric : TerritorialSpeechAct
  acquisitionProposal : TerritorialSpeechAct
  enactedTreaty : TerritorialSpeechAct
  enactedStatute : TerritorialSpeechAct
  militaryOrder : TerritorialSpeechAct

record TerritorialSymbolicArtifact : Set where
  constructor territorial-symbolic-artifact
  field
    act : TerritorialSpeechAct
    carrier : String
    representedTerritory : String
    source : Source.AttributedSource
    officialLegalInstrument : Bool
    formalAnnexationPolicy : Bool
    evidencesTerritorialImaginary : Bool
    provesImplementationIntent : Bool

open TerritorialSymbolicArtifact public

septemberMap : TerritorialSymbolicArtifact
septemberMap = territorial-symbolic-artifact
  mapPost
  "Trump Truth Social post as reported by Reuters"
  "United States plus Canada, Greenland, Iceland, Mexico, Central America and Caribbean areas under U.S. flag"
  trumpMapReuters2026
  false false true false

data SymbolicMapMeansAnnexationPolicy : Set where
data TerritorialRhetoricMeansMilitaryOrder : Set where
data OnePostDefinesWholeUSForeignPolicy : Set where

symbolicMapDoesNotEqualAnnexationPolicy :
  SymbolicMapMeansAnnexationPolicy → ⊥
symbolicMapDoesNotEqualAnnexationPolicy ()

territorialRhetoricDoesNotEqualMilitaryOrder :
  TerritorialRhetoricMeansMilitaryOrder → ⊥
territorialRhetoricDoesNotEqualMilitaryOrder ()

onePostDoesNotDefineWholeUSForeignPolicy :
  OnePostDefinesWholeUSForeignPolicy → ⊥
onePostDoesNotDefineWholeUSForeignPolicy ()
