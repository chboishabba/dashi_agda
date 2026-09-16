module DASHI.Law.SensibLawWoogarooIbrahimRicNattrassLocalActivityExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Ibrahim
import DASHI.Law.SensibLawWoogarooIbrahimDeweyQidLegalAtomExact as Canonical
import DASHI.Law.SensibLawWoogarooExistingLocalKoalaMonitoringSnowballExact as Monitoring
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- THIN LOCAL-ACTIVITY EXTENSION
--
-- Adds a currently public, local-government monitoring result that is closer
-- to the Woogaroo corridor than the general/regional literature.  It extends
-- the existing monitoring Snowball; it does not create a second monitoring,
-- traversal or legal-atom architecture.
------------------------------------------------------------------------

koalaQid : Id.ItemId
koalaQid = Id.itemId "Q36101"

ecologicalConnectivityQid : Id.ItemId
ecologicalConnectivityQid = Id.itemId "Q2993449"

cityOfIpswichQid : Id.ItemId
cityOfIpswichQid = Id.itemId "Q1631867"

koalaDewey : String
koalaDewey = "599.25"

ecologyDewey : String
ecologyDewey = "577"

conservationDewey : String
conservationDewey = "333.95"

------------------------------------------------------------------------
-- Attribution.
------------------------------------------------------------------------

ipswichKoalaPlanActivitySource : Source.AttributedSource
ipswichKoalaPlanActivitySource = Source.mkNoDOISource
  "Ipswich City Council"
  "Koala Conservation and Habitat Management Plan — Appendix B OWAD Koala Activity Survey Results"
  "Ipswich City Council"
  "2018"
  "https://www.ipswich.qld.gov.au/files/assets/public/v/1/about-council/initiatives/environment/wildlife/koala-conservation/documents/koala-conservation-plan.pdf"
  Source.governmentSource
  "Primary local-government carrier for the Appendix B OWAD activity results. It records Ric Nattrass Environmental Park with Final Score 8 and Koala Activity Level 3 under the plan's own activity scoring scheme. Used as a historical local activity observation, not as a current population estimate or Springview occurrence."
  Source.publicAttribution

ricNattrassParkSource : Source.AttributedSource
ricNattrassParkSource = Source.mkNoDOISource
  "Ipswich City Council"
  "Ric Nattrass Environmental Park"
  "Ipswich City Council parks/reserves register"
  "2026"
  "https://www.ipswich.qld.gov.au/Explore/Parks-and-Reserves/Parks-Search/Ric-Nattrass-Environmental-Park"
  Source.governmentSource
  "Primary local-government place/function source. Council states the 13.7 ha park adjoins Woogaroo Creek and provides connectivity for species from White Rock-Spring Mountain Conservation Estate to the Brisbane River corridor. Used to bind the historical activity record to a Council-described corridor function, not to prove realised koala movement through Springview."
  Source.publicAttribution

localActivityAtlas : Source.AttributedSourceAtlas
localActivityAtlas = Source.mkSourceAtlas
  "Woogaroo Ric Nattrass local Koala activity extension"
  "DASHI.Law.SensibLawWoogarooIbrahimRicNattrassLocalActivityExtensionExact"
  (ipswichKoalaPlanActivitySource ∷ ricNattrassParkSource ∷ [])
  "Two Ipswich City Council carriers: one historical Koala-activity result and one current place/connectivity description. They are institutionally related and are not counted as independent biological replications. Neither establishes Springview occupancy, realised movement, viable-population identity or a legal conclusion."

------------------------------------------------------------------------
-- Ibrahim/Dewey/QID coordinates.
------------------------------------------------------------------------

ricNattrassActivityCoordinate : Ibrahim.DashiKnowledgeCoordinate
ricNattrassActivityCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimRicNattrassLocalActivityExtensionExact.agda"
  "Ric Nattrass Environmental Park historical Koala activity"
  koalaDewey
  (Id.rawItemId koalaQid)
  "primary: Ipswich City Council Koala Conservation and Habitat Management Plan Appendix B"

ricNattrassConnectivityCoordinate : Ibrahim.DashiKnowledgeCoordinate
ricNattrassConnectivityCoordinate = Ibrahim.dashi-knowledge-coordinate
  "DASHI/Law/SensibLawWoogarooIbrahimRicNattrassLocalActivityExtensionExact.agda"
  "Ric Nattrass / Woogaroo Creek connection from White Rock-Spring Mountain to Brisbane River corridor"
  ecologyDewey
  (Id.rawItemId ecologicalConnectivityQid)
  "primary: Ipswich City Council Ric Nattrass Environmental Park register"

activityToS13 : Ibrahim.DashiFirstLinkEdge
activityToS13 = Ibrahim.dashi-first-link-edge
  ricNattrassActivityCoordinate Canonical.s13EssentialityCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Independent local-government monitoring records high historical Koala activity at a Woogaroo Creek park in the broader corridor. It strengthens the case for acquiring the underlying local population/movement series but does not identify Springview's viable population or establish essentiality."
  true

connectivityToS13 : Ibrahim.DashiFirstLinkEdge
connectivityToS13 = Ibrahim.dashi-first-link-edge
  ricNattrassConnectivityCoordinate Canonical.s13EssentialityCoordinate Ibrahim.supportedBy
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Council itself describes the park as a species-connectivity link between White Rock-Spring Mountain and the Brisbane River corridor. This is stronger local institutional corridor evidence than a generic map, but realised koala movement through Springview/Opossum-Woogaroo remains a separate fact."
  true

activityToS102 : Ibrahim.DashiFirstLinkEdge
activityToS102 = Ibrahim.dashi-first-link-edge
  ricNattrassActivityCoordinate Canonical.s102StatutoryCoordinate Ibrahim.crossPollinatesWith
  Ibrahim.canonicalDashiFirstLinkPolicy
  "Historical local activity is independently relevant to the biological plausibility of a functioning local koala landscape, while current likely significant detrimental effect still needs a present same-object expert assessment."
  true

------------------------------------------------------------------------
-- Legal-atom bindings.
------------------------------------------------------------------------

record LocalActivityAtomBinding : Set where
  constructor local-activity-atom-binding
  field
    atom : Atom.LegalExecutionAtom
    consumer : Atom.LegalExecutionConsumer
    sourcePaid : Bool
    sameObjectSpringviewPaid : Bool
    contribution : String
    residual : String

open LocalActivityAtomBinding public

s13LocalActivityBinding : LocalActivityAtomBinding
s13LocalActivityBinding = local-activity-atom-binding
  Atom.habitatPopulationEssentialityAtom
  Atom.nca13EssentialityConsumer
  true false
  "Pays a historical local Koala-activity observation on Woogaroo Creek plus Council-described corridor function to White Rock-Spring Mountain."
  "Identify whether Springview/Opossum-Woogaroo habitat forms a realised movement/population connection to this local activity/corridor system and to which viable population it belongs."

s102LocalActivityBinding : LocalActivityAtomBinding
s102LocalActivityBinding = local-activity-atom-binding
  Atom.affectedWildlifeHabitatAtom
  Atom.nca102InterimOrderConsumer
  true false
  "Adds independent local-government evidence that Koala activity has been recorded within the broader Woogaroo Creek corridor system."
  "A current expert must still join the approved 9281 process, present habitat/population state and likely magnitude/duration/reversibility of detrimental effect."

------------------------------------------------------------------------
-- Highest-alpha consequence.
------------------------------------------------------------------------

record LocalActivityFrontier : Set where
  constructor local-activity-frontier
  field
    localActivityResultPaid : Bool
    councilCorridorFunctionPaid : Bool
    springviewSameObjectJoinPaid : Bool
    currentPopulationTrendPaid : Bool
    realisedConnectivityPaid : Bool
    nextCut : String

currentLocalActivityFrontier : LocalActivityFrontier
currentLocalActivityFrontier = local-activity-frontier
  true true false false false
  "This discovery increases, rather than reduces, the value of acquiring the 2020/2023/2025 Ipswich monitoring outputs. First ask whether those repeated sites/results include White Rock-Spring Mountain, Ric Nattrass/Woogaroo Creek or another spatially joinable part of the corridor; then join the time series to Springview/Opossum-Woogaroo. Do not commission a new static corridor model before exhausting those local longitudinal records."

monitoringFrontier : Monitoring.ExistingMonitoringFrontier
monitoringFrontier = Monitoring.currentExistingMonitoringFrontier

------------------------------------------------------------------------
-- WrongType / attribution boundaries.
------------------------------------------------------------------------

data HistoricalActivityEqualsCurrentPopulation : Set where
data RicNattrassEqualsSpringview : Set where
data CouncilConnectivityDescriptionEqualsRealisedKoalaMovement : Set where
data SameCouncilMeansIndependentBiologicalReplication : Set where
data ActivityScoreEqualsS13Essentiality : Set where
data ActivityScoreEqualsS102DetrimentalEffect : Set where

historicalActivityDoesNotBecomeCurrentPopulation : HistoricalActivityEqualsCurrentPopulation → ⊥
historicalActivityDoesNotBecomeCurrentPopulation ()

ricNattrassDoesNotBecomeSpringview : RicNattrassEqualsSpringview → ⊥
ricNattrassDoesNotBecomeSpringview ()

councilDescriptionDoesNotCreateRealisedMovement : CouncilConnectivityDescriptionEqualsRealisedKoalaMovement → ⊥
councilDescriptionDoesNotCreateRealisedKoalaMovement ()

sameInstitutionDoesNotCreateIndependentReplication : SameCouncilMeansIndependentBiologicalReplication → ⊥
sameInstitutionDoesNotCreateIndependentBiologicalReplication ()

activityScoreDoesNotCreateEssentiality : ActivityScoreEqualsS13Essentiality → ⊥
activityScoreDoesNotCreateEssentiality ()

activityScoreDoesNotCreateDetrimentalEffect : ActivityScoreEqualsS102DetrimentalEffect → ⊥
activityScoreDoesNotCreateDetrimentalEffect ()
