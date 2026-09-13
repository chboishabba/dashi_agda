module DASHI.Wikimedia.IbrahimSnowballGeologyStratigraphyDeepTimeCarbonConsumerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact as Carbon
import DASHI.Environment.LESDomainBasisBidiFrontierExact as LES

------------------------------------------------------------------------
-- IBRAHIM / GEOLOGY BREADTH CONCRETE CONSUMER
--
-- The concrete downstream consumer is the existing deep-time carbon ledger.
-- It already has sediment and fossil-carbon reservoirs, but a stock/flux ledger
-- cannot recover depositional system, source-to-sink history, stratigraphic
-- context, preservation pathway or tectonic setting.  This is the missing
-- geology/stratigraphy consumer demanded by the live Ibrahim roadmap.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim geology/stratigraphy/deep-time-carbon concrete consumer"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; identity does not create geological mechanism, stratigraphic correlation, depositional history, carbon provenance or causal authority")

geologyQid : Identity.ExternalIdentityDemand
geologyQid = mkQid "geology" "Q1069"

stratigraphyQid : Identity.ExternalIdentityDemand
stratigraphyQid = mkQid "stratigraphy" "Q134783"

sedimentologyQid : Identity.ExternalIdentityDemand
sedimentologyQid = mkQid "sedimentology" "Q205768"

geomorphologyQid : Identity.ExternalIdentityDemand
geomorphologyQid = mkQid "geomorphology" "Q52109"

tectonicsQid : Identity.ExternalIdentityDemand
tectonicsQid = mkQid "tectonics" "Q193343"

stratigraphicUnitQid : Identity.ExternalIdentityDemand
stratigraphicUnitQid = mkQid "stratigraphic unit" "Q3694119"

------------------------------------------------------------------------
-- Dewey navigation: geology has two already-inspected coordinates in the live
-- roadmap.  Subdiscipline DDCs stay unresolved until individually inspected.
------------------------------------------------------------------------

geologyDewey550 : Dewey.DeweyCoordinate
geologyDewey550 = Dewey.mkVerifiedDewey
  "geology"
  "550"
  "Wikidata Q1069 DDC statement retained from live Ibrahim roadmap"

geologyDewey551 : Dewey.DeweyCoordinate
geologyDewey551 = Dewey.mkVerifiedDewey
  "geology"
  "551"
  "Wikidata Q1069 DDC statement retained from live Ibrahim roadmap; multiple library views preserved"

stratigraphyDewey : Dewey.DeweyCoordinate
stratigraphyDewey = Dewey.mkUnresolvedDewey
  "stratigraphy"
  "no exact inspected DDC value promoted in this pass"

sedimentologyDewey : Dewey.DeweyCoordinate
sedimentologyDewey = Dewey.mkUnresolvedDewey
  "sedimentology"
  "no exact inspected DDC value promoted in this pass"

------------------------------------------------------------------------
-- DOI/source line paying the selected consumer.
------------------------------------------------------------------------

sourceToSinkCarbonSource : Attribution.AttributedSource
sourceToSinkCarbonSource = Attribution.mkDOISource
  "Elana L. Leithold; Neal E. Blair; Karl W. Wegmann"
  "Source-to-sink sedimentary systems and global carbon burial: A river runs through it"
  "Earth-Science Reviews 153, 30-42"
  "2016"
  "10.1016/j.earscirev.2015.10.011"
  "https://doi.org/10.1016/j.earscirev.2015.10.011"
  Attribution.academicArticleSource
  "review/source-to-sink synthesis showing that carbon burial reflects linked sedimentary-system source, transport, transformation and depositional setting; used here to motivate geology coordinates, not to import quantitative global values"
  Attribution.publicAttribution

deepTimeLandOceanSource : Attribution.AttributedSource
deepTimeLandOceanSource = Attribution.mkDOISource
  "Brian W. Romans; Stephan A. Graham"
  "A Deep-Time Perspective of Land-Ocean Linkages in the Sedimentary Record"
  "Annual Review of Marine Science 5, 69-94"
  "2013"
  "10.1146/annurev-marine-121211-172426"
  "https://doi.org/10.1146/annurev-marine-121211-172426"
  Attribution.academicArticleSource
  "review of source-to-sink sedimentary basins and stratigraphic archives for reconstructing deep-time environmental change; source role is geological context, not automatic reconstruction of a particular reservoir history"
  Attribution.publicAttribution

lacustrineCarbonBurialSource : Attribution.AttributedSource
lacustrineCarbonBurialSource = Attribution.mkDOISource
  "Chao Liang et al."
  "Lacustrine organic carbon burial in deep time: Perspectives from major geologic events and tectonic-climatic-ecological coupling"
  "Earth-Science Reviews 272, 105312"
  "2026"
  "10.1016/j.earscirev.2025.105312"
  "https://doi.org/10.1016/j.earscirev.2025.105312"
  Attribution.academicArticleSource
  "review identifying multiple interacting controls on lacustrine organic-carbon burial including tectonics, climate, lake scale, hydro-ecology and volcanic/hydrothermal activity; does not imply one universal burial mechanism"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Exact existing boundaries reused.
------------------------------------------------------------------------

carbonLedgerBoundary : Carbon.DeepTimeCarbonReservoirFluxBoundary
carbonLedgerBoundary = Carbon.canonicalDeepTimeCarbonReservoirFluxBoundary

lesDomainBoundary : LES.LESDomainBasisBoundary
lesDomainBoundary = LES.canonicalLESDomainBasisBoundary

------------------------------------------------------------------------
-- Regression 1: same sediment/fossil carbon stock cannot recover depositional
-- and stratigraphic history.
------------------------------------------------------------------------

data CarbonGeologyCase : Set where
  sameStockRapidBurial sameStockProtractedReworking : CarbonGeologyCase

data CarbonStockSurface : Set where sameSedimentCarbonInventory : CarbonStockSurface
data DepositionalHistory : Set where rapidPreservationalBurial protractedTransportReworking : DepositionalHistory

carbonStockSurface : CarbonGeologyCase → CarbonStockSurface
carbonStockSurface _ = sameSedimentCarbonInventory

depositionalHistory : CarbonGeologyCase → DepositionalHistory
depositionalHistory sameStockRapidBurial = rapidPreservationalBurial
depositionalHistory sameStockProtractedReworking = protractedTransportReworking

stockHistoryDefect : INF.NonFactorabilityWitness carbonStockSurface depositionalHistory
stockHistoryDefect = INF.nonFactorabilityWitness
  sameStockRapidBurial sameStockProtractedReworking refl (λ ())

carbonInventoryCannotFactorDepositionalHistory :
  INF.FactorsThrough carbonStockSurface depositionalHistory → ⊥
carbonInventoryCannotFactorDepositionalHistory =
  INF.witnessRulesOutEveryFlatFactorisation stockHistoryDefect

------------------------------------------------------------------------
-- Regression 2: sediment-transport classification cannot recover geological
-- mechanism/context.  This instantiates the LES frontier's existing warning.
------------------------------------------------------------------------

data SedimentCase : Set where
  sameSedimentTransportFluvialDeltaic sameSedimentTransportSubmarineFan : SedimentCase

data TransportSurface : Set where sameSedimentTransportLabel : TransportSurface
data GeologicalSetting : Set where fluvialDeltaicSetting submarineFanSetting : GeologicalSetting

transportSurface : SedimentCase → TransportSurface
transportSurface _ = sameSedimentTransportLabel

geologicalSetting : SedimentCase → GeologicalSetting
geologicalSetting sameSedimentTransportFluvialDeltaic = fluvialDeltaicSetting
geologicalSetting sameSedimentTransportSubmarineFan = submarineFanSetting

transportSettingDefect : INF.NonFactorabilityWitness transportSurface geologicalSetting
transportSettingDefect = INF.nonFactorabilityWitness
  sameSedimentTransportFluvialDeltaic sameSedimentTransportSubmarineFan refl (λ ())

sedimentTransportCannotFactorGeologicalSetting :
  INF.FactorsThrough transportSurface geologicalSetting → ⊥
sedimentTransportCannotFactorGeologicalSetting =
  INF.witnessRulesOutEveryFlatFactorisation transportSettingDefect

------------------------------------------------------------------------
-- Regression 3: same present stratigraphic unit label cannot recover unique
-- paleoenvironmental interpretation without facies/provenance/context receipts.
------------------------------------------------------------------------

data StrataCase : Set where
  sameUnitInterpretationA sameUnitInterpretationB : StrataCase

data UnitSurface : Set where sameStratigraphicUnit : UnitSurface
data PaleoenvironmentReading : Set where paleoenvironmentA paleoenvironmentB : PaleoenvironmentReading

unitSurface : StrataCase → UnitSurface
unitSurface _ = sameStratigraphicUnit

paleoenvironmentReading : StrataCase → PaleoenvironmentReading
paleoenvironmentReading sameUnitInterpretationA = paleoenvironmentA
paleoenvironmentReading sameUnitInterpretationB = paleoenvironmentB

strataReadingDefect : INF.NonFactorabilityWitness unitSurface paleoenvironmentReading
strataReadingDefect = INF.nonFactorabilityWitness
  sameUnitInterpretationA sameUnitInterpretationB refl (λ ())

stratigraphicUnitCannotFactorUniquePaleoenvironment :
  INF.FactorsThrough unitSurface paleoenvironmentReading → ⊥
stratigraphicUnitCannotFactorUniquePaleoenvironment =
  INF.witnessRulesOutEveryFlatFactorisation strataReadingDefect

------------------------------------------------------------------------
-- Reverse BIDI constraints.
------------------------------------------------------------------------

record GeologyReverseConstraint : Set where
  constructor geology-reverse-constraint
  field
    parentNode : String
    distinctionForcedUpward : String
    parentMayEraseDistinction : Bool
open GeologyReverseConstraint public

carbonConstraint : GeologyReverseConstraint
carbonConstraint = geology-reverse-constraint
  "Deep-time carbon / carbon cycle"
  "present reservoir stock, source provenance, transport path, depositional setting, preservation, burial efficiency and stratigraphic age/context remain distinct"
  false

geologyConstraint : GeologyReverseConstraint
geologyConstraint = geology-reverse-constraint
  "Geology / stratigraphy / sedimentology"
  "rock/sediment identity, stratigraphic relation, depositional process, tectonic setting, geomorphic transport and paleoenvironmental interpretation remain distinct"
  false

lesConstraint : GeologyReverseConstraint
lesConstraint = geology-reverse-constraint
  "LES / environment"
  "sediment balance/transport vocabulary cannot substitute for geological evolution, weathering, basin history or stratigraphic context"
  false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CarbonStockCreatesDepositionalHistory : Set where
data SedimentTransportCreatesGeomorphology : Set where
data StratigraphicUnitCreatesPaleoenvironment : Set where
data GeologyQidCreatesMechanism : Set where
data DeweyCreatesGeologicalDependency : Set where

carbonStockDoesNotCreateDepositionalHistory : CarbonStockCreatesDepositionalHistory → ⊥
carbonStockDoesNotCreateDepositionalHistory ()

sedimentTransportDoesNotCreateGeomorphology : SedimentTransportCreatesGeomorphology → ⊥
sedimentTransportDoesNotCreateGeomorphology ()

stratigraphicUnitDoesNotCreatePaleoenvironment : StratigraphicUnitCreatesPaleoenvironment → ⊥
stratigraphicUnitDoesNotCreatePaleoenvironment ()

geologyQidDoesNotCreateMechanism : GeologyQidCreatesMechanism → ⊥
geologyQidDoesNotCreateMechanism ()

deweyDoesNotCreateGeologicalDependency : DeweyCreatesGeologicalDependency → ⊥
deweyDoesNotCreateGeologicalDependency ()

record GeologyStratigraphyDeepTimeCarbonBoundary : Set where
  constructor geology-stratigraphy-deep-time-carbon-boundary
  field
    concreteDeepTimeCarbonConsumerSelected : Bool
    qidsAttachedWhenSafelyResolved : Bool
    geologyMultipleDeweyCoordinatesRetained : Bool
    subdisciplineDeweyUnresolvedStatesRetained : Bool
    doiSourceRolesRetained : Bool
    existingCarbonLedgerReused : Bool
    existingLESFrontierReused : Bool
    carbonStockSeparatedFromDepositionalHistory : Bool
    sedimentTransportSeparatedFromGeologicalSetting : Bool
    stratigraphicUnitSeparatedFromPaleoenvironment : Bool
    reverseBidiConstraintsPropagateUpward : Bool
    presentAxisVocabularyClaimedComplete : Bool
open GeologyStratigraphyDeepTimeCarbonBoundary public

canonicalGeologyStratigraphyDeepTimeCarbonBoundary :
  GeologyStratigraphyDeepTimeCarbonBoundary
canonicalGeologyStratigraphyDeepTimeCarbonBoundary =
  geology-stratigraphy-deep-time-carbon-boundary
    true true true true true true true true true true true false
