module DASHI.Physics.CondensedMatter.GaoFe5GeTe2FlatBandChargeOrderSourceReplayExact where

------------------------------------------------------------------------
-- Fe5GeTe2 INTERACTION-DRIVEN FLAT BAND / CHARGE ORDER
--
-- PRIMARY SOURCE
-- Qiang Gao et al.,
-- "Interaction-driven flat band and charge order in Fe5GeTe2"
-- Science Advances 12(32), eaeg5930 (2026)
-- DOI 10.1126/sciadv.aeg5930
--
-- SECONDARY PUBLIC SUMMARY
-- University of Chicago / ScienceDaily, 1 October 2026.
--
-- This file records source-paid statements and explicit unpaid boundaries.
-- It does not turn the authors' phenomenological interpretation into a
-- repository-derived microscopic Hamiltonian.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

gaoEtAl2026 : Attribution.AttributedSource
gaoEtAl2026 =
  Attribution.mkDOISource
    "Qiang Gao, Gabriele Berruto, Khanh Duy Nguyen, Chaowei Hu, Paul Malinowski, Haoran Lin, Beomjoon Goh, Bo Gyu Jang, Xiaodong Xu, Peter Littlewood, Jiun-Haw Chu, Shuolong Yang"
    "Interaction-driven flat band and charge order in Fe5GeTe2"
    "Science Advances 12(32), eaeg5930"
    "2026"
    "10.1126/sciadv.aeg5930"
    "https://doi.org/10.1126/sciadv.aeg5930"
    Attribution.academicArticleSource
    "primary source for high-resolution ARPES evidence of an interaction-driven flat band at the Fermi level, sqrt(3) x sqrt(3) R30-degree charge order, band folding within 30 meV below EF, Brillouin-zone-wide flat-band presence, and logarithmic temperature dependence of spectral weight; the source suggests a phenomenological Kondo-like coherent Fermi liquid and does not provide a DASHI-derived microscopic Hamiltonian"
    Attribution.publicAttribution

scienceDaily20261001 : Attribution.AttributedSource
scienceDaily20261001 =
  Attribution.mkNoDOISource
    "University of Chicago"
    "Electrons slow to a crawl in a strange new quantum state"
    "ScienceDaily"
    "2026"
    "https://www.sciencedaily.com/releases/2026/09/260929053548.htm"
    Attribution.newsSource
    "secondary public summary for the Fe5GeTe2 result, including the report that coherent behaviour persists to about 100 K and prospective memory-device discussion; not a primary source for the microscopic interpretation"
    Attribution.publicAttribution

fe5gete2SourceAtlas : Attribution.AttributedSourceAtlas
fe5gete2SourceAtlas =
  Attribution.mkSourceAtlas
    "Fe5GeTe2 interaction-driven flat-band and charge-order source atlas"
    "DASHI.Physics.CondensedMatter.GaoFe5GeTe2FlatBandChargeOrderSourceReplayExact"
    (gaoEtAl2026 ∷ scienceDaily20261001 ∷ [])
    "primary-paper observations and attributed interpretation are separated from secondary technology-temperature commentary and from repository-owned formal abstractions"

record Fe5GeTe2SourceReplay : Set where
  constructor fe5gete2-source-replay
  field
    source : Attribution.AttributedSourceAtlas
    material : String
    measurementMethod : String
    flatBandAtFermiLevelReported : Bool
    flatBandThroughoutBrillouinZoneReported : Bool
    chargeOrderSymmetry : String
    chargeOrderReported : Bool
    bandFoldingWindowBelowFermiMeV : Nat
    logarithmicTemperatureDependenceOfSpectralWeightReported : Bool
    phenomenologicalKondoLikeCoherentFermiLiquidSuggested : Bool
    interactionDrivenFlatBandInterpretationAttributed : Bool
    secondarySummaryReportsCoherenceToApproxKelvin : Nat
    rawARPESArrayPaidByAtlas : Bool
    exactMicroscopicHamiltonianPaidByAtlas : Bool
    uniqueKondoHamiltonianDerivedByRepository : Bool
    roomTemperatureOperationDemonstrated : Bool
    memoryDeviceDemonstrated : Bool

open Fe5GeTe2SourceReplay public

canonicalFe5GeTe2SourceReplay : Fe5GeTe2SourceReplay
canonicalFe5GeTe2SourceReplay =
  fe5gete2-source-replay
    fe5gete2SourceAtlas
    "Fe5GeTe2"
    "high-resolution angle-resolved photoemission spectroscopy (ARPES)"
    true
    true
    "sqrt(3) x sqrt(3) R30-degree charge order"
    true
    30
    true
    true
    true
    100
    false
    false
    false
    false
    false

record Fe5GeTe2AttributionBoundary : Set where
  constructor fe5gete2-attribution-boundary
  field
    primaryARPESObservationAttributed : Bool
    chargeOrderAndBandFoldingAttributed : Bool
    kondoLikeLanguageKeptPhenomenological : Bool
    hundredKelvinStatementKeptSecondary : Bool
    rawSpectrumInvented : Bool
    exactHamiltonianInvented : Bool
    memoryApplicationPromotedToDemonstratedDevice : Bool

canonicalFe5GeTe2AttributionBoundary : Fe5GeTe2AttributionBoundary
canonicalFe5GeTe2AttributionBoundary =
  fe5gete2-attribution-boundary
    true true true true
    false false false
