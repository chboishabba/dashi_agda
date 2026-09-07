module DASHI.Physics.GR.GravitationalObservationSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-SHAPED GRAVITATIONAL OBSERVATION ATLAS
--
-- This branch does not depend on the newer generic AttributedSource API, so the
-- atlas carries the minimum explicit source shape locally.  It is an attribution
-- carrier, not a theorem that every claim in the cited source is true.
------------------------------------------------------------------------

data ObservationSourceKind : Set where
  collaborationCatalog : ObservationSourceKind
  collaborationGRTest : ObservationSourceKind
  pulsarTimingCollaborationResult : ObservationSourceKind
  futureMissionAuthority : ObservationSourceKind

record ObservationAttributedSource : Set where
  constructor observation-attributed-source
  field
    sourceKind : ObservationSourceKind
    responsibleBody : String
    title : String
    publicationOrReleaseDate : String
    carrierURL : String
    exactUse : String
    inspectedForExactUse : Bool
    empiricalResultCarrier : Bool

open ObservationAttributedSource public

lvkGWTC5 : ObservationAttributedSource
lvkGWTC5 = observation-attributed-source
  collaborationCatalog
  "LIGO-Virgo-KAGRA Collaboration / LIGO Scientific Collaboration"
  "GWTC-5.0 / O4b Catalog"
  "2026-05-26"
  "https://ligo.org/detections/o4b-catalog/"
  "catalog authority for significant compact-binary gravitational-wave observations through O4b; page reports 161 new significant signals and 390 cumulative detections"
  true true

lvkGRTests2026 : ObservationAttributedSource
lvkGRTests2026 = observation-attributed-source
  collaborationGRTest
  "LIGO-Virgo-KAGRA Collaboration / LIGO Scientific Collaboration"
  "Testing general relativity with the latest and loudest compact binary merger observations"
  "2026-07"
  "https://ligo.org/science-summaries/o4b_tgr/"
  "authority for current compact-binary gravitational-wave tests of GR; summary reports no detected deviation across the tested suite and tighter bounds"
  true true

nanoGrav15Year : ObservationAttributedSource
nanoGrav15Year = observation-attributed-source
  pulsarTimingCollaborationResult
  "NANOGrav Collaboration"
  "Evidence for a Gravitational-Wave Background / 15-Year Data Set"
  "2023"
  "https://nanograv.org/15yr/Summary/Background"
  "source for evidence of Hellings-Down-like correlated pulsar timing residuals consistent with a nanohertz gravitational-wave background"
  true true

lisaMissionAuthority : ObservationAttributedSource
lisaMissionAuthority = observation-attributed-source
  futureMissionAuthority
  "European Space Agency"
  "LISA"
  "current mission page inspected 2026"
  "https://www.esa.int/Science_Exploration/Space_Science/LISA"
  "future-detector authority only; planned space-based gravitational-wave observatory with launch currently planned for 2035"
  true false

record GravitationalObservationSourceBoundary : Set where
  constructor gravitational-observation-source-boundary
  field
    catalogSourceProvesEveryEventModel : Bool
    collaborationGRTestProvesGRIsUniquePossibleTheory : Bool
    pulsarTimingEvidenceIdentifiesUniqueBackgroundPopulation : Bool
    futureLISAMissionCountsAsPresentObservation : Bool
    currentObservationClaimsRequireAttributedCarrier : Bool

canonicalGravitationalObservationSourceBoundary : GravitationalObservationSourceBoundary
canonicalGravitationalObservationSourceBoundary =
  gravitational-observation-source-boundary false false false false true
