module DASHI.Physics.GR.GravitationalObservationSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-SHAPED GRAVITATIONAL OBSERVATION ATLAS
--
-- Attribution policy on this branch:
--
--   author/responsible body + title + DOI/arXiv/official stable identifier
--   + exact carrier + actual inspection date + exact source-entitled use.
--
-- Missing metadata remains a residual; it is never guessed.  A source carrier
-- attributes only the bounded claim recorded in exactUse.  DASHI reconstruction,
-- cross-source inference, theory comparison, and theorem promotion are separate.
------------------------------------------------------------------------

data ObservationSourceKind : Set where
  collaborationCatalog : ObservationSourceKind
  collaborationGRTest : ObservationSourceKind
  pulsarTimingCollaborationResult : ObservationSourceKind
  futureMissionAuthority : ObservationSourceKind

data StableIdentifierKind : Set where
  doiIdentifier : StableIdentifierKind
  arxivIdentifier : StableIdentifierKind
  officialCanonicalURLIdentifier : StableIdentifierKind

record ObservationAttributedSource : Set where
  constructor observation-attributed-source
  field
    sourceKind : ObservationSourceKind
    authorOrResponsibleBody : String
    title : String
    stableIdentifierKind : StableIdentifierKind
    stableIdentifier : String
    publicationOrReleaseDate : String
    carrierURL : String
    inspectedOn : String
    exactUse : String
    inspectedForExactUse : Bool
    empiricalResultCarrier : Bool

open ObservationAttributedSource public

lvkGWTC5 : ObservationAttributedSource
lvkGWTC5 = observation-attributed-source
  collaborationCatalog
  "LIGO Scientific Collaboration, Virgo Collaboration, KAGRA Collaboration"
  "GWTC-5.0: Observations from the Second Part of the Fourth LIGO-Virgo-KAGRA Observing Run and Updates to the Gravitational-Wave Transient Catalog"
  arxivIdentifier
  "arXiv:2605.27225"
  "2026-05-26"
  "https://ligo.org/detections/o4b-catalog/"
  "2026-09-08"
  "catalog/result authority for compact-binary gravitational-wave observations through O4b; the inspected collaboration catalog page reports 161 new significant signals and 390 cumulative detections"
  true true

lvkGRTests2026 : ObservationAttributedSource
lvkGRTests2026 = observation-attributed-source
  collaborationGRTest
  "LIGO Scientific Collaboration, Virgo Collaboration, KAGRA Collaboration"
  "GWTC-5.0: Tests of General Relativity"
  arxivIdentifier
  "arXiv:2607.19293"
  "2026-07-21"
  "https://ligo.org/science-summaries/o4b_tgr/"
  "2026-09-08"
  "authority for current compact-binary gravitational-wave tests of GR; the inspected collaboration summary and linked paper report no evidence for physics beyond GR across the tested suite while tightening deviation constraints"
  true true

nanoGrav15Year : ObservationAttributedSource
nanoGrav15Year = observation-attributed-source
  pulsarTimingCollaborationResult
  "Gabriella Agazie et al. / NANOGrav Collaboration"
  "The NANOGrav 15-year Data Set: Evidence for a Gravitational-Wave Background"
  doiIdentifier
  "10.3847/2041-8213/acdac6"
  "2023-06-28"
  "https://nanograv.org/15yr/Summary/Background"
  "2026-09-08"
  "source for evidence of Hellings-Downs-pattern correlated pulsar timing residuals consistent with a nanohertz gravitational-wave background; it does not uniquely identify the source population"
  true true

lisaMissionAuthority : ObservationAttributedSource
lisaMissionAuthority = observation-attributed-source
  futureMissionAuthority
  "European Space Agency"
  "LISA"
  officialCanonicalURLIdentifier
  "https://www.esa.int/Science_Exploration/Space_Science/LISA"
  "current mission authority"
  "https://www.esa.int/Science_Exploration/Space_Science/LISA"
  "2026-09-08"
  "future-detector authority only; planned space-based gravitational-wave observatory, not a present observation carrier"
  true false

record GravitationalObservationSourceBoundary : Set where
  constructor gravitational-observation-source-boundary
  field
    authorTitleAndStableIdentifierRequired : Bool
    missingMetadataMayBeGuessed : Bool
    sourceExactUseEqualsAllClaimsInCarrier : Bool
    catalogSourceProvesEveryEventModel : Bool
    collaborationGRTestProvesGRIsUniquePossibleTheory : Bool
    pulsarTimingEvidenceIdentifiesUniqueBackgroundPopulation : Bool
    futureLISAMissionCountsAsPresentObservation : Bool
    currentObservationClaimsRequireAttributedCarrier : Bool
    dashiReconstructionIsExternalSourceClaim : Bool

canonicalGravitationalObservationSourceBoundary : GravitationalObservationSourceBoundary
canonicalGravitationalObservationSourceBoundary =
  gravitational-observation-source-boundary
    true false false false false false false true false
