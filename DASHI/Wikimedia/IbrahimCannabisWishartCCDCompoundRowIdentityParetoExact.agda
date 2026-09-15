module DASHI.Wikimedia.IbrahimCannabisWishartCCDCompoundRowIdentityParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisWishartArticleCCDDiscrepancyParetoExact as Discrepancy
import DASHI.Wikimedia.IbrahimCannabisWishartPublicReviewContextParetoExact as Review
import DASHI.Wikimedia.IbrahimCannabisTerpenePubChemCIDAuthorityExact as Registry
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- WISHART ARTICLE <-> CCD COMPOUND-ROW IDENTITY DISCRIMINATOR
--
-- The article reports THCA as the most abundant cannabinoid in all six
-- cultivars, gives an across-cultivar mean 148.833 +/- 19.364 mg/g, and states
-- a range of 133--162 mg/g for the extrema named in prose.  The current CCD
-- exposes distinct rows for delta-9-THCA-A and delta-8-THCA with large values.
-- This owner treats compound-row identity/mapping as a live lineage
-- hypothesis.  It does not diagnose a database bug without the exact Table S5
-- and ingestion mapping.
------------------------------------------------------------------------

record PublishedTHCASurface : Set where
  constructor published-thca-surface
  field
    sourceDOI : String
    assayReference : String
    tableReference : String
    articleMeanReference : String
    articleRangeReference : String
    abundanceClaimReference : String
    exactPerCultivarTableS5Paid : Bool
open PublishedTHCASurface public

wishartPublishedTHCASurface : PublishedTHCASurface
wishartPublishedTHCASurface = published-thca-surface
  "10.1021/acs.jafc.3c06616"
  "targeted LC-MS/MS cannabinoid assay; article says 16 cannabinoids quantified"
  "Table 3 reports THCA average 148.833 +/- 19.364 mg/g; exact Table S5 per-cultivar rows remain to be inspected directly"
  "THCA average concentration across six cultivars = 148.833 +/- 19.364 mg/g"
  "article prose: 133 mg/g in Tangerine Dream and Gabriola; 162 mg/g in Sensi Star and Alien Dawg"
  "article prose: THCA was the most abundant cannabinoid found in all cultivars"
  false

record CCDCompoundRow : Set where
  constructor ccd-compound-row
  field
    cdbID : String
    compoundLabel : String
    pubChemCID : String
    cultivar : String
    concentration : String
    unitReference : String
    dataSource : String
    sourceCitationState : String
    currentCCDRowPaid : Bool
    sameAsPublishedTableS5RowPaid : Bool
open CCDCompoundRow public

alienDawgTHCAA : CCDCompoundRow
alienDawgTHCAA = ccd-compound-row
  "CDB000016"
  "Delta-9-tetrahydrocannabinolic acid A"
  "98523"
  "Alien Dawg"
  "206.0"
  "mg/g dry wt"
  "HMP"
  "CCD row attributes value to Wishart et al., shown as 2023 manuscript submitted"
  true false

sensiStarTHCAA : CCDCompoundRow
sensiStarTHCAA = ccd-compound-row
  "CDB000016"
  "Delta-9-tetrahydrocannabinolic acid A"
  "98523"
  "Sensi Star"
  "218.0"
  "mg/g dry wt"
  "HMP"
  "CCD row attributes value to Wishart et al., shown as 2023 manuscript submitted"
  true false

alienDawgDelta8THCA : CCDCompoundRow
alienDawgDelta8THCA = ccd-compound-row
  "CDB000023"
  "Delta-8-tetrahydrocannabinolic acid"
  "59444391"
  "Alien Dawg"
  "209"
  "mg/g dry wt"
  "HMP"
  "CCD concentration detail attributes value to Wishart et al., shown as 2023 manuscript submitted"
  true false

sensiStarDelta8THCA : CCDCompoundRow
sensiStarDelta8THCA = ccd-compound-row
  "CDB000023"
  "Delta-8-tetrahydrocannabinolic acid"
  "59444391"
  "Sensi Star"
  "205"
  "mg/g dry wt"
  "HMP"
  "CCD concentration detail attributes value to Wishart et al., shown as 2023 manuscript submitted"
  true false

tangerineDreamDelta8THCA : CCDCompoundRow
tangerineDreamDelta8THCA = ccd-compound-row
  "CDB000023"
  "Delta-8-tetrahydrocannabinolic acid"
  "59444391"
  "Tangerine Dream"
  "121"
  "mg/g dry wt"
  "HMP"
  "CCD concentration detail attributes value to Wishart et al., shown as 2023 manuscript submitted"
  true false

------------------------------------------------------------------------
-- Live hypotheses.  None is promoted without Table S5 + ingestion lineage.
------------------------------------------------------------------------

data CompoundRowHypothesis : Set where
  articleProseOrAggregateError
  ccdCompoundMappingError
  ccdColumnOrRowShift
  sourceVersionDifference
  assaySemanticDifference
  intendedDistinctAnalytes
  unresolvedCompoundRowLineage : CompoundRowHypothesis

record CompoundRowHypothesisReceipt : Set where
  constructor compound-row-hypothesis-receipt
  field
    hypothesis : CompoundRowHypothesis
    discriminator : String
    exactTableS5Required : Bool
    exactCCDIngestionRequired : Bool
    hypothesisPaid : Bool
open CompoundRowHypothesisReceipt public

mappingHypothesis : CompoundRowHypothesisReceipt
mappingHypothesis = compound-row-hypothesis-receipt
  ccdCompoundMappingError
  "compare each Table S5 analyte label/CDB identifier/value column against current CCD CDB000016 and CDB000023 concentration rows"
  true true false

shiftHypothesis : CompoundRowHypothesisReceipt
shiftHypothesis = compound-row-hypothesis-receipt
  ccdColumnOrRowShift
  "test whether high values assigned to delta-8-THCA or delta-9-THCA-A reproduce another Table S5 row under a deterministic row/column offset"
  true true false

versionHypothesis : CompoundRowHypothesisReceipt
versionHypothesis = compound-row-hypothesis-receipt
  sourceVersionDifference
  "CCD cites a 2023 manuscript-submitted state while the published article is 2024; compare prepublication and final supporting data if obtainable"
  true true false

------------------------------------------------------------------------
-- Strong internal discriminator, kept bounded.
------------------------------------------------------------------------

record AbundanceConsistencyCheck : Set where
  constructor abundance-consistency-check
  field
    articleClaim : String
    ccdObservation : String
    sameCompoundSemanticsPaid : Bool
    sameSamplePaid : Bool
    contradictionPaid : Bool
open AbundanceConsistencyCheck public

alienDawgAbundanceCheck : AbundanceConsistencyCheck
alienDawgAbundanceCheck = abundance-consistency-check
  "published article: THCA was the most abundant cannabinoid in every cultivar"
  "current CCD: Alien Dawg delta-8-THCA = 209 mg/g and delta-9-THCA-A = 206 mg/g"
  false true false

-- Because 'THCA' in the article must first be matched to exact Table S5 analyte
-- semantics, 209 > 206 is a discriminator, not yet a formal contradiction.

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LargerCCDValueProvesDatabaseBug : Set where
data Delta8RowProvesAnalyticalDetection : Set where
data ArticleProseDefinesExactTableS5Identity : Set where
data CurrentCCDRowEqualsPublishedRow : Set where

data RegistryCIDCreatesAssayIdentity : Set where

largerCCDValueDoesNotProveDatabaseBug : LargerCCDValueProvesDatabaseBug → ⊥
largerCCDValueDoesNotProveDatabaseBug ()

delta8RowDoesNotProveAnalyticalDetection : Delta8RowProvesAnalyticalDetection → ⊥
delta8RowDoesNotProveAnalyticalDetection ()

articleProseDoesNotDefineExactTableS5Identity : ArticleProseDefinesExactTableS5Identity → ⊥
articleProseDoesNotDefineExactTableS5Identity ()

currentCCDRowDoesNotEqualPublishedRowByCitation : CurrentCCDRowEqualsPublishedRow → ⊥
currentCCDRowDoesNotEqualPublishedRowByCitation ()

registryCIDDoesNotCreateAssayIdentity : RegistryCIDCreatesAssayIdentity → ⊥
registryCIDDoesNotCreateAssayIdentity ()

------------------------------------------------------------------------
-- Pareto continuation.
------------------------------------------------------------------------

data CompoundRowParetoTarget : Set where
  acquireExactTableS5
  recoverPrepublicationSupportingData
  mapTableS5RowsToCDBIDs
  testRowColumnTransforms
  freezeBifurcatedLineage
  resumeInteractionTranslation : CompoundRowParetoTarget

record CompoundRowParetoStep : Set where
  constructor compound-row-pareto-step
  field
    priority : Nat
    target : CompoundRowParetoTarget
    action : String
    pays : String
    dominatedUntil : String
open CompoundRowParetoStep public

pareto0 : CompoundRowParetoStep
pareto0 = compound-row-pareto-step
  0 acquireExactTableS5
  "inspect the actual cannabinoid Table S5 PDF rows, including analyte label, CDB number, cultivar columns and units"
  "publication-side exact compound/value mapping"
  "none"

pareto1 : CompoundRowParetoStep
pareto1 = compound-row-pareto-step
  1 recoverPrepublicationSupportingData
  "look for 2023 manuscript/supporting-data state matching the CCD citation surface"
  "version-discriminator between submitted and published data"
  "exact final Table S5 should be known first or in parallel"

pareto2 : CompoundRowParetoStep
pareto2 = compound-row-pareto-step
  2 mapTableS5RowsToCDBIDs
  "join each cannabinoid analyte to PubChem/CDB identity and current CCD concentration rows without label-only equivalence"
  "compound-row identity"
  "requires exact Table S5"

pareto3 : CompoundRowParetoStep
pareto3 = compound-row-pareto-step
  3 testRowColumnTransforms
  "test deterministic swaps, offsets, unit transforms and replicate aggregation against all cannabinoid rows, not a single cherry-picked value"
  "candidate ingestion/transformation explanation"
  "requires both source matrices"

pareto4 : CompoundRowParetoStep
pareto4 = compound-row-pareto-step
  4 freezeBifurcatedLineage
  "retain published and CCD vectors separately if provenance cannot reconcile them"
  "consumer-safe composition object"
  "no silent averaging or overwrite"

pareto9 : CompoundRowParetoStep
pareto9 = compound-row-pareto-step
  9 resumeInteractionTranslation
  "only resume exposure/entourage concentration reasoning from a reconciled or explicitly bifurcated composition vector"
  "downstream pharmacology admission"
  "dominated by row-identity lineage"

------------------------------------------------------------------------
-- Temporal state.
------------------------------------------------------------------------

data RowTime : Set where
  submittedManuscript2023
  publishedArticle2024
  currentCCD2026 : RowTime

data RowInterpretation : Set where
  submittedRowSurfaceUnknown
  publishedAggregateSurfaceKnown
  ccdCompoundRowsKnown
  exactRowLineageExplained : RowInterpretation

data RowSummary : Set where rowIdentityStillOpen : RowSummary

RowCompatible : RowTime → RowInterpretation → Set
RowCompatible submittedManuscript2023 submittedRowSurfaceUnknown = ⊤
RowCompatible submittedManuscript2023 publishedAggregateSurfaceKnown = ⊥
RowCompatible submittedManuscript2023 ccdCompoundRowsKnown = ⊥
RowCompatible submittedManuscript2023 exactRowLineageExplained = ⊥
RowCompatible publishedArticle2024 submittedRowSurfaceUnknown = ⊤
RowCompatible publishedArticle2024 publishedAggregateSurfaceKnown = ⊤
RowCompatible publishedArticle2024 ccdCompoundRowsKnown = ⊥
RowCompatible publishedArticle2024 exactRowLineageExplained = ⊥
RowCompatible currentCCD2026 submittedRowSurfaceUnknown = ⊤
RowCompatible currentCCD2026 publishedAggregateSurfaceKnown = ⊤
RowCompatible currentCCD2026 ccdCompoundRowsKnown = ⊤
RowCompatible currentCCD2026 exactRowLineageExplained = ⊥

rowTemporalSystem : Temporal.TemporalEvidenceSystem
rowTemporalSystem = record
  { Time = RowTime
  ; Interpretation = RowInterpretation
  ; Compatible = RowCompatible
  ; Summary = RowSummary
  ; summarize = λ _ → rowIdentityStillOpen
  ; timeReference = λ
      { submittedManuscript2023 → "CCD concentration rows cite Wishart et al. as 2023 manuscript submitted"
      ; publishedArticle2024 → "Wishart et al. 2024 DOI 10.1021/acs.jafc.3c06616"
      ; currentCCD2026 → "current CCD concentration-detail / compound-card surface observed in 2026"
      }
  }

currentRowLineageStillOpen : Temporal.EvidenceFibre rowTemporalSystem currentCCD2026
currentRowLineageStillOpen = Temporal.liveInterpretationAt ccdCompoundRowsKnown tt

record WishartCCDCompoundRowBoundary : Set where
  constructor wishart-ccd-compound-row-boundary
  field
    publicationAggregateRetained : Bool
    currentCCDRowsRetained : Bool
    submittedVsPublishedSeparated : Bool
    pubChemIdentitySeparateFromAssayIdentity : Bool
    compoundMappingErrorProven : Bool
    exactLineageExplained : Bool
open WishartCCDCompoundRowBoundary public

canonicalWishartCCDCompoundRowBoundary : WishartCCDCompoundRowBoundary
canonicalWishartCCDCompoundRowBoundary =
  wishart-ccd-compound-row-boundary true true true true false false
