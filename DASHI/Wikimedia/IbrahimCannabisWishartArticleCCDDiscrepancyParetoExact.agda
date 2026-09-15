module DASHI.Wikimedia.IbrahimCannabisWishartArticleCCDDiscrepancyParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTerpeneCommercialSampleQuantitativeAssayExact as Commercial
import DASHI.Wikimedia.IbrahimCannabisTerpenePubChemCIDAuthorityExact as PubChem
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- WISHART ARTICLE <-> CANNABIS COMPOUND DATABASE DATA-LINEAGE DISCREPANCY
--
-- Highest-alpha continuation after paying same-sample terpene composition.
-- The 2024 paper prose reports THCA concentrations spanning 133--162 mg/g dry
-- weight for the six commercial samples, with Tangerine Dream/Gabriola at the
-- low endpoint and Sensi Star/Alien Dawg at the high endpoint.  The current
-- Cannabis Compound Database THCA-A card, attributed to David S. Wishart et al.,
-- exposes a different six-sample vector (115--218 mg/g, including Alien Dawg
-- 206, Sensi Star 218, etc.).
--
-- This owner DOES NOT choose one surface as silently correct.  It types the
-- conflict and makes source/version/provenance reconciliation the next Pareto
-- payment before using a per-sample cannabinoid vector downstream.
------------------------------------------------------------------------

record SourceSurface : Set where
  constructor source-surface
  field
    label : String
    sourceKind : String
    sourceReference : String
    doiOrStableLink : String
    versionReference : String
    sameStudyClaim : Bool
open SourceSurface public

articleSurface : SourceSurface
articleSurface = source-surface
  "Wishart et al. article prose / corrected publication surface"
  "primary peer-reviewed publication"
  "Chemical Composition of Commercial Cannabis, J Agric Food Chem 72(25):14099-14113"
  "10.1021/acs.jafc.3c06616"
  "article page currently connected to correction DOI 10.1021/acs.jafc.4c01418"
  true

ccdSurface : SourceSurface
ccdSurface = source-surface
  "Cannabis Compound Database THCA-A concentration card"
  "author-linked database distribution surface"
  "CDB000016, Delta-9-tetrahydrocannabinolic acid A"
  "https://cannabisdatabase.ca/compounds/CDB000016"
  "Cannabis Database Version 1.0 current web surface"
  true

record THCARegistryIdentity : Set where
  constructor thca-registry-identity
  field
    canonicalLabel : String
    cannabisCompoundDatabaseId : String
    pubChemCID : String
    pubChemLink : String
    molecularFormula : String
    cidAuthority : String
    cdbIsPubChemCID : Bool
open THCARegistryIdentity public

thcaIdentity : THCARegistryIdentity
thcaIdentity = thca-registry-identity
  "delta9-tetrahydrocannabinolic acid A / THCA-A"
  "CDB000016"
  "98523"
  "https://pubchem.ncbi.nlm.nih.gov/compound/98523"
  "C22H30O4"
  "PubChem Compound"
  false

------------------------------------------------------------------------
-- Conflicting same-labelled sample values.
------------------------------------------------------------------------

record SampleValue : Set where
  constructor sample-value
  field
    sampleLabel : String
    valueMgPerGDryWeight : String
    surface : SourceSurface
    exactNumericValue : Bool
    endpointOnly : Bool
open SampleValue public

-- Article prose explicitly supplies endpoint values only for these labelled
-- samples; it does not expose a complete per-sample vector on the acquired
-- article surface.
articleTangerineDream : SampleValue
articleTangerineDream = sample-value
  "Tangerine Dream" "133" articleSurface true true

articleGabriola : SampleValue
articleGabriola = sample-value
  "Gabriola" "133" articleSurface true true

articleSensiStar : SampleValue
articleSensiStar = sample-value
  "Sensi Star" "162" articleSurface true true

articleAlienDawg : SampleValue
articleAlienDawg = sample-value
  "Alien Dawg" "162" articleSurface true true

-- Current CCD THCA-A card values.
ccdAlienDawg : SampleValue
ccdAlienDawg = sample-value "Alien Dawg" "206" ccdSurface true false

ccdGabriola : SampleValue
ccdGabriola = sample-value "Gabriola" "187" ccdSurface true false

ccdIslandHoney : SampleValue
ccdIslandHoney = sample-value "Island Honey" "194" ccdSurface true false

ccdQuadra : SampleValue
ccdQuadra = sample-value "Quadra" "194" ccdSurface true false

ccdSensiStar : SampleValue
ccdSensiStar = sample-value "Sensi Star" "218" ccdSurface true false

ccdTangerineDream : SampleValue
ccdTangerineDream = sample-value "Tangerine Dream" "115" ccdSurface true false

------------------------------------------------------------------------
-- Conflict is typed, not numerically averaged away.
------------------------------------------------------------------------

data AgreementStanding : Set where
  agrees
  disagrees
  unresolvedVersionJoin : AgreementStanding

record SameLabelConflict : Set where
  constructor same-label-conflict
  field
    sample : String
    articleValue : String
    databaseValue : String
    standing : AgreementStanding
    sourceIdentitySameEnoughForComparison : Bool
    exactVersionJoinPaid : Bool
    resolutionReference : String
open SameLabelConflict public

alienDawgConflict : SameLabelConflict
alienDawgConflict = same-label-conflict
  "Alien Dawg" "162" "206" disagrees true false
  "article prose and current CCD card differ; inspect article/SI/CCD ingestion/version lineage before downstream use"

sensiStarConflict : SameLabelConflict
sensiStarConflict = same-label-conflict
  "Sensi Star" "162" "218" disagrees true false
  "article prose and current CCD card differ; inspect article/SI/CCD ingestion/version lineage before downstream use"

tangerineDreamConflict : SameLabelConflict
tangerineDreamConflict = same-label-conflict
  "Tangerine Dream" "133" "115" disagrees true false
  "article prose and current CCD card differ; inspect article/SI/CCD ingestion/version lineage before downstream use"

gabriolaConflict : SameLabelConflict
gabriolaConflict = same-label-conflict
  "Gabriola" "133" "187" disagrees true false
  "article prose and current CCD card differ; inspect article/SI/CCD ingestion/version lineage before downstream use"

------------------------------------------------------------------------
-- Correction notice is retained but does not currently pay the data conflict.
------------------------------------------------------------------------

record CorrectionReceipt : Set where
  constructor correction-receipt
  field
    doi : String
    directLink : String
    publishedReference : String
    locatedContent : String
    correctsTHCAValuesOnLocatedSurface : Bool
open CorrectionReceipt public

wishartCorrection : CorrectionReceipt
wishartCorrection = correction-receipt
  "10.1021/acs.jafc.4c01418"
  "https://doi.org/10.1021/acs.jafc.4c01418"
  "Correction to Chemical Composition of Commercial Cannabis, J Agric Food Chem 72(25):14479"
  "located correction surface adds/discloses Dr. J. R. B. Dyck cannabis-company board/CSO/shareholding conflict-of-interest information; no THCA data correction was located on the acquired correction text"
  false

------------------------------------------------------------------------
-- Pareto reconciliation route.
------------------------------------------------------------------------

data ReconciliationTarget : Set where
  acquireSupplementaryTableS5
  identifyCCDConcentrationProvenance
  compareAnalyticalIdentityAndUnits
  recoverVersionTimestampOrIngestionTransform
  selectDownstreamPerSampleVector
  continueEntourageInteraction : ReconciliationTarget

record ReconciliationStep : Set where
  constructor reconciliation-step
  field
    priority : Nat
    target : ReconciliationTarget
    action : String
    pays : String
    dominatedUntil : String
open ReconciliationStep public

firstStep : ReconciliationStep
firstStep = reconciliation-step
  0 acquireSupplementaryTableS5
  "acquire the exact cannabinoid per-sample table/supporting data attached to DOI 10.1021/acs.jafc.3c06616 and preserve its version/hash/page/table coordinates"
  "primary per-sample cannabinoid vector closest to the publication object"
  "none"

secondStep : ReconciliationStep
secondStep = reconciliation-step
  1 identifyCCDConcentrationProvenance
  "follow each CDB000016 concentration detail to its source/version/ingestion record and determine whether the current CCD vector derives from the same article data, a transformed dataset, or another version"
  "database-value genealogy"
  "primary Table S5 acquisition should happen first"

thirdStep : ReconciliationStep
thirdStep = reconciliation-step
  2 compareAnalyticalIdentityAndUnits
  "verify THCA versus THCA-A analyte identity, dry-weight units, calibration, any dilution/conversion factors, and whether values are raw/mean/replicate/derived"
  "rules out WrongType differences masquerading as numeric disagreement"
  "requires both source surfaces"

fourthStep : ReconciliationStep
fourthStep = reconciliation-step
  3 recoverVersionTimestampOrIngestionTransform
  "recover CCD ingestion/version timestamp or transformation notes and compare against article publication/correction state"
  "temporal/version explanation if one exists"
  "requires provenance details"

fifthStep : ReconciliationStep
fifthStep = reconciliation-step
  4 selectDownstreamPerSampleVector
  "only after reconciliation, freeze the versioned per-sample cannabinoid vector used with the already-paid terpene sample profile"
  "same-object cannabinoid + terpene interaction input"
  "all earlier reconciliation gates"

lastStep : ReconciliationStep
lastStep = reconciliation-step
  9 continueEntourageInteraction
  "resume concentration-matched interaction/exposure translation only after the cannabinoid vector is provenance-stable"
  "mechanism experiment selection"
  "data-lineage conflict must be resolved first"

------------------------------------------------------------------------
-- Temporal evidence fibre: database updates can reopen/refine interpretation.
------------------------------------------------------------------------

data DiscrepancyTime : Set where
  article2024
  correction2024
  ccdCurrent
  reconciledFuture : DiscrepancyTime

data DiscrepancyInterpretation : Set where
  articleVectorCandidate
  ccdVectorCandidate
  unresolvedDataLineageConflict
  reconciledSameObjectVector : DiscrepancyInterpretation

data DiscrepancySummary : Set where quantitativeCannabinoidFrontierOpen : DiscrepancySummary

DiscrepancyCompatible : DiscrepancyTime → DiscrepancyInterpretation → Set
DiscrepancyCompatible article2024 articleVectorCandidate = ⊤
DiscrepancyCompatible article2024 ccdVectorCandidate = ⊥
DiscrepancyCompatible article2024 unresolvedDataLineageConflict = ⊥
DiscrepancyCompatible article2024 reconciledSameObjectVector = ⊥
DiscrepancyCompatible correction2024 articleVectorCandidate = ⊤
DiscrepancyCompatible correction2024 ccdVectorCandidate = ⊥
DiscrepancyCompatible correction2024 unresolvedDataLineageConflict = ⊥
DiscrepancyCompatible correction2024 reconciledSameObjectVector = ⊥
DiscrepancyCompatible ccdCurrent articleVectorCandidate = ⊤
DiscrepancyCompatible ccdCurrent ccdVectorCandidate = ⊤
DiscrepancyCompatible ccdCurrent unresolvedDataLineageConflict = ⊤
DiscrepancyCompatible ccdCurrent reconciledSameObjectVector = ⊥
DiscrepancyCompatible reconciledFuture articleVectorCandidate = ⊤
DiscrepancyCompatible reconciledFuture ccdVectorCandidate = ⊤
DiscrepancyCompatible reconciledFuture unresolvedDataLineageConflict = ⊥
DiscrepancyCompatible reconciledFuture reconciledSameObjectVector = ⊤

discrepancyTemporalSystem : Temporal.TemporalEvidenceSystem
discrepancyTemporalSystem = record
  { Time = DiscrepancyTime
  ; Interpretation = DiscrepancyInterpretation
  ; Compatible = DiscrepancyCompatible
  ; Summary = DiscrepancySummary
  ; summarize = λ _ → quantitativeCannabinoidFrontierOpen
  ; timeReference = λ
      { article2024 → "Wishart et al. primary article DOI 10.1021/acs.jafc.3c06616"
      ; correction2024 → "correction DOI 10.1021/acs.jafc.4c01418"
      ; ccdCurrent → "current Cannabis Compound Database CDB000016 concentration surface"
      ; reconciledFuture → "future source/version/ingestion reconciliation receipt"
      }
  }

currentConflictLive : Temporal.EvidenceFibre discrepancyTemporalSystem ccdCurrent
currentConflictLive = Temporal.liveInterpretationAt unresolvedDataLineageConflict tt

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ConflictingValuesMayBeAveragedWithoutLineage : Set where
data DatabaseCurrentValueSilentlyOverridesPublication : Set where
data PublicationProseSilentlyOverridesDatabase : Set where
data SameAuthorMeansSameVersion : Set where
data CorrectionDOIMeansNumericCorrection : Set where
data UnresolvedVectorCanDriveEntourageExperiment : Set where

conflictingValuesCannotBeAveragedWithoutLineage : ConflictingValuesMayBeAveragedWithoutLineage → ⊥
conflictingValuesCannotBeAveragedWithoutLineage ()

databaseDoesNotSilentlyOverridePublication : DatabaseCurrentValueSilentlyOverridesPublication → ⊥
databaseDoesNotSilentlyOverridePublication ()

publicationDoesNotSilentlyOverrideDatabase : PublicationProseSilentlyOverridesDatabase → ⊥
publicationDoesNotSilentlyOverrideDatabase ()

sameAuthorDoesNotMeanSameVersion : SameAuthorMeansSameVersion → ⊥
sameAuthorDoesNotMeanSameVersion ()

correctionDOIDoesNotMeanNumericCorrection : CorrectionDOIMeansNumericCorrection → ⊥
correctionDOIDoesNotMeanNumericCorrection ()

unresolvedVectorCannotDriveEntourageExperiment : UnresolvedVectorCanDriveEntourageExperiment → ⊥
unresolvedVectorCannotDriveEntourageExperiment ()

commercialBoundary : Commercial.CommercialCannabisQuantitativeAssayBoundary
commercialBoundary = Commercial.canonicalCommercialCannabisQuantitativeAssayBoundary

pubChemBoundary : PubChem.PubChemCIDAuthorityBoundary
pubChemBoundary = PubChem.canonicalPubChemCIDAuthorityBoundary

record WishartArticleCCDDiscrepancyBoundary : Set where
  constructor wishart-article-ccd-discrepancy-boundary
  field
    primaryArticleRetained : Bool
    databaseDistributionSurfaceRetained : Bool
    PubChemOwnsCID : Bool
    articleAndDatabaseVersionsSeparated : Bool
    conflictingValuesRemainExplicit : Bool
    correctionRoleBounded : Bool
    unresolvedConflictBlocksInteractionPromotion : Bool
    conflictResolved : Bool
open WishartArticleCCDDiscrepancyBoundary public

canonicalWishartArticleCCDDiscrepancyBoundary : WishartArticleCCDDiscrepancyBoundary
canonicalWishartArticleCCDDiscrepancyBoundary =
  wishart-article-ccd-discrepancy-boundary
    true true true true true true true false
