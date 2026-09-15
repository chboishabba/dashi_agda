module DASHI.Wikimedia.IbrahimFirstLinkV3ExecutionLanePruningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimFirstLinkProducerOutputPathResidualExact as OutputPath
import DASHI.Wikimedia.IbrahimFirstLinkRepositoryHistoryCustodyPruningExact as History

------------------------------------------------------------------------
-- IBRAHIM HISTORICAL FLN: V3 EXECUTION-LANE PRUNING
--
-- Public source archaeology contains an apparently attractive older lane where
-- producer and combiner use the same `flnetwork` directory.  That cannot be
-- promoted to the published full First Link Network: the exact old VACC worker
-- stops after ten pages of each input chunk.  A sibling desktop/cluster scratch
-- variant stops after 1000 pages and then overwrites its cluster paths with
-- desktop paths.  These are useful development/execution-history receipts, but
-- neither pays the full-corpus producer-to-combiner same-object edge.
------------------------------------------------------------------------

publicProducerRepository : Attribution.AttributedSource
publicProducerRepository = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "marksibrahim/wikipedia_network historical V3 producer and VACC wrappers"
  "GitHub public producer repository"
  "2015 public snapshot"
  "https://github.com/marksibrahim/wikipedia_network"
  (Attribution.namedSourceKind "public historical execution-source archaeology")
  "supports source-code path topology, 112-job submission topology and explicit test page limits only; does not prove exact executed revision, dump-byte identity, complete shard custody or published FLN identity"
  Attribution.publicAttribution

executionArtifactQid : Identity.ExternalIdentityDemand
executionArtifactQid = Identity.mkOptionalIdentityDemand
  "Ibrahim historical FLN V3 execution-lane pruning"
  "historical source-code execution artifact identity"
  "old VACC/V3 producer scripts"
  Identity.wikidataQid
  (Identity.notApplicable
    "repository source artifacts are identified by repository path/blob provenance here; no Wikidata entity is required for the same-object consumer")

record V3ExecutionSourceReceipt : Set where
  constructor v3-execution-source-receipt
  field
    repositoryPath : String
    gitBlobSha : String
    inputPathSurface : String
    outputPathSurface : String
    submittedOrEnumeratedJobs : String
    explicitPageLimit : String
    fullPublishedProducerPaid : Bool
open V3ExecutionSourceReceipt public

oldVaccWorker : V3ExecutionSourceReceipt
oldVaccWorker = v3-execution-source-receipt
  "code/old_code/old_vacc/process_xml_v3.py"
  "959799f08bafbabfae675e834ef27b65107b7448"
  "/users/m/s/msibrahi/full_wiki_data/small*.xml"
  "/users/m/s/msibrahi/v3/results/flnetwork/<i>.json"
  "112 chunk names; paired run_vacc.py submits indices 0..111"
  "if p > 10: break"
  false

oldVaccWrapper : V3ExecutionSourceReceipt
oldVaccWrapper = v3-execution-source-receipt
  "code/old_code/old_vacc/run_vacc.py"
  "70e50aa98a12cce518c60d74583d8165bd389fc7"
  "invokes process_xml_v3.py with one integer job index"
  "/users/m/s/msibrahi/v3/code/vacc_logs/ job-script surface"
  "for i in range(0,112), qsub wikijob<i>.script"
  "worker owns ten-page cap"
  false

siblingV3ScratchWorker : V3ExecutionSourceReceipt
siblingV3ScratchWorker = v3-execution-source-receipt
  "code/old_code/process/process_xml_v3.py"
  "d6c5f939234e0160f0244f3396cb1c552d5bc6aa"
  "comments retain enwiki_20141106.xml and small*.xml paths; runtime later points to Desktop/wiki_v3"
  "cluster first_link_network path is overwritten by Desktop output path"
  "112 file names remain enumerated"
  "if p > 1000: break"
  false

------------------------------------------------------------------------
-- A consistent output basename/path is not enough to identify the production
-- object if the worker deliberately truncates every input.
------------------------------------------------------------------------

data LaneCase : Set where
  pathConsistentTruncatedLane pathConsistentFullLane : LaneCase

data PathSurface : Set where sameFlnetworkPath : PathSurface
data CorpusCoverage : Set where truncatedCoverage fullCoverage : CorpusCoverage

pathSurface : LaneCase → PathSurface
pathSurface _ = sameFlnetworkPath

corpusCoverage : LaneCase → CorpusCoverage
corpusCoverage pathConsistentTruncatedLane = truncatedCoverage
corpusCoverage pathConsistentFullLane = fullCoverage

open import DASHI.Core.IntersectionalNonFactorability as INF

pathCoverageDefect : INF.NonFactorabilityWitness pathSurface corpusCoverage
pathCoverageDefect = INF.nonFactorabilityWitness
  pathConsistentTruncatedLane pathConsistentFullLane refl (λ ())

pathConsistencyCannotFactorFullCorpusProduction :
  INF.FactorsThrough pathSurface corpusCoverage → ⊥
pathConsistencyCannotFactorFullCorpusProduction =
  INF.witnessRulesOutEveryFlatFactorisation pathCoverageDefect

------------------------------------------------------------------------
-- Existing residuals remain authoritative.
------------------------------------------------------------------------

outputPathBoundary : OutputPath.ProducerOutputPathBoundary
outputPathBoundary = OutputPath.canonicalProducerOutputPathBoundary

historyBoundary : History.RepositoryHistoryCustodyBoundary
historyBoundary = History.canonicalRepositoryHistoryCustodyBoundary

------------------------------------------------------------------------
-- Pruned and surviving routes.
------------------------------------------------------------------------

prunedRoute : String
prunedRoute =
  "Do not use the old V3/VACC flnetwork path consistency as payment for the published full FLN: the surviving path-consistent worker is explicitly capped at ten pages per chunk, and its sibling scratch worker is capped at 1000 pages and redirected to desktop outputs."

remainingRoute : String
remainingRoute =
  "The full-production custody residual therefore remains external/historical: recover the exact 2014 dump object/hash, decompression/rename receipt, raw split operation/chunk hashes, the actually executed uncapped producer revision or cluster wrapper, custody between numbered outputs and combiner inputs, and the author-hosted fln.json hash/same-object comparison."

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SamePathMeansSameProductionObject : Set where
data JobCountMeansFullCoverage : Set where
data HistoricalTestWorkerMeansExecutedProductionWorker : Set where
data QidRequiredForExecutionArtifact : Set where

samePathDoesNotMeanSameProductionObject : SamePathMeansSameProductionObject → ⊥
samePathDoesNotMeanSameProductionObject ()

jobCountDoesNotMeanFullCoverage : JobCountMeansFullCoverage → ⊥
jobCountDoesNotMeanFullCoverage ()

historicalTestWorkerDoesNotBecomeProductionReceipt :
  HistoricalTestWorkerMeansExecutedProductionWorker → ⊥
historicalTestWorkerDoesNotBecomeProductionReceipt ()

qidIsNotRequiredForRepositoryArtifactIdentity : QidRequiredForExecutionArtifact → ⊥
qidIsNotRequiredForRepositoryArtifactIdentity ()

record V3ExecutionLanePruningBoundary : Set where
  constructor v3-execution-lane-pruning-boundary
  field
    oldVacc112JobTopologyObserved : Bool
    oldVaccFlnetworkPathConsistencyObserved : Bool
    oldVaccTenPageCapObserved : Bool
    siblingThousandPageCapObserved : Bool
    siblingDesktopOverrideObserved : Bool
    pathConsistencyPromotedToFullProduction : Bool
    exactExecutedFullProducerStillUnpaid : Bool
    externalCustodyRouteStillRequired : Bool
    qidNonApplicabilityRetained : Bool
open V3ExecutionLanePruningBoundary public

canonicalV3ExecutionLanePruningBoundary : V3ExecutionLanePruningBoundary
canonicalV3ExecutionLanePruningBoundary =
  v3-execution-lane-pruning-boundary
    true true true true true false true true true
