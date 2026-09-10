module DASHI.ComputerScience.RSA260GNFSRevisionCustodySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GNFSStageRunReceiptExact as Run

------------------------------------------------------------------------
-- RSA-260 REVISION / CUSTODY SNOWBALL
--
-- Consumer: bind execution provenance as far as public evidence permits while
-- keeping chronology-derived candidates distinct from exact run revisions.
--
-- Primary first-party chronology from Eric Lu:
--   * 2026-08-13 00:11:58 Pacific: first Devin prompt for a drop-in las GPU
--     replacement;
--   * subsequent week: pipeline-wide optimization;
--   * 2026-08-18 12:14:19 UTC: RSA-260 run starts;
--   * 2026-09-03 01:48:57 UTC: RSA-260 run finishes.
--
-- Public upstream CADO mirror archaeology:
--   * latest master commit at/before the first prompt time is
--     a8ea6469cbfc84f19cf1573c8d33025f5e9acd66 (2026-08-06 12:10:45Z);
--   * later upstream commits exist before the RSA-260 run start, including
--     4d6f90dd018ff2d66e4a9e11c673fd28b89f21a6 and the 2026-08-16 build-system
--     branch work.
--
-- Therefore a8ea646... is a chronology candidate for the initially obtained
-- CADO tree, NOT an exact upstream revision receipt for the final run.
------------------------------------------------------------------------

data RevisionResolution : Set where
  unresolvedRevision : String → RevisionResolution
  chronologyCandidateRevision : String → String → RevisionResolution
  sourceReportedRevision : String → String → RevisionResolution
  exactSameObjectRevision : String → String → RevisionResolution

record RevisionCustodyReceipt : Set where
  constructor revision-custody-receipt
  field
    artifactReference : String
    roleReference : String
    resolution : RevisionResolution
    sourceReference : String
    exactRunSameObjectPaid : Bool
    publicSourceTreeBound : Bool
    executableDigestBound : Bool
    buildEnvironmentBound : Bool
    custodyLocationKnown : Bool
open RevisionCustodyReceipt public

------------------------------------------------------------------------
-- CADO upstream chronology candidates.
------------------------------------------------------------------------

cadoAtFirstDevinPrompt : RevisionCustodyReceipt
cadoAtFirstDevinPrompt =
  revision-custody-receipt
    "CADO-NFS upstream master"
    "latest public master commit at or before first Devin las prompt"
    (chronologyCandidateRevision
      "a8ea6469cbfc84f19cf1573c8d33025f5e9acd66"
      "GitHub mirror master tip at/before 2026-08-13 07:11:58Z; commit timestamp 2026-08-06 12:10:45Z")
    "public CADO-NFS GitHub mirror chronology + Eric Lu first-prompt timestamp"
    false true false false true

cadoAtRSA260RunStart : RevisionCustodyReceipt
cadoAtRSA260RunStart =
  revision-custody-receipt
    "CADO-NFS public repository history"
    "public upstream history visible before RSA-260 run start"
    (chronologyCandidateRevision
      "0a2e6cf01bb86c5c809bce26fba922d26794fb88"
      "a public repository commit before 2026-08-18 12:14:19Z; branch/history chronology does not show that Lu/Devin rebased or derived from this commit")
    "CADO-NFS GitHub mirror chronology + Eric Lu RSA-260 run-start timestamp"
    false true false false true

------------------------------------------------------------------------
-- Downstream modified implementation / msieve / executable custody.
------------------------------------------------------------------------

luDevinModifiedTree : RevisionCustodyReceipt
luDevinModifiedTree =
  revision-custody-receipt
    "Lu/Devin significantly modified CADO-NFS implementation"
    "source tree reported to have produced RSA-260"
    (unresolvedRevision
      "first-party article describes programs/interfaces/run scripts but exposes no exact public Git revision or source-tree locator")
    "Eric Lu, Factoring RSA-260, Cognition, 2026-09-09"
    false false false false false

msieveStage1Components : RevisionCustodyReceipt
msieveStage1Components =
  revision-custody-receipt
    "msieve components used in RSA-260 stage-1 polynomial selection"
    "upstream component contribution"
    (unresolvedRevision
      "Lu identifies components from msieve but does not name exact files, commit, release, or source-tree snapshot")
    "Eric Lu, Factoring RSA-260 + Jason Papadopoulos/Msieve project documentation"
    false false false false false

rsa260ExecutableCustody : RevisionCustodyReceipt
rsa260ExecutableCustody =
  revision-custody-receipt
    "RSA-260 executed GNFS pipeline"
    "compiled executable/container/build identity"
    (unresolvedRevision
      "no public exact binary digest, container digest, build manifest, compiler/toolchain lock, or runnable source revision located")
    "current public-source snowball"
    false false false false false

------------------------------------------------------------------------
-- Run linkage remains source-reported but not revision-bound.
------------------------------------------------------------------------

latticeRunStillUnboundToRevision : Run.StageRunReceipt
latticeRunStillUnboundToRevision = Run.rsa260LatticeSieveRun

linearAlgebraRunStillUnboundToRevision : Run.StageRunReceipt
linearAlgebraRunStillUnboundToRevision = Run.rsa260LinearAlgebraRun

------------------------------------------------------------------------
-- WrongType / temporal-attribution firewalls.
------------------------------------------------------------------------

data LatestBeforePromptIsExactCheckout : Set where
data LatestBeforeRunIsExactRunRevision : Set where
data PublicUpstreamCommitIsModifiedTreeCommit : Set where
data TimelineAdjacencyProvesDerivation : Set where
data SourceReportedExecutionPinsBinary : Set where
data NamedMsieveContributionPinsMsieveRevision : Set where

latestBeforePromptDoesNotProveCheckout : LatestBeforePromptIsExactCheckout → ⊥
latestBeforePromptDoesNotProveCheckout ()

latestBeforeRunDoesNotProveRunRevision : LatestBeforeRunIsExactRunRevision → ⊥
latestBeforeRunDoesNotProveRunRevision ()

upstreamCommitDoesNotBecomeModifiedTree : PublicUpstreamCommitIsModifiedTreeCommit → ⊥
upstreamCommitDoesNotBecomeModifiedTree ()

temporalAdjacencyDoesNotCreateDerivation : TimelineAdjacencyProvesDerivation → ⊥
temporalAdjacencyDoesNotCreateDerivation ()

reportedRunDoesNotPinBinary : SourceReportedExecutionPinsBinary → ⊥
reportedRunDoesNotPinBinary ()

msieveNameDoesNotPinRevision : NamedMsieveContributionPinsMsieveRevision → ⊥
msieveNameDoesNotPinRevision ()

------------------------------------------------------------------------
-- Current custody frontier.
------------------------------------------------------------------------

record RSA260RevisionCustodyBoundary : Set where
  constructor rsa260-revision-custody-boundary
  field
    firstPromptChronologyRetained : Bool
    runChronologyRetained : Bool
    prePromptCadoCandidateRetainedAsCandidateOnly : Bool
    exactCadoCheckoutUsedKnown : Bool
    exactMsieveContributionRevisionKnown : Bool
    publicLuDevinModifiedTreeKnown : Bool
    executableOrContainerDigestKnown : Bool
    exactBuildEnvironmentKnown : Bool
    exactRunRevisionSameObjectPaid : Bool
open RSA260RevisionCustodyBoundary public

canonicalRSA260RevisionCustodyBoundary : RSA260RevisionCustodyBoundary
canonicalRSA260RevisionCustodyBoundary =
  rsa260-revision-custody-boundary
    true true true
    false false false false false false
