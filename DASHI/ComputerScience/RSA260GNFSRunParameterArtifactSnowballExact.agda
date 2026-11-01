module DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260GNFSStageRunReceiptExact as Run
import DASHI.ComputerScience.RSA260GNFSRevisionCustodySnowballExact as Custody

------------------------------------------------------------------------
-- RSA-260 RUN PARAMETER / ATTACHED-ARTIFACT SNOWBALL
--
-- Eric Lu's primary technical account publishes exact stage chronology,
-- selected polynomial data, run parameters, and an attachment locator for the
-- 22 trial-sieved polynomials.  These substantially strengthen run identity,
-- but they do not identify an exact source revision, binary, or container.
------------------------------------------------------------------------

record RunParameterReceipt : Set where
  constructor run-parameter-receipt
  field
    stageReference : String
    runReference : String
    parameterReference : String
    sourceReference : String
    firstPartyPublished : Bool
    exactRunCarrierNamed : Bool
    executableRevisionBound : Bool
    independentlyReproduced : Bool
open RunParameterReceipt public

rsa260PolyselectParameters : RunParameterReceipt
rsa260PolyselectParameters =
  run-parameter-receipt
    "polynomial selection"
    "RSA-260"
    "GPU stage 1 polyselect-gps1 on B200/GB200/GB300 plus CADO polyselect; degree 6; P 2e7 and 3e7; incr 110880 and 465585120; ad 0 to above 1.04e16"
    "Eric Lu, Factoring RSA-260, Appendix 2 / Appendix 3"
    true true false false

rsa260SieveParameters : RunParameterReceipt
rsa260SieveParameters =
  run-parameter-receipt
    "lattice sieving"
    "RSA-260"
    "A 33; sqside 1; lpb 36/37; lim 2147483648/2147483648; mfb 72/111; ncurves 50/35; fill_bands 2; host_mr 1; qmin 1000000000; qrange 60000; special q 1000000000..39091320000; rels_wanted 13.46B then 13.85B; las.threads 22; siqs.threads 2; wutimeout 7200"
    "Eric Lu, Factoring RSA-260, Appendix 3"
    true true false false

rsa260FilterParameters : RunParameterReceipt
rsa260FilterParameters =
  run-parameter-receipt
    "filtering and merge"
    "RSA-260"
    "target_density 150.0; purge.keep 160; dup1 nshards 16; nslices_log 4; outfmt .zst; dup2 concurrent; purge/merge gzip off"
    "Eric Lu, Factoring RSA-260, Appendix 3"
    true true false false

rsa260LinearAlgebraParameters : RunParameterReceipt
rsa260LinearAlgebraParameters =
  run-parameter-receipt
    "block Wiedemann linear algebra"
    "RSA-260"
    "krylov m=512 n=512; two width-256 sequences; simd=256; nullspace=left; mm_impl=cuda; comm_impl=nccl; checkpoints every 8192, retained every 32768 for mksol; grids 4x2/4x4/8x4/16x4 on GB300/GB200; mksol 40 ranges of 32768; gather 2x2 on 4 GB200 nodes"
    "Eric Lu, Factoring RSA-260, Appendix 3"
    true true false false

rsa260SquareRootParameters : RunParameterReceipt
rsa260SquareRootParameters =
  run-parameter-receipt
    "characters and square root"
    "RSA-260"
    "nchar 50 on one B200 node; -ab pass on CPU; GPU sqrt; one dependency per node; dependencies 8..14; final factor-producing version used GPU-accelerated NTT multiplication"
    "Eric Lu, Factoring RSA-260, Appendix 2 / Appendix 3"
    true true false false

------------------------------------------------------------------------
-- Exact selected polynomial published inline by the primary source.
------------------------------------------------------------------------

record SelectedPolynomialReceipt : Set where
  constructor selected-polynomial-receipt
  field
    runReference : String
    polynomialReference : String
    coefficientReference : String
    selectionMetricReference : String
    sourceReference : String
    inlinePrimaryCarrier : Bool
    attachmentSameObjectClaimedByAuthor : Bool
    attachmentBytesAcquiredHere : Bool
    recomputedSelectionMetric : Bool
open SelectedPolynomialReceipt public

rsa260SelectedPolynomial : SelectedPolynomialReceipt
rsa260SelectedPolynomial =
  selected-polynomial-receipt
    "RSA-260"
    "c260-r1"
    "Y0=-221673351566952308029695237213052836736183; Y1=5766034074997040571677; c0=4438326758963496161172848385157253702543453653246272; c1=-2760724998540198898516614911500562788411825980; c2=-3288611114230578563553198296458642435160; c3=950383683194810225243935581823335; c4=541831494549130032021283293; c5=-32669802676467106300; c6=-1863645537600; skew=3226459.164"
    "degree 6; MurphyE 6.633e-10; author reports c260-r2 1-2% lower yield and c260-p1 13-16% lower yield"
    "Eric Lu, Factoring RSA-260, Appendix 2 / Appendix 3"
    true true false false

------------------------------------------------------------------------
-- Primary attached artifact.
--
-- The HTML primary source links the 22 trial-sieved polynomials to the exact
-- locator below.  The current web fetch path resolves that locator but cannot
-- retrieve application/gzip, so bytes/digest/content inspection stay open.
------------------------------------------------------------------------

data ArtifactAcquisitionState : Set where
  exactLocatorOnly : String → ArtifactAcquisitionState
  bytesAcquiredDigestUnbound : String → ArtifactAcquisitionState
  bytesAndDigestBound : String → String → ArtifactAcquisitionState

record PrimaryAttachedArtifactReceipt : Set where
  constructor primary-attached-artifact-receipt
  field
    artifactLabel : String
    exactLocator : String
    relationshipToRun : String
    sourceReference : String
    acquisitionState : ArtifactAcquisitionState
    nativeAttachmentClaimedByPrimarySource : Bool
    bytesInspected : Bool
    contentDigestBound : Bool
    exactSourceCodeArtifact : Bool
    exactExecutableArtifact : Bool
open PrimaryAttachedArtifactReceipt public

rsa260TrialSievedPolynomialArchive : PrimaryAttachedArtifactReceipt
rsa260TrialSievedPolynomialArchive =
  primary-attached-artifact-receipt
    "RSA-260 22 trial-sieved polynomial archive"
    "https://cognition.com/documents/c260-polys.tar.gz"
    "primary article says the attachment contains the 22 distinct trial-sieved polynomials; selected c260-r1 is also printed inline"
    "Eric Lu, Factoring RSA-260, Appendix 2, attachment link"
    (exactLocatorOnly
      "native application/gzip locator resolved from primary HTML; current acquisition tool could not retrieve the bytes")
    true false false false false

------------------------------------------------------------------------
-- Cross-layer retention.
------------------------------------------------------------------------

rsa260ReportedLatticeRun : Run.StageRunReceipt
rsa260ReportedLatticeRun = Run.rsa260LatticeSieveRun

rsa260RevisionStillUnresolved : Custody.RevisionCustodyReceipt
rsa260RevisionStillUnresolved = Custody.luDevinModifiedTree

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ParametersIdentifyExecutable : Set where
data PublishedPolynomialIdentifiesSourceRevision : Set where
data AttachmentLocatorMeansBytesInspected : Set where
data AttachmentMeansSourceCode : Set where
data SameOutputParametersProveSameImplementation : Set where
data AuthorMetricMeansIndependentMetricReproduction : Set where

parametersDoNotIdentifyExecutable : ParametersIdentifyExecutable → ⊥
parametersDoNotIdentifyExecutable ()

polynomialDoesNotIdentifySourceRevision : PublishedPolynomialIdentifiesSourceRevision → ⊥
polynomialDoesNotIdentifySourceRevision ()

locatorDoesNotMeanBytesInspected : AttachmentLocatorMeansBytesInspected → ⊥
locatorDoesNotMeanBytesInspected ()

runAttachmentDoesNotBecomeSourceCode : AttachmentMeansSourceCode → ⊥
runAttachmentDoesNotBecomeSourceCode ()

sameParametersDoNotProveSameImplementation : SameOutputParametersProveSameImplementation → ⊥
sameParametersDoNotProveSameImplementation ()

authorMetricDoesNotBecomeIndependentReproduction : AuthorMetricMeansIndependentMetricReproduction → ⊥
authorMetricDoesNotBecomeIndependentReproduction ()

------------------------------------------------------------------------
-- Current parameter/artifact frontier.
------------------------------------------------------------------------

record RSA260RunParameterArtifactBoundary : Set where
  constructor rsa260-run-parameter-artifact-boundary
  field
    exactPrimaryRunParametersRetained : Bool
    selectedPolynomialRetainedInline : Bool
    primaryAttachmentLocatorRetained : Bool
    attachmentBytesAcquired : Bool
    attachmentDigestBound : Bool
    exactSourceRevisionBound : Bool
    exactExecutableBound : Bool
    independentRunReproductionPaid : Bool
open RSA260RunParameterArtifactBoundary public

canonicalRSA260RunParameterArtifactBoundary : RSA260RunParameterArtifactBoundary
canonicalRSA260RunParameterArtifactBoundary =
  rsa260-run-parameter-artifact-boundary
    true true true false false false false false
