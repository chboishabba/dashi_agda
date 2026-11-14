module DASHI.ComputerScience.Goldbach30To29VendoredSourceAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- VENDORED SAME-OBJECT SOURCE RECEIPT
--
-- Upstream owner: Mike Dupont / meta-introspector
-- Repository: meta-introspector/aok
-- License: AGPL-3.0
--
-- The two Program.lean files below were recreated in this repository from the
-- upstream source bytes and Git returned the SAME blob identifiers as upstream.
-- This pays byte-level source-object identity for the machine definitions.
-- It does not by itself transport Lean proof terms into Agda.
--
-- The local LICENSE.AGPL-3.0 is a license/provenance notice which pins the
-- canonical upstream LICENSE blob; it is deliberately NOT represented as a
-- byte-identical copy of that legal-text object.
------------------------------------------------------------------------

record VendoredSourceObject : Set where
  constructor vendoredSourceObject
  field
    upstreamRevision : String
    upstreamPath : String
    localPath : String
    gitBlob : String
    byteIdentical : Bool

open VendoredSourceObject public

goldbach29ProgramSource : VendoredSourceObject
goldbach29ProgramSource =
  vendoredSourceObject
    "c168223e96f7acc6179044f2a365a92db2e350c3"
    "d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Program.lean"
    "vendor/meta-introspector-aok/c168223e96f7acc6179044f2a365a92db2e350c3/Goldbach29/Program.lean"
    "ff3f10a3e4c72771ac415a7f4bfb70a209478025"
    true

goldbach30ProgramSource : VendoredSourceObject
goldbach30ProgramSource =
  vendoredSourceObject
    "c168223e96f7acc6179044f2a365a92db2e350c3"
    "1fcb5ebe-bbab-4c12-bc38-4f1cd4739c1b/code/Cryptids/Goldbach30/Program.lean"
    "vendor/meta-introspector-aok/c168223e96f7acc6179044f2a365a92db2e350c3/Goldbach30/Program.lean"
    "ff748e1d68bf01d19e0c0998f6ac8d3a1c73e2f3"
    true

semanticDuplicateBlob : String
semanticDuplicateBlob = "782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b"

upstreamLicenseBlob : String
upstreamLicenseBlob = "0ad25db4bd1d86c452db3f9602ccdbe172438f52"

exactProgramSourceObjectsVendored : Bool
exactProgramSourceObjectsVendored = true

vendoredProgramSourcesContainFstepEnc : Bool
vendoredProgramSourcesContainFstepEnc = true

literalFirstTwentyFiveRulesShared : Bool
literalFirstTwentyFiveRulesShared = true

shiftedFailureTransitionShared : Bool
shiftedFailureTransitionShared = true

sourceDrivenFractranReplayAvailable : Bool
sourceDrivenFractranReplayAvailable = true

semanticTheoremTextVendored : Bool
semanticTheoremTextVendored = true

semanticMainLoopsDuplicateDetected : Bool
semanticMainLoopsDuplicateDetected = true

semanticBuildAuthorityPaid : Bool
semanticBuildAuthorityPaid = false

crossProverProofTransportPaid : Bool
crossProverProofTransportPaid = false

concreteFractranCheckpointFormalAttachmentPaid : Bool
concreteFractranCheckpointFormalAttachmentPaid = false

licenseNoticePresent : Bool
licenseNoticePresent = true

exactLicenseBlobVendored : Bool
exactLicenseBlobVendored = false

record GoldbachVendoredSourceBoundary : Set where
  constructor goldbachVendoredSourceBoundary
  field
    program29ByteIdentityPaid : Bool
    program30ByteIdentityPaid : Bool
    oneStepLeanBridgePresentInEachProgram : Bool
    replayReadsVendoredProgramBytes : Bool
    semanticTheoremTextPresent : Bool
    semanticMainLoopsAreDistinct : Bool
    semanticTreeBuildAuthorityPaid : Bool
    leanProofTransportedIntoAgda : Bool
    concreteCheckpointAttachmentFormal : Bool
    upstreamLicenseNoticePresent : Bool
    upstreamLicenseByteIdentityPaid : Bool
    upstreamAuthorshipRetained : Bool

canonicalGoldbachVendoredSourceBoundary : GoldbachVendoredSourceBoundary
canonicalGoldbachVendoredSourceBoundary =
  goldbachVendoredSourceBoundary
    true true true true true false false false false true false true
