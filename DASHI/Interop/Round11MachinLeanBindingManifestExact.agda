module DASHI.Interop.Round11MachinLeanBindingManifestExact where

------------------------------------------------------------------------
-- RECIPROCAL AGDA-SIDE MANIFEST FOR THE ROUTE-B LEAN BINDING
--
-- This is the Agda-side mirror of
--
--   Integration.BishopRound11MachinBindingManifest
--
-- in chboishabba/dashi_lean4.
--
-- The seven load-bearing Agda blobs below were checked against the live
-- route-B branch when this receipt was written.  Their Git blob IDs match the
-- Lean manifest exactly.
--
-- This module is provenance only: it does not claim that Lean imported or
-- kernel-replayed the Agda declarations.  It sharpens the residual to one
-- explicit generated/replay step.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

record SourceBlob : Set where
  constructor source-blob
  field
    path : String
    gitBlob : String

open SourceBlob public

bishopSubmoduleRepository : String
bishopSubmoduleRepository =
  "https://github.com/viktorcsimma/bishop.git"

bishopSubmoduleCommit : String
bishopSubmoduleCommit =
  "240e38c7f6938f20f865b1f956c5f084da48bd54"

sourceInstanceBlob : SourceBlob
sourceInstanceBlob =
  source-blob
    "DASHI/Moonshine/BishopRound11MachinSetoidComplexInstanceExact.agda"
    "ec132e001eeb7836078561e88fe2b3f54438facb"

machinConstructionBlob : SourceBlob
machinConstructionBlob =
  source-blob
    "DASHI/Foundations/BishopMachinArctanConstructionExact.agda"
    "be11dee1db4eb6856346267134dcd85fed96fc2a"

exponentialConvergenceBlob : SourceBlob
exponentialConvergenceBlob =
  source-blob
    "DASHI/Foundations/BishopExponentialSeriesConvergenceExact.agda"
    "b62d767e74c6473e31bdf86458d93445656f6978"

trigConvergenceBlob : SourceBlob
trigConvergenceBlob =
  source-blob
    "DASHI/Foundations/BishopConcreteTrigSeriesConvergenceExact.agda"
    "75b8b72ea4e240bfde706272beb5ff5e5fba9af5"

setoidComplexBlob : SourceBlob
setoidComplexBlob =
  source-blob
    "DASHI/Analysis/BishopSetoidComplexExact.agda"
    "739af368ced4b730225db4177529b281f4e8c493"

finiteQSeriesBlob : SourceBlob
finiteQSeriesBlob =
  source-blob
    "DASHI/Moonshine/JInvariantEisensteinBishopSetoidFiniteQSeriesExact.agda"
    "4787feafbd9630dc439556543c42c6b75bf7fdbd"

extractionBlob : SourceBlob
extractionBlob =
  source-blob
    "DASHI/Moonshine/JInvariantEisensteinBishopSetoidExtractionExact.agda"
    "baee86e7085c9193227142eb9713df9d2e4a546e"

loadBearingBlobs : List SourceBlob
loadBearingBlobs =
  sourceInstanceBlob
  ∷ machinConstructionBlob
  ∷ exponentialConvergenceBlob
  ∷ trigConvergenceBlob
  ∷ setoidComplexBlob
  ∷ finiteQSeriesBlob
  ∷ extractionBlob
  ∷ []

record SourceTheoremBinding : Set where
  constructor source-theorem-binding
  field
    agdaOwner : String
    agdaDeclaration : String
    leanOwner : String
    leanDeclaration : String

open SourceTheoremBinding public

expBinding : SourceTheoremBinding
expBinding =
  source-theorem-binding
    (path sourceInstanceBlob)
    "round11MachinExpConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.expConverges"

sineBinding : SourceTheoremBinding
sineBinding =
  source-theorem-binding
    (path sourceInstanceBlob)
    "round11MachinSineConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.sinConverges"

cosineBinding : SourceTheoremBinding
cosineBinding =
  source-theorem-binding
    (path sourceInstanceBlob)
    "round11MachinCosineConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.cosConverges"

atanFifthBinding : SourceTheoremBinding
atanFifthBinding =
  source-theorem-binding
    (path sourceInstanceBlob)
    "round11MachinAtanOneFifthConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.atanOneFifthConverges"

atan239Binding : SourceTheoremBinding
atan239Binding =
  source-theorem-binding
    (path sourceInstanceBlob)
    "round11MachinAtanOneTwoHundredThirtyNinthConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.atanOneTwoHundredThirtyNinthConverges"

machinPiBinding : SourceTheoremBinding
machinPiBinding =
  source-theorem-binding
    (path machinConstructionBlob)
    "bishopMachinPi"
    "Integration.BishopVendoredMachinPiSemantics"
    "machinPiB"

theoremBindings : List SourceTheoremBinding
theoremBindings =
  expBinding
  ∷ sineBinding
  ∷ cosineBinding
  ∷ atanFifthBinding
  ∷ atan239Binding
  ∷ machinPiBinding
  ∷ []

record ReciprocalManifestBoundary : Set where
  constructor reciprocal-manifest-boundary
  field
    bishopSubmoduleCommitPinned : Bool
    sevenLoadBearingBlobIdsRecorded : Bool
    agdaAndLeanManifestBlobIdsMatch : Bool
    declarationBindingTableRecorded : Bool
    leanPrimitiveExtractionCompilerOwned : Bool
    leanEndToEndRouteBCompilerOwned : Bool
    leanPinnedDeltaIdentityOwned : Bool
    leanCanonicalBishopCompletionBindingInhabited : Bool
    leanEveryAdmissibleBindingSetoidEquivalentToCanonical : Bool
    leanHypothesisFreeCanonicalRouteBOwned : Bool

    generatedAgdaToLeanReplayObserved : Bool
    leanExactHeadKernelReceiptObserved : Bool
    agdaExactHeadKernelReceiptObserved : Bool

open ReciprocalManifestBoundary public

canonicalReciprocalManifestBoundary :
  ReciprocalManifestBoundary
canonicalReciprocalManifestBoundary =
  reciprocal-manifest-boundary
    true true true true true true true
    true true true
    false false false
