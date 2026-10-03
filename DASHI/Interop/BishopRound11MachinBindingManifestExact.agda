module DASHI.Interop.BishopRound11MachinBindingManifestExact where

------------------------------------------------------------------------
-- CONTENT-ADDRESSED ROUND11 / MACHIN ROUTE-B BINDING MANIFEST
--
-- Reciprocal owner of:
--   dashi_lean4/Integration/BishopRound11MachinBindingManifest.lean
--
-- This receipt pins the exact Agda source blobs consumed by the Lean mirror
-- surface.  It is provenance, not a transported proof term.
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

agdaSourceRepository : String
agdaSourceRepository =
  "https://github.com/chboishabba/dashi_agda.git"

agdaSourceCommit : String
agdaSourceCommit =
  "c72ea464663a02333319f2254967c94bd188f5f5"

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

record DeclarationBinding : Set where
  constructor declaration-binding
  field
    agdaOwner : String
    agdaDeclaration : String
    leanOwner : String
    leanDeclaration : String

open DeclarationBinding public

expBinding : DeclarationBinding
expBinding =
  declaration-binding
    (path sourceInstanceBlob)
    "round11MachinExpConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.expConverges"

sineBinding : DeclarationBinding
sineBinding =
  declaration-binding
    (path sourceInstanceBlob)
    "round11MachinSineConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.sinConverges"

cosineBinding : DeclarationBinding
cosineBinding =
  declaration-binding
    (path sourceInstanceBlob)
    "round11MachinCosineConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.cosConverges"

atanFifthBinding : DeclarationBinding
atanFifthBinding =
  declaration-binding
    (path sourceInstanceBlob)
    "round11MachinAtanOneFifthConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.atanOneFifthConverges"

atan239Binding : DeclarationBinding
atan239Binding =
  declaration-binding
    (path sourceInstanceBlob)
    "round11MachinAtanOneTwoHundredThirtyNinthConverges"
    "Integration.BishopRound11MachinSourceBinding"
    "Round11MachinSourceBinding.atanOneTwoHundredThirtyNinthConverges"

machinPiBinding : DeclarationBinding
machinPiBinding =
  declaration-binding
    (path machinConstructionBlob)
    "bishopMachinPi"
    "Integration.BishopVendoredMachinPiSemantics"
    "machinPiB"

declarationBindings : List DeclarationBinding
declarationBindings =
  expBinding
  ∷ sineBinding
  ∷ cosineBinding
  ∷ atanFifthBinding
  ∷ atan239Binding
  ∷ machinPiBinding
  ∷ []

record BindingManifestBoundary : Set where
  constructor binding-manifest-boundary
  field
    agdaSourceCommitPinned : Bool
    bishopSubmoduleCommitPinned : Bool
    loadBearingAgdaBlobsPinned : Bool
    declarationBindingTableOwned : Bool
    reciprocalLeanManifestSourceWritten : Bool
    leanCanonicalBindingInhabited : Bool
    leanBindingUniqueUpToBishopSetoid : Bool
    leanCanonicalRouteBHypothesisFree : Bool
    leanGeneratedBindingTableKernelMatchSourceOwned : Bool

    generatedCrossProverReplayObserved : Bool
    leanKernelReceiptObserved : Bool
    agdaKernelReceiptObservedForCurrentHead : Bool

open BindingManifestBoundary public

canonicalBindingManifestBoundary : BindingManifestBoundary
canonicalBindingManifestBoundary =
  binding-manifest-boundary
    true true true true true
    true true true true
    false false false
