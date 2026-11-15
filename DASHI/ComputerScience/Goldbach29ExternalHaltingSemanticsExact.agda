module DASHI.ComputerScience.Goldbach29ExternalHaltingSemanticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ATTRIBUTED CROSS-PROVER SOURCE AUDIT
--
-- Owner: Mike Dupont / meta-introspector
-- Repository: meta-introspector/aok
-- Pinned revision: 428e2366045cb0b728115777df8bef14318a3bcf
-- Main path:
--   d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Main.lean
-- Claimed declaration:
--   ConjectureMachines.Goldbach29.goldbachProg_halts_iff
--
-- IMPORTANT AUTHORITY CORRECTION
-- ------------------------------
-- The theorem text is genuinely present in the pinned upstream tree, but an
-- exact Git-object audit shows Main.lean and Loops.lean are the SAME blob:
--
--   782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b
--
-- and that blob begins by importing `Cryptids.Goldbach29.Loops`. Therefore the
-- pinned tree is not a clean independent Main/Loops module pair: Loops.lean is
-- self-importing at this revision. Git history records Create Loops -> Rename
-- Loops to Main -> Create Loops, ending in the duplicate blob.
--
-- Under DASHI attribution rules this pays SOURCE-VISIBLE THEOREM TEXT, but it
-- does NOT pay a kernel-build receipt. We therefore no longer promote this
-- revision to verified external formal-theorem authority until a clean upstream
-- revision/build receipt is recovered or independently replayed.
--
-- Legacy regression token: `importedFormalTheoremSource` is intentionally
-- retired as a paid role for this revision; its historical presence in the
-- audit tests must not be read as current authority.
------------------------------------------------------------------------

data FormalAuthorityRole : Set where
  sourceVisibleTheoremText : FormalAuthorityRole
  buildVerifiedFormalTheoremSource : FormalAuthorityRole
  localAgdaReconstruction : FormalAuthorityRole

record ExternalFormalTheoremReceipt : Set where
  constructor externalFormalTheoremReceipt
  field
    role : FormalAuthorityRole
    owner : String
    repository : String
    revision : String
    sourcePath : String
    sourceBlob : String
    declaration : String
    theoremScope : String

open ExternalFormalTheoremReceipt public

goldbach29HaltingSemanticsReceipt : ExternalFormalTheoremReceipt
goldbach29HaltingSemanticsReceipt =
  externalFormalTheoremReceipt
    sourceVisibleTheoremText
    "Mike Dupont / meta-introspector"
    "meta-introspector/aok"
    "428e2366045cb0b728115777df8bef14318a3bcf"
    "d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Main.lean"
    "782ef73cb0b1e0ee72043f5f097b8b1b5213bd3b"
    "ConjectureMachines.Goldbach29.goldbachProg_halts_iff"
    "Text states: FractranHaltsFrom goldbachProg goldbachStart iff there exists an even n >= 4 with no prime-sum representation"

externalGoldbach29HaltingTheoremTextPresent : Bool
externalGoldbach29HaltingTheoremTextPresent = true

externalGoldbach29MainLoopsSameBlob : Bool
externalGoldbach29MainLoopsSameBlob = true

externalGoldbach29SemanticTreeBuildAuthorityPaid : Bool
externalGoldbach29SemanticTreeBuildAuthorityPaid = false

-- Backward-compatible name, now deliberately means only the source-text surface
-- is paid. Consumers requiring kernel authority must use the build-authority flag.
externalGoldbach29HaltingSemanticsSourcePaid : Bool
externalGoldbach29HaltingSemanticsSourcePaid = true

agdaGoldbach29HaltingSemanticsPaid : Bool
agdaGoldbach29HaltingSemanticsPaid = false

goldbachConjectureProvedByUpstreamTheorem : Bool
goldbachConjectureProvedByUpstreamTheorem = false

record Goldbach29ExternalSemanticsBoundary : Set where
  constructor goldbach29ExternalSemanticsBoundary
  field
    sourceRevisionPinned : Bool
    theoremTextPresent : Bool
    mainAndLoopsAreDistinctModules : Bool
    cleanUpstreamKernelBuildReceiptPaid : Bool
    upstreamLeanTheoremImportedAsAgdaProof : Bool
    theoremEquivalenceProvesNoCounterexample : Bool
    theoremTextCanSpecifyDeclaredHaltingConsumer : Bool
    theoremMayBeUsedAsVerifiedFormalAuthority : Bool

canonicalGoldbach29ExternalSemanticsBoundary :
  Goldbach29ExternalSemanticsBoundary
canonicalGoldbach29ExternalSemanticsBoundary =
  goldbach29ExternalSemanticsBoundary
    true true false false false false true false
