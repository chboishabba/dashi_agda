module DASHI.ComputerScience.Goldbach29ExternalHaltingSemanticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ATTRIBUTED CROSS-PROVER FORMAL SOURCE
--
-- Owner: Mike Dupont / meta-introspector
-- Repository: meta-introspector/aok
-- Source revision: 428e2366045cb0b728115777df8bef14318a3bcf
-- Source path:
--   d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Main.lean
-- Source declaration:
--   ConjectureMachines.Goldbach29.goldbachProg_halts_iff
--
-- The Lean theorem states that the 29-fraction program started at N0=710892
-- halts iff there exists an even n >= 4 which is not a sum of two primes.
--
-- This is imported FORMAL SOURCE authority.  It is not replayed by the Agda
-- kernel here.  In particular an equivalence
--
--     program halts <-> counterexample exists
--
-- does not prove that no counterexample exists, so it does not prove Goldbach.
------------------------------------------------------------------------

data FormalAuthorityRole : Set where
  importedFormalTheoremSource : FormalAuthorityRole
  localAgdaReconstruction : FormalAuthorityRole

record ExternalFormalTheoremReceipt : Set where
  constructor externalFormalTheoremReceipt
  field
    role : FormalAuthorityRole
    owner : String
    repository : String
    revision : String
    sourcePath : String
    declaration : String
    theoremScope : String

open ExternalFormalTheoremReceipt public

goldbach29HaltingSemanticsReceipt : ExternalFormalTheoremReceipt
goldbach29HaltingSemanticsReceipt =
  externalFormalTheoremReceipt
    importedFormalTheoremSource
    "Mike Dupont / meta-introspector"
    "meta-introspector/aok"
    "428e2366045cb0b728115777df8bef14318a3bcf"
    "d3e01240-2567-46da-9224-8a1bc6668f6b/code/Cryptids/Goldbach29/Main.lean"
    "ConjectureMachines.Goldbach29.goldbachProg_halts_iff"
    "FractranHaltsFrom goldbachProg goldbachStart iff there exists an even n >= 4 with no prime-sum representation"

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
    upstreamLeanHaltingIffCounterexample : Bool
    upstreamLeanTheoremImportedAsAgdaProof : Bool
    theoremEquivalenceProvesNoCounterexample : Bool
    theoremCanServeAsDeclaredHaltingConsumerSource : Bool

canonicalGoldbach29ExternalSemanticsBoundary :
  Goldbach29ExternalSemanticsBoundary
canonicalGoldbach29ExternalSemanticsBoundary =
  goldbach29ExternalSemanticsBoundary
    true true false false true
