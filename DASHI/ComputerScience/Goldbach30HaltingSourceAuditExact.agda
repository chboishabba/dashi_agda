module DASHI.ComputerScience.Goldbach30HaltingSourceAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GOLDBACH30 HALTING-SOURCE AUDIT
--
-- Upstream commit 7added5000a75226a834ba7aab08a7380f0c70b3 has a signed
-- development narrative which states that
--
--   ConjectureMachines.Goldbach30.goldbachProg_halts_iff
--
-- exists in Cryptids/Goldbach30/Main.lean and that a no-sorry build passed.
-- However, a recursive audit of that exact commit tree finds the identified
-- Goldbach30 directory contains Program.lean only; no Goldbach30/Main.lean or
-- Goldbach30/Loops.lean occurs anywhere in the audited tree.  Current indexed
-- repository search likewise exposes Goldbach30/Program.lean but not the
-- claimed theorem source.
--
-- Under DASHI attribution rules this is development-narrative evidence, not
-- imported formal theorem authority.  The theorem statement is a strong
-- acquisition lead, but the formal-source payment remains open.
------------------------------------------------------------------------

data Goldbach30SourceRole : Set where
  developmentNarrativeClaim : Goldbach30SourceRole
  importedFormalTheoremSource : Goldbach30SourceRole

record Goldbach30ClaimReceipt : Set where
  constructor goldbach30ClaimReceipt
  field
    role : Goldbach30SourceRole
    owner : String
    repository : String
    revision : String
    claimedDeclaration : String
    claimedScope : String
    auditedTreeSha : String

open Goldbach30ClaimReceipt public

goldbach30NarrativeReceipt : Goldbach30ClaimReceipt
goldbach30NarrativeReceipt =
  goldbach30ClaimReceipt
    developmentNarrativeClaim
    "Mike Dupont / meta-introspector"
    "meta-introspector/aok"
    "7added5000a75226a834ba7aab08a7380f0c70b3"
    "ConjectureMachines.Goldbach30.goldbachProg_halts_iff"
    "Claimed: 30-fraction program halts from N0 iff an even n >= 4 has no representation as a sum of two primes"
    "1ff3d6acbc46a2b01fc4663964eb031aca7635e4"

goldbach30NarrativeHaltingClaimFound : Bool
goldbach30NarrativeHaltingClaimFound = true

goldbach30MainFilePresentInAuditedTree : Bool
goldbach30MainFilePresentInAuditedTree = false

goldbach30LoopsFilePresentInAuditedTree : Bool
goldbach30LoopsFilePresentInAuditedTree = false

goldbach30FormalHaltingSourceFound : Bool
goldbach30FormalHaltingSourceFound = false

record Goldbach30HaltingSourceAuditBoundary : Set where
  constructor goldbach30HaltingSourceAuditBoundary
  field
    narrativeClaimExists : Bool
    programSourceExists : Bool
    mainSourceExists : Bool
    loopsSourceExists : Bool
    narrativePromotedToFormalTheoremAuthority : Bool
    formalHaltingAttachmentPaid : Bool
    acquisitionShouldSearchOtherRevisionOrRequestSource : Bool

canonicalGoldbach30HaltingSourceAuditBoundary :
  Goldbach30HaltingSourceAuditBoundary
canonicalGoldbach30HaltingSourceAuditBoundary =
  goldbach30HaltingSourceAuditBoundary
    true true false false false false true
