module DASHI.Interop.SLRBinaryWorldWireParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact cross-kernel contract for the production world-store wire ABI.
--
-- Runtime owner:
--   chboishabba/slr :: crates/sl-world-store
--
-- Wire v1 fixed header, in order:
--   magic[4] = "SLRW"
--   version : u16 little-endian = 1
--   kind    : u8
--   flags   : u8
--   idLen   : u32 little-endian
--   auxLen  : u32 little-endian
--   bodyLen : u32 little-endian
--   iteration : i64 little-endian
-- followed by exactly idLen UTF-8 bytes, auxLen UTF-8 bytes and bodyLen
-- opaque kind-owned binary bytes.  Presence of iteration/aux is carried by
-- flags; no textual sentinel, JSON object, JSONB payload or regex parser is
-- part of the production ABI.
------------------------------------------------------------------------

data WorldWireKind : Set where
  sourceManifestation : WorldWireKind
  pnfCandidate : WorldWireKind
  worldAtom : WorldWireKind
  gap : WorldWireKind
  obligation : WorldWireKind
  routeAction : WorldWireKind
  iteration : WorldWireKind

worldWireKindTag : WorldWireKind → Nat
worldWireKindTag sourceManifestation = 1
worldWireKindTag pnfCandidate = 2
worldWireKindTag worldAtom = 3
worldWireKindTag gap = 4
worldWireKindTag obligation = 5
worldWireKindTag routeAction = 6
worldWireKindTag iteration = 7

wireVersion : Nat
wireVersion = 1

record BinaryWorldWireParity : Set where
  constructor binaryWorldWireParity
  field
    magicIsSLRW : Bool
    versionIsOne : Bool
    littleEndianHeader : Bool
    kindTagMappingExact : Bool
    lengthsAreExplicitU32 : Bool
    iterationCoordinateIsI64 : Bool
    iterationPresenceCarriedByFlag : Bool
    auxPresenceCarriedByFlag : Bool
    idAndAuxAreLengthBoundedUtf8 : Bool
    bodyIsLengthBoundedBinary : Bool
    frameMayBeDecodedIncrementally : Bool
    wholeStreamBufferRequired : Bool
    jsonTransportUsed : Bool
    jsonPayloadUsed : Bool
    postgresJsonbUsed : Bool
    regexParserUsed : Bool
    postgresBinaryCopyUsed : Bool
    postgresBodyStoredAsBytea : Bool
    replayMayRewritePriorEvidence : Bool
    persistenceCreatesSemanticAuthority : Bool
    semanticPromotion : Bool

open BinaryWorldWireParity public

canonicalBinaryWorldWireParity : BinaryWorldWireParity
canonicalBinaryWorldWireParity =
  binaryWorldWireParity
    true true true true
    true true true true
    true true true false
    false false false false
    true true
    false false false

------------------------------------------------------------------------
-- Production firewalls.
------------------------------------------------------------------------

data JsonWorldTransport : Set where
data JsonWorldPayload : Set where
data PostgresJsonbWorldPayload : Set where
data RegexWorldParser : Set where
data WholeStreamBufferRequired : Set where
data BinaryPersistenceCreatesSemanticAuthority : Set where
data BinaryPersistencePromotesTruth : Set where
data BinaryReplayRewritesPriorEvidence : Set where

jsonWorldTransportForbidden : JsonWorldTransport → ⊥
jsonWorldTransportForbidden ()

jsonWorldPayloadForbidden : JsonWorldPayload → ⊥
jsonWorldPayloadForbidden ()

postgresJsonbWorldPayloadForbidden : PostgresJsonbWorldPayload → ⊥
postgresJsonbWorldPayloadForbidden ()

regexWorldParserForbidden : RegexWorldParser → ⊥
regexWorldParserForbidden ()

streamingWireDoesNotRequireWholeBuffer : WholeStreamBufferRequired → ⊥
streamingWireDoesNotRequireWholeBuffer ()

binaryPersistenceDoesNotCreateSemanticAuthority : BinaryPersistenceCreatesSemanticAuthority → ⊥
binaryPersistenceDoesNotCreateSemanticAuthority ()

binaryPersistenceDoesNotPromoteTruth : BinaryPersistencePromotesTruth → ⊥
binaryPersistenceDoesNotPromoteTruth ()

binaryReplayDoesNotRewritePriorEvidence : BinaryReplayRewritesPriorEvidence → ⊥
binaryReplayDoesNotRewritePriorEvidence ()
