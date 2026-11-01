module DASHI.Interop.SLRBinaryWorldWireParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Exact cross-kernel contract for the production world-store wire ABI.
------------------------------------------------------------------------

data WorldWireKind : Set where
  sourceManifestation : WorldWireKind
  pnfCandidate : WorldWireKind
  worldAtom : WorldWireKind
  gap : WorldWireKind
  obligation : WorldWireKind
  routeAction : WorldWireKind
  iteration : WorldWireKind
  payment : WorldWireKind
  review : WorldWireKind

worldWireKindTag : WorldWireKind → Nat
worldWireKindTag sourceManifestation = 1
worldWireKindTag pnfCandidate = 2
worldWireKindTag worldAtom = 3
worldWireKindTag gap = 4
worldWireKindTag obligation = 5
worldWireKindTag routeAction = 6
worldWireKindTag iteration = 7
worldWireKindTag payment = 8
worldWireKindTag review = 9

wireVersion : Nat
wireVersion = 1

record BinaryWorldWireParity : Set where
  constructor binaryWorldWireParity
  field
    magicIsSLRW : Bool
    versionIsOne : Bool
    littleEndianHeader : Bool
    kindTagMappingExact : Bool
    paymentKindTagIsEight : Bool
    reviewKindTagIsNine : Bool
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
    frontierUsesFallibleRowIteration : Bool
    frontierEmitsFramesIncrementally : Bool
    typedRunnerRequiresBinaryWire : Bool
    legacyJsonExecutablePathAvailable : Bool
    textReceiptRegexValidationUsed : Bool
    replayMayRewritePriorEvidence : Bool
    persistenceCreatesSemanticAuthority : Bool
    semanticPromotion : Bool

open BinaryWorldWireParity public

canonicalBinaryWorldWireParity : BinaryWorldWireParity
canonicalBinaryWorldWireParity =
  binaryWorldWireParity
    true true true true true true
    true true true true
    true true true false
    false false false false
    true true
    true true true false false
    false false false

------------------------------------------------------------------------
-- Production firewalls.
------------------------------------------------------------------------

data JsonWorldTransport : Set where
data JsonWorldPayload : Set where
data PostgresJsonbWorldPayload : Set where
data RegexWorldParser : Set where
data WholeStreamBufferRequired : Set where
data LegacyJsonExecutablePath : Set where
data TextReceiptRegexValidation : Set where
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

legacyJsonExecutablePathForbidden : LegacyJsonExecutablePath → ⊥
legacyJsonExecutablePathForbidden ()

textReceiptRegexValidationForbidden : TextReceiptRegexValidation → ⊥
textReceiptRegexValidationForbidden ()

binaryPersistenceDoesNotCreateSemanticAuthority : BinaryPersistenceCreatesSemanticAuthority → ⊥
binaryPersistenceDoesNotCreateSemanticAuthority ()

binaryPersistenceDoesNotPromoteTruth : BinaryPersistencePromotesTruth → ⊥
binaryPersistenceDoesNotPromoteTruth ()

binaryReplayDoesNotRewritePriorEvidence : BinaryReplayRewritesPriorEvidence → ⊥
binaryReplayDoesNotRewritePriorEvidence ()
