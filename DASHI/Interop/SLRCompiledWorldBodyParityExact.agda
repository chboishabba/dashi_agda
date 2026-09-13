module DASHI.Interop.SLRCompiledWorldBodyParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRBinaryWorldWireParityExact as Wire
import DASHI.Interop.SLRSpacyObservationWorldCompilerParityExact as Compiler

------------------------------------------------------------------------
-- Kind-owned SLRW body layouts emitted by crates/sl-world-compiler.
-- The outer frame is SLRW v1; these are the exact binary bodies carried by
-- sourceManifestation / pnfCandidate / worldAtom / iteration records.
------------------------------------------------------------------------

data CompiledBodyKind : Set where
  sourceBody : CompiledBodyKind
  pnfBody : CompiledBodyKind
  atomBody : CompiledBodyKind
  iterationBody : CompiledBodyKind

bodyMagicTag : CompiledBodyKind → Nat
bodyMagicTag sourceBody = 1       -- bytes "SRC1"
bodyMagicTag pnfBody = 2          -- bytes "PNF1"
bodyMagicTag atomBody = 3         -- bytes "ATM1"
bodyMagicTag iterationBody = 4    -- bytes "ITR1"

record SourceBodyLayout : Set where
  constructor sourceBodyLayout
  field
    magicIsSRC1 : Bool
    qidIsLengthPrefixedUtf8 : Bool
    languageIsLengthPrefixedUtf8 : Bool
    revisionRefIsLengthPrefixedUtf8 : Bool
    sourceSha256IsExactly32Bytes : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool

canonicalSourceBodyLayout : SourceBodyLayout
canonicalSourceBodyLayout = sourceBodyLayout true true true true true true true

record PNFBodyLayout : Set where
  constructor pnfBodyLayout
  field
    magicIsPNF1 : Bool
    fragmentTagIsU8 : Bool
    dependencyShapeTagIsU8 : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool
    sentenceIdIsU64LittleEndian : Bool
    localOrdinalIsU32LittleEndian : Bool
    headOrdinalIsU32LittleEndian : Bool
    startCharIsU32LittleEndian : Bool
    endCharIsU32LittleEndian : Bool
    dependentOrthIsLengthPrefixedUtf8 : Bool
    dependentLemmaIsLengthPrefixedUtf8 : Bool
    headOrthIsLengthPrefixedUtf8 : Bool
    headLemmaIsLengthPrefixedUtf8 : Bool

canonicalPNFBodyLayout : PNFBodyLayout
canonicalPNFBodyLayout =
  pnfBodyLayout true true true true true true true true true true true true true true

record AtomBodyLayout : Set where
  constructor atomBodyLayout
  field
    magicIsATM1 : Bool
    sourceCandidateIdIsLengthPrefixedUtf8 : Bool
    embeddedPNFLengthIsU32LittleEndian : Bool
    embeddedBodyIsExactPNFBody : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool

canonicalAtomBodyLayout : AtomBodyLayout
canonicalAtomBodyLayout = atomBodyLayout true true true true true true

record IterationBodyLayout : Set where
  constructor iterationBodyLayout
  field
    magicIsITR1 : Bool
    manifestationCountIsU64LittleEndian : Bool
    pnfCandidateCountIsU64LittleEndian : Bool
    worldAtomCountIsU64LittleEndian : Bool
    unresolvedDependencyCountIsU64LittleEndian : Bool
    candidateOnlyByteIsOne : Bool
    semanticPromotionByteIsZero : Bool

canonicalIterationBodyLayout : IterationBodyLayout
canonicalIterationBodyLayout = iterationBodyLayout true true true true true true true

record CompiledBodyParity : Set where
  constructor compiledBodyParity
  field
    outerWireVersion : Nat
    observationCompilerVersion : Nat
    sourceLayoutExact : Bool
    pnfLayoutExact : Bool
    atomLayoutExact : Bool
    iterationLayoutExact : Bool
    jsonBodyAllowed : Bool
    textualSentinelParsingAllowed : Bool
    semanticPromotion : Bool

canonicalCompiledBodyParity : CompiledBodyParity
canonicalCompiledBodyParity =
  compiledBodyParity
    Wire.wireVersion
    Compiler.observationWireVersion
    true true true true
    false false false

data JsonCompiledWorldBody : Set where
data TextSentinelCompiledWorldBody : Set where
data CompiledWorldBodyTruthPromotion : Set where

jsonCompiledWorldBodyForbidden : JsonCompiledWorldBody → ⊥
jsonCompiledWorldBodyForbidden ()

textSentinelCompiledWorldBodyForbidden : TextSentinelCompiledWorldBody → ⊥
textSentinelCompiledWorldBodyForbidden ()

compiledWorldBodyDoesNotPromoteTruth : CompiledWorldBodyTruthPromotion → ⊥
compiledWorldBodyDoesNotPromoteTruth ()
