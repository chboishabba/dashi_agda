module DASHI.ComputerScience.HelloWorldJacquardExact where

open import DASHI.Core.Prelude
open import Data.Maybe using (Maybe; just; nothing)

import DASHI.ComputerScience.HelloWorldFibreExact as Hello
import DASHI.Algebra.Trit as Trit
import DASHI.Combinatorics.ProofFabricCompilerExact as ProofFabric
import DASHI.Computation.JacquardProofVisibleSurfaceExact as Visible
import DASHI.Computation.JacquardOperationalSemanticsExact as Jacquard

------------------------------------------------------------------------
-- HELLO WORLD -> TRIT CODE -> JACQUARD PROGRAM -> VISIBLE CLOTH
--
-- This is not a new textile compiler.  It supplies only a Hello-World codec
-- instance to the existing ProofFabric/Jacquard pipeline.  The existing owner
-- remains authoritative for trit-to-tile encoding, Jacquard compilation,
-- execution, visible-face projection, and visible readback.
--
-- One semantic helloWorld token is encoded by the neutral trit marker
--   neg, zer, pos
-- and lists of messages concatenate that marker.  This is a DASHI-defined
-- machine code, not a claim about cultural textile meaning.
------------------------------------------------------------------------

serializeHelloOutput : Hello.Output → List Trit.Trit
serializeHelloOutput [] = []
serializeHelloOutput (Hello.helloWorld ∷ output) =
  Trit.neg ∷ Trit.zer ∷ Trit.pos ∷ serializeHelloOutput output

parseHelloOutput : List Trit.Trit → Maybe Hello.Output
parseHelloOutput [] = just []
parseHelloOutput (Trit.neg ∷ Trit.zer ∷ Trit.pos ∷ stream)
  with parseHelloOutput stream
... | nothing = nothing
... | just output = just (Hello.helloWorld ∷ output)
parseHelloOutput stream = nothing

parseSerializeHelloExact :
  (output : Hello.Output) →
  parseHelloOutput (serializeHelloOutput output) ≡ just output
parseSerializeHelloExact [] = refl
parseSerializeHelloExact (Hello.helloWorld ∷ output)
  rewrite parseSerializeHelloExact output = refl

helloWorldTritCodec : ProofFabric.ProofTritCodec Hello.Output
helloWorldTritCodec =
  ProofFabric.proof-trit-codec
    serializeHelloOutput
    parseHelloOutput
    parseSerializeHelloExact

helloWorldTritStream : List Trit.Trit
helloWorldTritStream = serializeHelloOutput Hello.helloWorldSpec

helloWorldTritStreamExact :
  helloWorldTritStream ≡ Trit.neg ∷ Trit.zer ∷ Trit.pos ∷ []
helloWorldTritStreamExact = refl

helloWorldTritRoundtrip :
  parseHelloOutput helloWorldTritStream ≡ just Hello.helloWorldSpec
helloWorldTritRoundtrip = refl

------------------------------------------------------------------------
-- Canonical proof-fabric/Jacquard realization.
------------------------------------------------------------------------

helloWorldTiles : List ProofFabric.ProofWeaveTile
helloWorldTiles =
  ProofFabric.compileTritStream helloWorldTritStream

helloWorldJacquardProgram : Jacquard.JacquardProgram 2
helloWorldJacquardProgram =
  Visible.proofToJacquard helloWorldTritCodec Hello.helloWorldSpec

helloWorldVisiblePattern : Visible.VisiblePattern2
helloWorldVisiblePattern =
  Visible.proofVisiblePattern helloWorldTritCodec Hello.helloWorldSpec

helloWorldJacquardWitness : Visible.JacquardProofFabricWitness Hello.Output
helloWorldJacquardWitness =
  Visible.compileProofToJacquardWitness
    helloWorldTritCodec
    Hello.helloWorldSpec

helloWorldJacquardProgramUsesCanonicalCompiler :
  Visible.program helloWorldJacquardWitness ≡ helloWorldJacquardProgram
helloWorldJacquardProgramUsesCanonicalCompiler = refl

helloWorldVisiblePatternUsesCanonicalProjection :
  Visible.visiblePattern helloWorldJacquardWitness
  ≡ Visible.visiblePatternOfTiles helloWorldTiles
helloWorldVisiblePatternUsesCanonicalProjection = refl

------------------------------------------------------------------------
-- Visible cloth readback.
--
-- The visible face recovers the exact trit serialization.  Separately, the
-- Hello codec proves that serialization parses back to the semantic message.
-- Keeping these as two receipts avoids pretending visible cloth itself creates
-- or proves the source semantics.
------------------------------------------------------------------------

helloWorldVisibleReadbackExact :
  Visible.readVisiblePattern helloWorldVisiblePattern
  ≡ ProofFabric.justTritStream helloWorldTritStream
helloWorldVisibleReadbackExact =
  Visible.proofVisibleCodeReadable
    helloWorldTritCodec
    Hello.helloWorldSpec

helloWorldSerializedSourceParsesExactly :
  ProofFabric.parseProof helloWorldTritCodec helloWorldTritStream
  ≡ just Hello.helloWorldSpec
helloWorldSerializedSourceParsesExactly =
  ProofFabric.parseSerializeExact
    helloWorldTritCodec
    Hello.helloWorldSpec

------------------------------------------------------------------------
-- Exact three-tile visible pattern for the single semantic token.
------------------------------------------------------------------------

helloWorldTilesExact :
  helloWorldTiles
  ≡ ProofFabric.tritToTile Trit.neg
    ∷ ProofFabric.tritToTile Trit.zer
    ∷ ProofFabric.tritToTile Trit.pos
    ∷ []
helloWorldTilesExact = refl

helloWorldVisibleCompilationExact :
  Visible.visibleProgram2 helloWorldJacquardProgram
  ≡ Visible.visiblePatternOfTiles helloWorldTiles
helloWorldVisibleCompilationExact =
  Visible.jacquardTilesProduceVisiblePattern helloWorldTiles

record HelloWorldJacquardReceipt : Set where
  constructor helloWorldJacquardReceipt
  field
    source : Hello.Output
    serialized : List Trit.Trit
    tiles : List ProofFabric.ProofWeaveTile
    program : Jacquard.JacquardProgram 2
    visible : Visible.VisiblePattern2
    sourceExact : source ≡ Hello.helloWorldSpec
    serializationExact : serialized ≡ helloWorldTritStream
    tilesExact : tiles ≡ helloWorldTiles
    visibleReadbackExact :
      Visible.readVisiblePattern visible
      ≡ ProofFabric.justTritStream serialized
    sourceParsesExact :
      ProofFabric.parseProof helloWorldTritCodec serialized ≡ just source

canonicalHelloWorldJacquardReceipt : HelloWorldJacquardReceipt
canonicalHelloWorldJacquardReceipt =
  helloWorldJacquardReceipt
    Hello.helloWorldSpec
    helloWorldTritStream
    helloWorldTiles
    helloWorldJacquardProgram
    helloWorldVisiblePattern
    refl
    refl
    refl
    helloWorldVisibleReadbackExact
    helloWorldSerializedSourceParsesExactly

record HelloWorldJacquardBoundary : Set where
  constructor helloWorldJacquardBoundary
  field
    reusesCanonicalJacquardCompiler : Bool
    visibleFaceRecoversExactSerialization : Bool
    serializationParsesToSemanticSource : Bool
    wovenVisibilityCreatesSemanticTruth : Bool
    textileEncodingClaimsCulturalMeaning : Bool
    materialMechanicsClaimed : Bool

canonicalHelloWorldJacquardBoundary : HelloWorldJacquardBoundary
canonicalHelloWorldJacquardBoundary =
  helloWorldJacquardBoundary true true true false false false
