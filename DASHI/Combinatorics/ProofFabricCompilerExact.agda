module DASHI.Combinatorics.ProofFabricCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Codec.VerifiedFiniteTritCoder as Codec
import DASHI.Combinatorics.TextileNFibreCalculusExact as T
import DASHI.Combinatorics.TextileFibreHyperfabricExact as TextileHyper
import DASHI.Reasoning.TypedHyperfabricCore as Hyper
import DASHI.Culture.CulturalProvenanceBoundaryCore as Cultural
import DASHI.Culture.KimmererBraidingAcknowledgement as Kimmerer

------------------------------------------------------------------------
-- PROOF <-> FABRIC COMPILER
--
-- A proof formalism supplies only an exact serialization to a trit stream.
-- DASHI then reuses the existing verified finite trit coder and maps the
-- resulting two-bit words into physically interpretable over/under weave tiles.
--
-- This deliberately does NOT say that proof semantics are intrinsically
-- ternary, nor that any culturally situated textile semantics are replaceable
-- by this encoding.  Trits are the neutral machine/interchange layer here.
------------------------------------------------------------------------

record ProofTritCodec (Proof : Set) : Set₁ where
  constructor proof-trit-codec
  field
    serializeProof : Proof → List Trit
    parseProof : List Trit → Maybe Proof
    parseSerializeExact :
      (proof : Proof) →
      parseProof (serializeProof proof) ≡ just proof

open ProofTritCodec public

------------------------------------------------------------------------
-- Four physical two-cell weave tiles.  The first three are valid trit
-- codewords inherited from VerifiedFiniteTritCoder; tile11 is deliberately
-- reserved/malformed, giving the textile alphabet an error-detection surface.
------------------------------------------------------------------------

data ProofWeaveTile : Set where
  tile00 tile01 tile10 tile11 : ProofWeaveTile

wordToTile : Codec.Word2 → ProofWeaveTile
wordToTile Codec.word00 = tile00
wordToTile Codec.word01 = tile01
wordToTile Codec.word10 = tile10
wordToTile Codec.word11 = tile11

tileToWord : ProofWeaveTile → Codec.Word2
tileToWord tile00 = Codec.word00
tileToWord tile01 = Codec.word01
tileToWord tile10 = Codec.word10
tileToWord tile11 = Codec.word11

tileWordRoundtrip : (word : Codec.Word2) → tileToWord (wordToTile word) ≡ word
tileWordRoundtrip Codec.word00 = refl
tileWordRoundtrip Codec.word01 = refl
tileWordRoundtrip Codec.word10 = refl
tileWordRoundtrip Codec.word11 = refl

wordTileRoundtrip : (tile : ProofWeaveTile) → wordToTile (tileToWord tile) ≡ tile
wordTileRoundtrip tile00 = refl
wordTileRoundtrip tile01 = refl
wordTileRoundtrip tile10 = refl
wordTileRoundtrip tile11 = refl

tritToTile : Trit → ProofWeaveTile
tritToTile t = wordToTile (Codec.encodeTrit t)

tileToTrit : ProofWeaveTile → Maybe Trit
tileToTrit tile = Codec.decodeWord (tileToWord tile)

tritTileRoundtrip : (t : Trit) → tileToTrit (tritToTile t) ≡ just t
tritTileRoundtrip neg = refl
tritTileRoundtrip zer = refl
tritTileRoundtrip pos = refl

reservedTileRejected : tileToTrit tile11 ≡ nothing
reservedTileRejected = refl

------------------------------------------------------------------------
-- Literal loom interpretation.
--
-- Each tile is a one-pick, two-warp cell.  A zero bit is represented by weft
-- over warp (warp-under-weft); a one bit by warp over weft.  Concatenating
-- tiles into a wider/taller draft is manufacturing/layout work and does not
-- change the verified symbol semantics.
------------------------------------------------------------------------

tilePasses : ProofWeaveTile → List T.WeavePass
tilePasses tile00 =
  T.warpUnderWeft 0 0 ∷ T.warpUnderWeft 1 0 ∷ []
tilePasses tile01 =
  T.warpUnderWeft 0 0 ∷ T.warpOverWeft 1 0 ∷ []
tilePasses tile10 =
  T.warpOverWeft 0 0 ∷ T.warpUnderWeft 1 0 ∷ []
tilePasses tile11 =
  T.warpOverWeft 0 0 ∷ T.warpOverWeft 1 0 ∷ []

compileTritStream : List Trit → List ProofWeaveTile
compileTritStream [] = []
compileTritStream (t ∷ ts) = tritToTile t ∷ compileTritStream ts

readTileStream : List ProofWeaveTile → List (Maybe Trit)
readTileStream [] = []
readTileStream (tile ∷ tiles) = tileToTrit tile ∷ readTileStream tiles

justTritStream : List Trit → List (Maybe Trit)
justTritStream [] = []
justTritStream (t ∷ ts) = just t ∷ justTritStream ts

readCompiledTritStream :
  (stream : List Trit) →
  readTileStream (compileTritStream stream) ≡ justTritStream stream
readCompiledTritStream [] = refl
readCompiledTritStream (neg ∷ stream) rewrite readCompiledTritStream stream = refl
readCompiledTritStream (zer ∷ stream) rewrite readCompiledTritStream stream = refl
readCompiledTritStream (pos ∷ stream) rewrite readCompiledTritStream stream = refl

------------------------------------------------------------------------
-- Proof artefact: proof, exact serialization, and manufacturable tile stream
-- are kept together.  The proof does not become true because it is woven;
-- truth/derivability is owned by the source proof system.  The textile object
-- is a faithful representation of the supplied serialization.
------------------------------------------------------------------------

record ProofFabricArtifact (Proof : Set) : Set where
  constructor proof-fabric-artifact
  field
    sourceProof : Proof
    serializedProof : List Trit
    weaveTiles : List ProofWeaveTile
    tilesMatchSerialization : weaveTiles ≡ compileTritStream serializedProof

open ProofFabricArtifact public

compileProofToFabric :
  {Proof : Set} →
  (codec : ProofTritCodec Proof) →
  Proof →
  ProofFabricArtifact Proof
compileProofToFabric codec proof =
  proof-fabric-artifact
    proof
    (serializeProof codec proof)
    (compileTritStream (serializeProof codec proof))
    refl

compiledArtifactParsesToSource :
  {Proof : Set} →
  (codec : ProofTritCodec Proof) →
  (proof : Proof) →
  parseProof codec
    (serializedProof (compileProofToFabric codec proof))
  ≡ just proof
compiledArtifactParsesToSource codec proof =
  parseSerializeExact codec proof

compiledArtifactTilesReadExactly :
  {Proof : Set} →
  (codec : ProofTritCodec Proof) →
  (proof : Proof) →
  readTileStream (weaveTiles (compileProofToFabric codec proof))
  ≡ justTritStream (serializeProof codec proof)
compiledArtifactTilesReadExactly codec proof =
  readCompiledTritStream (serializeProof codec proof)

------------------------------------------------------------------------
-- Same physical encoding lifted into the actual textile hyperfabric.
------------------------------------------------------------------------

tileHyperedges : ProofWeaveTile → List (TextileHyper.TextileEdge 2)
tileHyperedges tile00 =
  TextileHyper.weaveInterlaceEdge 0 0 T.underCrossing ∷
  TextileHyper.weaveInterlaceEdge 1 0 T.underCrossing ∷ []
tileHyperedges tile01 =
  TextileHyper.weaveInterlaceEdge 0 0 T.underCrossing ∷
  TextileHyper.weaveInterlaceEdge 1 0 T.overCrossing ∷ []
tileHyperedges tile10 =
  TextileHyper.weaveInterlaceEdge 0 0 T.overCrossing ∷
  TextileHyper.weaveInterlaceEdge 1 0 T.underCrossing ∷ []
tileHyperedges tile11 =
  TextileHyper.weaveInterlaceEdge 0 0 T.overCrossing ∷
  TextileHyper.weaveInterlaceEdge 1 0 T.overCrossing ∷ []

tilesToHyperedges :
  List ProofWeaveTile →
  List (TextileHyper.TextileEdge 2)
tilesToHyperedges [] = []
tilesToHyperedges (tile ∷ tiles) =
  tileHyperedges tile ++ tilesToHyperedges tiles

proofFabricHyperfabricTrace :
  List ProofWeaveTile →
  Hyper.HyperfabricTrace (TextileHyper.TextileEdge 2)
proofFabricHyperfabricTrace tiles = record
  { visitedEdges = tilesToHyperedges tiles
  ; traceReceipts =
      "verified trit code rendered as over/under textile hyperedges" ∷ []
  ; traceLabel = "proof-fabric hyperfabric trace"
  }

compiledProofHyperfabricTrace :
  {Proof : Set} →
  (codec : ProofTritCodec Proof) →
  Proof →
  Hyper.HyperfabricTrace (TextileHyper.TextileEdge 2)
compiledProofHyperfabricTrace codec proof =
  proofFabricHyperfabricTrace
    (weaveTiles (compileProofToFabric codec proof))

------------------------------------------------------------------------
-- Braided carrier backend.
--
-- The same four two-bit words can be rendered as two consecutive crossings of
-- one actual three-fibre generator.  This yields a hand-braidable proof strip
-- while retaining the same codec alphabet as the woven representation.
------------------------------------------------------------------------

sigma0With : T.CrossingOrientation → T.AdjacentCrossing 3
sigma0With orientation = T.sigma 0 orientation T.threeHasSigma0

bitCrossing : Codec.Bit → T.AdjacentCrossing 3
bitCrossing Codec.bit0 = sigma0With T.underCrossing
bitCrossing Codec.bit1 = sigma0With T.overCrossing

wordToBraidTile : Codec.Word2 → T.BraidWord 3
wordToBraidTile Codec.word00 =
  bitCrossing Codec.bit0 ∷ bitCrossing Codec.bit0 ∷ []
wordToBraidTile Codec.word01 =
  bitCrossing Codec.bit0 ∷ bitCrossing Codec.bit1 ∷ []
wordToBraidTile Codec.word10 =
  bitCrossing Codec.bit1 ∷ bitCrossing Codec.bit0 ∷ []
wordToBraidTile Codec.word11 =
  bitCrossing Codec.bit1 ∷ bitCrossing Codec.bit1 ∷ []

tritToBraidTile : Trit → T.BraidWord 3
tritToBraidTile t = wordToBraidTile (Codec.encodeTrit t)

compileTritStreamToBraid : List Trit → T.BraidWord 3
compileTritStreamToBraid [] = []
compileTritStreamToBraid (t ∷ ts) =
  tritToBraidTile t ++ compileTritStreamToBraid ts

compileProofToBraid :
  {Proof : Set} →
  ProofTritCodec Proof →
  Proof →
  T.BraidWord 3
compileProofToBraid codec proof =
  compileTritStreamToBraid (serializeProof codec proof)

------------------------------------------------------------------------
-- Embodied / portable carriers.
--
-- These are media choices for a code, not claims that all media or historical
-- practices have interchangeable meanings.
------------------------------------------------------------------------

data MaterialProofCarrier : Set where
  wovenCloth : MaterialProofCarrier
  braidedCord : MaterialProofCarrier
  knittedFabric : MaterialProofCarrier
  crochetedFabric : MaterialProofCarrier
  hairBraidCarrier : MaterialProofCarrier
  bodyMarkingCarrier : MaterialProofCarrier

record MaterialProofPlan : Set where
  constructor material-proof-plan
  field
    carrier : MaterialProofCarrier
    encodedTrits : List Trit
    codeIsDashiDefined : Bool
    culturalMeaningClaimed : Bool
    historicalClaimCertified : Bool
    provenanceNote : String

open MaterialProofPlan public

canonicalWovenProofPlan : List Trit → MaterialProofPlan
canonicalWovenProofPlan stream =
  material-proof-plan
    wovenCloth stream true false false
    "DASHI-defined proof code; no external cultural semantics claimed"

canonicalBraidedProofPlan : List Trit → MaterialProofPlan
canonicalBraidedProofPlan stream =
  material-proof-plan
    braidedCord stream true false false
    "DASHI-defined proof code rendered as ordered braid crossings"

------------------------------------------------------------------------
-- Cultural / historical authority boundary.
--
-- Existing repository provenance governance is imported literally.  The
-- Kimmerer acknowledgement remains the provenance owner for the inspiration
-- that distinct knowledge strands may be braided without forced fusion.
--
-- Historical claims about route/map encoding in hair or other embodied media
-- require source-specific historical evidence before attribution.  A fictional
-- body-carried escape map may motivate the carrier idea but is not evidence for
-- a historical practice.  No restricted/community-owned pattern is copied by
-- default by this compiler.
------------------------------------------------------------------------

record ProofFabricCulturalBoundary : Set where
  constructor proof-fabric-cultural-boundary
  field
    culturalProvenance : Cultural.CulturalProvenanceBoundary
    kimmererAcknowledgement : Kimmerer.KimmererBraidingAcknowledgement

    proofEncodingEqualsIndigenousKnowledge : Bool
    proofEncodingEqualsIndigenousKnowledgeIsFalse :
      proofEncodingEqualsIndigenousKnowledge ≡ false

    historicalHairMapClaimTreatedAsEstablishedByAnalogy : Bool
    historicalHairMapClaimTreatedAsEstablishedByAnalogyIsFalse :
      historicalHairMapClaimTreatedAsEstablishedByAnalogy ≡ false

    fictionalBodyMapCountsAsHistoricalEvidence : Bool
    fictionalBodyMapCountsAsHistoricalEvidenceIsFalse :
      fictionalBodyMapCountsAsHistoricalEvidence ≡ false

    restrictedCulturalPatternCopiedByDefault : Bool
    restrictedCulturalPatternCopiedByDefaultIsFalse :
      restrictedCulturalPatternCopiedByDefault ≡ false

    communityPermissionMayBeRequired : Bool
    communityPermissionMayBeRequiredIsTrue :
      communityPermissionMayBeRequired ≡ true

    physicalFabricCanFaithfullyCarryDashiProofCode : Bool
    physicalFabricCanFaithfullyCarryDashiProofCodeIsTrue :
      physicalFabricCanFaithfullyCarryDashiProofCode ≡ true

canonicalProofFabricCulturalBoundary : ProofFabricCulturalBoundary
canonicalProofFabricCulturalBoundary =
  proof-fabric-cultural-boundary
    Cultural.canonicalCulturalProvenanceBoundary
    Kimmerer.canonicalKimmererBraidingAcknowledgement
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
