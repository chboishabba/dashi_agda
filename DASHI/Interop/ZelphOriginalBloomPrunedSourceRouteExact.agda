module DASHI.Interop.ZelphOriginalBloomPrunedSourceRouteExact where

-- Original Zelph A2-B mathematical implication:
--   source-equal all-chunk membership extraction with no Bloom false
--   negatives + exact C++ native candidate-row replay gives SAME source
--   edge relation, preserving multivalued adjacency and any duplicate keys.
--
-- The physical HTTP206 hashes, original Cap'n Proto decoder correctness,
-- source-complete Chunk enumeration, and actual Bloom membership
-- implementation MUST be supplied by the external witness pipeline.
-- This theorem neither fabricates those premises nor proves the concrete
-- splitmix64 C++/Python hash implementation correct. Absence from a
-- PARTIALLY observed original section is not a global negative.

open import Data.Empty using (⊥)

record _⇔_ (A B : Set) : Set where
  constructor both-directions
  field
    forward : A → B
    backward : B → A
open _⇔_ public

-- The Chunk type must denote the complete original left OR right source
-- section's indexed chunk domain, not only the downloaded selected shards.
-- A concrete finite index/manifest cover is the independent physical input.
data OriginalEdge
  {Chunk Node : Set}
  (OriginalRow : Chunk → Node → Node → Set)
  (src dst : Node) : Set where
  original-edge :
    (chunk : Chunk) →
    OriginalRow chunk src dst →
    OriginalEdge OriginalRow src dst

-- A Bloom-positive key does not prove an edge. The edge requires a separate
-- actual original-source native decoded row from that candidate chunk.
data CandidateReplayedEdge
  {Chunk Node : Set}
  (MayContain : Chunk → Node → Set)
  (NativeRow : Chunk → Node → Node → Set)
  (src dst : Node) : Set where
  candidate-edge :
    (chunk : Chunk) →
    MayContain chunk src →
    NativeRow chunk src dst →
    CandidateReplayedEdge MayContain NativeRow src dst

-- Under the real original-source byte and decoder premises,
-- Bloom's NO-FALSE-NEGATIVE direction allows every original edge to be
-- found among the candidate chunks, and exact native row replay recovers it.
originalEdgeToBloomCandidate :
  {Chunk Node : Set}
  {Verified : Chunk → Set}
  {MayContain : Chunk → Node → Set}
  {OriginalRow NativeRow : Chunk → Node → Node → Set} →
  (allOriginalChunksVerified : (c : Chunk) → Verified c) →
  (noFalseNegative :
    (c : Chunk) (src dst : Node) →
    Verified c → OriginalRow c src dst → MayContain c src) →
  (candidateNativeExact :
    (c : Chunk) (src dst : Node) →
    Verified c → MayContain c src →
    OriginalRow c src dst ⇔ NativeRow c src dst) →
  {src dst : Node} →
  OriginalEdge OriginalRow src dst →
  CandidateReplayedEdge MayContain NativeRow src dst
originalEdgeToBloomCandidate all noFalse exact {src} {dst}
  (original-edge c sourceRow) =
  candidate-edge c possible (forward (exact c src dst (all c) possible) sourceRow)
  where
    possible = noFalse c src dst (all c) sourceRow

-- An exact native candidate row is not merely a Bloom false positive:
-- it really belongs to the original packed section.
bloomCandidateToOriginalEdge :
  {Chunk Node : Set}
  {Verified : Chunk → Set}
  {MayContain : Chunk → Node → Set}
  {OriginalRow NativeRow : Chunk → Node → Node → Set} →
  (allOriginalChunksVerified : (c : Chunk) → Verified c) →
  (noFalseNegative :
    (c : Chunk) (src dst : Node) →
    Verified c → OriginalRow c src dst → MayContain c src) →
  (candidateNativeExact :
    (c : Chunk) (src dst : Node) →
    Verified c → MayContain c src →
    OriginalRow c src dst ⇔ NativeRow c src dst) →
  {src dst : Node} →
  CandidateReplayedEdge MayContain NativeRow src dst →
  OriginalEdge OriginalRow src dst
bloomCandidateToOriginalEdge all noFalse exact {src} {dst}
  (candidate-edge c possible decodedRow) =
  original-edge c (backward (exact c src dst (all c) possible) decodedRow)

-- This is the source-scoped extensional adjacency weld. It does NOT
-- infer source coverage from the presence of 3 selected adjacency shards;
-- the universally quantified allOriginalChunksVerified proof is mandatory.
originalEdgesEquivalentToBloomReplayedEdges :
  {Chunk Node : Set}
  {Verified : Chunk → Set}
  {MayContain : Chunk → Node → Set}
  {OriginalRow NativeRow : Chunk → Node → Node → Set} →
  (allOriginalChunksVerified : (c : Chunk) → Verified c) →
  (noFalseNegative :
    (c : Chunk) (src dst : Node) →
    Verified c → OriginalRow c src dst → MayContain c src) →
  (candidateNativeExact :
    (c : Chunk) (src dst : Node) →
    Verified c → MayContain c src →
    OriginalRow c src dst ⇔ NativeRow c src dst) →
  (src dst : Node) →
  OriginalEdge OriginalRow src dst
  ⇔ CandidateReplayedEdge MayContain NativeRow src dst
originalEdgesEquivalentToBloomReplayedEdges all noFalse exact src dst =
  both-directions
    (originalEdgeToBloomCandidate all noFalse exact)
    (bloomCandidateToOriginalEdge all noFalse exact)

-- One-sided negative control: if the VERIFIED original chunk's filter is
-- definitely absent for a node, a row in THAT chunk is impossible.
-- This cannot be applied to unobserved chunks without a Verified witness.
bloomNegativeExcludesSourceRow :
  {Chunk Node : Set}
  {Verified : Chunk → Set}
  {MayContain : Chunk → Node → Set}
  {OriginalRow : Chunk → Node → Node → Set} →
  (noFalseNegative :
    (c : Chunk) (src dst : Node) →
    Verified c → OriginalRow c src dst → MayContain c src) →
  {c : Chunk} {src dst : Node} →
  Verified c →
  (MayContain c src → ⊥) →
  OriginalRow c src dst →
  ⊥
bloomNegativeExcludesSourceRow noFalse {c} {src} {dst}
  verified notPossible originalRow =
  notPossible (noFalse c src dst verified originalRow)
