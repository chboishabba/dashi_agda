module DASHI.Mathematics.Complexity.Karp21OriginalGammaGraphWordFieldsReplayExact where

------------------------------------------------------------------------
-- N21/E20: exact replay of every original weighted graph word FIELD.
--
-- Actual existing wire encoder:
--   encodeGraphWord (n,g) =
--     gamma(n) ++ gamma(length(edges g)) ++
--     encodeEdgeWords(edges g) ++ gamma(abs(threshold g)).
--
-- Actual decoder owners:
--   Gamma.readGamma (vertex/edge counts and magnitude threshold)
--   Graph.readRawEdges (ordered signed edge triples).
--
-- All four field reads are proved on those exact original functions,
-- preserving their byte suffix. This is not a replacement parser
-- and does not claim the later strict positive-threshold, lexicographic
-- Fin reconstruction, 2m guard or machine-time checks have succeeded.
--
-- Credits: Elias gamma; Richard Karp 1972; DASHI original signed
-- graph word and raw edge-list source owners. Agda kernel unrun.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _++_; length)
open import Data.Nat.Base using (_≤_)
open import Data.Maybe.Base using (just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (∣_∣)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as Instance
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as EncodeGamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Numeric
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21EncodedGraphSparseBitBoundExact as Size

-- Exact tail of the serialized gamma vertex-count header. The source
-- graph may have an enormous vertex count and zero listed edges.
graphWordAfterVertexCount :
  (instance : Instance.GraphInstance) → Word.BitWord
graphWordAfterVertexCount (n , graph) =
  EncodeGamma.encodeGammaNat (length (Cut.edges graph)) ++
  Encode.encodeEdgeWords (Cut.edges graph) ++
  EncodeGamma.encodeGammaNat (∣ Cut.threshold graph ∣)

graphWordAfterEdgeCount :
  (instance : Instance.GraphInstance) → Word.BitWord
graphWordAfterEdgeCount (n , graph) =
  Encode.encodeEdgeWords (Cut.edges graph) ++
  EncodeGamma.encodeGammaNat (∣ Cut.threshold graph ∣)

graphWordThresholdBits :
  (instance : Instance.GraphInstance) → Word.BitWord
graphWordThresholdBits (n , graph) =
  EncodeGamma.encodeGammaNat (∣ Cut.threshold graph ∣)

-- This is the REAL original encoder, not a new serialization.
graphWordStartsAtSameObject :
  (instance : Instance.GraphInstance) →
  Encode.encodeGraphWord instance ≡
  EncodeGamma.encodeGammaNat (proj₁ instance) ++
  graphWordAfterVertexCount instance
graphWordStartsAtSameObject (n , graph) = refl

readEncodedGraphVertexCount :
  (instance : Instance.GraphInstance) →
  Gamma.readGamma (Encode.encodeGraphWord instance)
    ≡ just (proj₁ instance ,
            graphWordAfterVertexCount instance)
readEncodedGraphVertexCount (n , graph) =
  Numeric.gammaReadEncodeSuffix n
    (graphWordAfterVertexCount (n , graph))

readEncodedGraphEdgeCount :
  (instance : Instance.GraphInstance) →
  Gamma.readGamma (graphWordAfterVertexCount instance)
    ≡ just
      (length (Cut.edges (proj₂ instance)) ,
       graphWordAfterEdgeCount instance)
readEncodedGraphEdgeCount (n , graph) =
  Numeric.gammaReadEncodeSuffix (length (Cut.edges graph))
    (graphWordAfterEdgeCount (n , graph))

readEncodedGraphEdgeTriples :
  (instance : Instance.GraphInstance) →
  Graph.readRawEdges
    (length (Cut.edges (proj₂ instance)))
    (graphWordAfterEdgeCount instance)
    ≡ just
      (Raw.rawOfEdges (Cut.edges (proj₂ instance)) ,
       graphWordThresholdBits instance)
readEncodedGraphEdgeTriples (n , graph) =
  Raw.readActualEdgeListWordSuffix
    (Cut.edges graph) (graphWordThresholdBits (n , graph))

readEncodedGraphThresholdMagnitude :
  (instance : Instance.GraphInstance) →
  Gamma.readGamma (graphWordThresholdBits instance)
    ≡ just
      (∣ Cut.threshold (proj₂ instance) ∣ , [])
readEncodedGraphThresholdMagnitude (n , graph) =
  Numeric.gammaReadEncodeRoundTrip
    (∣ Cut.threshold graph ∣)


------------------------------------------------------------------------
-- The EXACT parser-side 3m guard is already implied by the original
-- canonical graph serialization. It is not a separately assumed
-- Boolean condition and it never bounds declared vertex count by bits.
------------------------------------------------------------------------

readEncodedGraphEdgeCountBudget :
  (instance : Instance.GraphInstance) →
  (length (Cut.edges (proj₂ instance)) * suc (suc (suc zero)))
    ≤ length (graphWordAfterEdgeCount instance)
readEncodedGraphEdgeCountBudget instance =
  Size.encodedGraphEdgeParserBudget instance

