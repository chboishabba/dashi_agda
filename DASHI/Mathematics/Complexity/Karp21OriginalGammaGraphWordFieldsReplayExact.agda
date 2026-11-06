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
  (inst : Instance.GraphInstance) → Word.BitWord
graphWordAfterVertexCount (n , graph) =
  EncodeGamma.encodeGammaNat (length (Cut.edges graph)) ++
  Encode.encodeEdgeWords (Cut.edges graph) ++
  EncodeGamma.encodeGammaNat (∣ Cut.threshold graph ∣)

graphWordAfterEdgeCount :
  (inst : Instance.GraphInstance) → Word.BitWord
graphWordAfterEdgeCount (n , graph) =
  Encode.encodeEdgeWords (Cut.edges graph) ++
  EncodeGamma.encodeGammaNat (∣ Cut.threshold graph ∣)

graphWordThresholdBits :
  (inst : Instance.GraphInstance) → Word.BitWord
graphWordThresholdBits (n , graph) =
  EncodeGamma.encodeGammaNat (∣ Cut.threshold graph ∣)

-- This is the REAL original encoder, not a new serialization.
graphWordStartsAtSameObject :
  (inst : Instance.GraphInstance) →
  Encode.encodeGraphWord inst ≡
  EncodeGamma.encodeGammaNat (proj₁ inst) ++
  graphWordAfterVertexCount inst
graphWordStartsAtSameObject (n , graph) = refl

readEncodedGraphVertexCount :
  (inst : Instance.GraphInstance) →
  Gamma.readGamma (Encode.encodeGraphWord inst)
    ≡ just (proj₁ inst ,
            graphWordAfterVertexCount inst)
readEncodedGraphVertexCount (n , graph) =
  Numeric.gammaReadEncodeSuffix n
    (graphWordAfterVertexCount (n , graph))

readEncodedGraphEdgeCount :
  (inst : Instance.GraphInstance) →
  Gamma.readGamma (graphWordAfterVertexCount inst)
    ≡ just
      (length (Cut.edges (proj₂ inst)) ,
       graphWordAfterEdgeCount inst)
readEncodedGraphEdgeCount (n , graph) =
  Numeric.gammaReadEncodeSuffix (length (Cut.edges graph))
    (graphWordAfterEdgeCount (n , graph))

readEncodedGraphEdgeTriples :
  (inst : Instance.GraphInstance) →
  Graph.readRawEdges
    (length (Cut.edges (proj₂ inst)))
    (graphWordAfterEdgeCount inst)
    ≡ just
      (Raw.rawOfEdges (Cut.edges (proj₂ inst)) ,
       graphWordThresholdBits inst)
readEncodedGraphEdgeTriples (n , graph) =
  Raw.readActualEdgeListWordSuffix
    (Cut.edges graph) (graphWordThresholdBits (n , graph))

readEncodedGraphThresholdMagnitude :
  (inst : Instance.GraphInstance) →
  Gamma.readGamma (graphWordThresholdBits inst)
    ≡ just
      (∣ Cut.threshold (proj₂ inst) ∣ , [])
readEncodedGraphThresholdMagnitude (n , graph) =
  Numeric.gammaReadEncodeRoundTrip
    (∣ Cut.threshold graph ∣)


------------------------------------------------------------------------
-- The EXACT parser-side 3m guard is already implied by the original
-- canonical graph serialization. It is not a separately assumed
-- Boolean condition and it never bounds declared vertex count by bits.
------------------------------------------------------------------------

readEncodedGraphEdgeCountBudget :
  (inst : Instance.GraphInstance) →
  (length (Cut.edges (proj₂ inst)) * suc (suc (suc zero)))
    ≤ length (graphWordAfterEdgeCount inst)
readEncodedGraphEdgeCountBudget inst =
  Size.encodedGraphEdgeParserBudget inst

