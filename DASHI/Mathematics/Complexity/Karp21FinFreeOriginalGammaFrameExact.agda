module DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGammaFrameExact where

------------------------------------------------------------------------
-- P1/N21: ACTUAL FIN-FREE RAW WORD PARSER ON ORIGINAL E20 IMAGE.
--
-- Graph.decodeGraphWord and Runtime.readRawGraphWord read the very
-- same gamma(n), gamma(m), signed edge triples and gamma(W) wire.
-- This owner follows the ORIGINAL Runtime parser, not a proxy oracle,
-- and reuses previous source-field and lexicographic check proofs.
--
-- No Fin n constructed on this runtime parse route. This does NOT
-- prove the two sparse witness verifiers have equal scores for all
-- words, nor that the unary Nat fields have binary-tape clocks.
-- Agda kernel / transitive --safe acceptance remains unrun.
--
-- Original Karp 1972; DASHI Fin-free runtime and gamma source owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.List.Base using (List; []; length)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ; +_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21PositiveThresholdGammaExact as Positive
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21OriginalGammaGraphWordFieldsReplayExact as Fields
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeE20RawValidatorAgreementExact as RawValid

-- General success theorem for the original finite, Fin-free nested
-- parser under its exact same-word successful-read obligations.
readFinFreeRawGraphFromActualFrame :
  (word : Word.BitWord) (n m k : Nat)
  (afterN afterM afterEdges : Word.BitWord)
  (raw : List Graph.RawEdge) →
  Gamma.readGamma word ≡ just (n , afterN) →
  Gamma.readGamma afterN ≡ just (m , afterM) →
  m * suc (suc (suc zero)) ≤ length afterM →
  Graph.readRawEdges m afterM ≡ just (raw , afterEdges) →
  Gamma.readGamma afterEdges ≡ just (suc k , []) →
  Runtime.validRawEdges n Graph.noPrevious raw ≡ true →
  Runtime.readRawGraphWord word
    ≡ just (Runtime.parsed-raw-graph n raw (suc k))
readFinFreeRawGraphFromActualFrame
    word n m k afterN afterM afterEdges raw
    readN readM tripleBound readEdges readW valid
  rewrite readN | readM
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no violatesTriple = ⊥-elim (violatesTriple tripleBound)
... | yes _ rewrite readEdges | readW | valid = refl

-- In the E20 scaled complete image this constructs an ACTUAL
-- successful runtime parse, rather than only showing each raw edge
-- is well-formed in isolation.
e20OriginalWordFinFreeRawDecode :
  ∀ {n : Nat}
    (source : Vec.Vec ℤ n)
    (threshold : ℤ)
    (positive : Threshold.PositiveThreshold threshold) →
  Σ Nat
    (λ k →
      (threshold ≡ + (suc k))
      × (Runtime.readRawGraphWord
          (Encode.encodeGraphWord
            (n , Cut.graph
              (Gen.completeScaledPairEdges source)
              threshold positive))
          ≡ just
            (Runtime.parsed-raw-graph n
              (Raw.rawOfEdges (Gen.completeScaledPairEdges source))
              (suc k))))
e20OriginalWordFinFreeRawDecode {n} source threshold positive
  with Positive.positiveThresholdIsSuccessor threshold positive
... | k , refl =
  let graph = Cut.graph (Gen.completeScaledPairEdges source)
                (+ (suc k)) positive
      instance = n , graph
      word = Encode.encodeGraphWord instance
  in k , (refl ,
    readFinFreeRawGraphFromActualFrame
      word n (length (Cut.edges graph)) k
      (Fields.graphWordAfterVertexCount instance)
      (Fields.graphWordAfterEdgeCount instance)
      (Fields.graphWordThresholdBits instance)
      (Raw.rawOfEdges (Cut.edges graph))
      (Fields.readEncodedGraphVertexCount instance)
      (Fields.readEncodedGraphEdgeCount instance)
      (Fields.readEncodedGraphEdgeCountBudget instance)
      (Fields.readEncodedGraphEdgeTriples instance)
      (Fields.readEncodedGraphThresholdMagnitude instance)
      (RawValid.scaledCompleteRuntimeRawValid source))
