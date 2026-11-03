module DASHI.Mathematics.Complexity.Karp21CanonicalParsedGraphAcceptanceExact where

------------------------------------------------------------------------
-- E20 / N21: ACTUAL VALIDATED FINITE GRAPH ACCEPTANCE, BOTH DIRECTIONS
--
-- We construct the same positive-threshold WeightedCutGraph that the
-- signed PARTITION reduction already uses, and replace *only* its edge
-- list with the output of the ORIGINAL validateRawEdges parser.
--
-- The previous source-owned theorem returns the real decoded Fin n
-- edges and a fieldwise observation proving exact signed cut-score
-- equivalence. The terminal property here is therefore the original
-- WeightedMaxCutYES predicate, not a proxy truth marker.
--
-- Crucially the two offDiagonal proof functions are never equated.
-- The remaining gamma n/m/W field composition, actual
-- decodeGraphWordCertified result and bit-machine clocks are separate.
--
-- Richard Karp (1972); DASHI original weighted graph, finite signed
-- PARTITION output and canonical raw graph parser owners.
-- Source-written only. No Agda compiler/kernel receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; length)
open import Data.Integer.Base using (ℤ; _*_)
open import Data.Maybe.Base using (just)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)

import Data.Vec.Base as Vec
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorCompleteExact as Valid
import DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact as Observed
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21SignedPartitionIndexedGraphDecisionExact as Indexed
import DASHI.Mathematics.Complexity.Karp21SignedPartitionActualGraphYESExact as Actual
import DASHI.Mathematics.Complexity.Karp21PartitionScaledInstanceExact as Source
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold

------------------------------------------------------------------------
-- General theorem for the original scaled complete signed graph and
-- ANY source-owned positive threshold: the raw decoder's returned
-- Fin graph is actually the same Max-Cut decision problem.
------------------------------------------------------------------------

scaledRawParsedGraphAcceptanceBidi :
  ∀ {n : Nat}
    (source : Vec.Vec ℤ n)
    (threshold : ℤ)
    (positive : Threshold.PositiveThreshold threshold) →
  Σ (Cut.WeightedCutGraph n)
    (λ decoded →
      (Graph.validateRawEdges n Graph.noPrevious
        (Raw.rawOfEdges (Gen.completeScaledPairEdges source))
        ≡ just (Cut.edges decoded))
      × PR.Iff
        (Cut.WeightedMaxCutYES
          (Cut.graph (Gen.completeScaledPairEdges source)
            threshold positive))
        (Cut.WeightedMaxCutYES decoded))
scaledRawParsedGraphAcceptanceBidi {n} source threshold positive
  with Valid.scaledCompleteRawValidatorSuccess source
... | decodedEdges , (parserAccepted , sameFields) =
  Cut.graph decodedEdges threshold positive ,
    (parserAccepted ,
      Observed.sameWeightedGraphsAccept
        (Cut.graph (Gen.completeScaledPairEdges source)
          threshold positive)
        (Cut.graph decodedEdges threshold positive)
        refl
        sameFields)

------------------------------------------------------------------------
-- Specialization to the EXACT original E20 source-indexed weighted
-- graph, with its signed total-square nonzero positive threshold.
-- No work is delegated to an assumed image BIDI interface.
------------------------------------------------------------------------

e20ScaledCanonicalRawGraphAcceptsIff :
  (parts : List ℤ)
  (nonzero : Threshold.NonZero (Source.sourceTotal parts)) →
  Σ (Cut.WeightedCutGraph (length parts))
    (λ decoded →
      (Graph.validateRawEdges (length parts) Graph.noPrevious
        (Raw.rawOfEdges
          (Cut.edges (Actual.sourceIndexedWeightedGraph parts nonzero)))
        ≡ just (Cut.edges decoded))
      × PR.Iff
        (Cut.WeightedMaxCutYES
          (Actual.sourceIndexedWeightedGraph parts nonzero))
        (Cut.WeightedMaxCutYES decoded))
e20ScaledCanonicalRawGraphAcceptsIff parts nonzero =
  scaledRawParsedGraphAcceptanceBidi
    (Indexed.vectorOfList parts)
    (Source.sourceTotal parts * Source.sourceTotal parts)
    (Threshold.nonzeroTotalSquareIsPositiveThreshold
      (Source.sourceTotal parts) nonzero)
