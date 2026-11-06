module DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorPremisesExact where

------------------------------------------------------------------------
-- E20: all exact execution-order premises of the ORIGINAL
-- Decode.validateRawEdges on the SOURCE generated complete graph.
--
-- The validator reads a head (u,v,w), checks u<v and v<n, checks
-- strictAfter with the previous edge, then repeats from (u,v).
-- The two existing source owners supply exactly these premises:
--    Bounds.sourceIndexedScaledCompleteGraphEndpoints
--    StrictAfter.sourceIndexedScaledGraphPassesStrictAfter
--
-- This file joins them structurally in the SAME recursive edge order.
-- It does NOT yet claim that the proof-carrying parser returns just,
-- or that dependent offDiagonal functions are judgmentally equal.
-- Both are separate checked proof leaves; actual machine clock OPEN.
--
-- Karp 1972; original DASHI UpperPair/weighted graph/parser owners.
-- Source-written, not Agda-kernel accepted, and not --safe while
-- original weighted-graph imports remain non-Golden.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ)

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphEndpointOrderExact as Bounds
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictAfterExact as Ordered
import DASHI.Mathematics.Complexity.Karp21UpperPairStructuralLexOrderExact as Lex
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Decode

-- This is a proof of precisely the checks performed by the parser,
-- with the same previous-pair state and the same signed edge list.
data ValidFromPrevious {n : Nat} :
  Decode.PreviousPair →
  List (Cut.SignedUndirectedEdge n) → Set where
  validNil :
    ∀ {prev} →
    ValidFromPrevious prev []
  validCons :
    ∀ {prev edge rest} →
    Bounds.CanonicalEdgeEndpoints edge →
    Decode.strictAfter prev
      (Fin.toℕ (Cut.first edge))
      (Fin.toℕ (Cut.second edge)) ≡ true →
    ValidFromPrevious
      (Decode.previous
        (Fin.toℕ (Cut.first edge))
        (Fin.toℕ (Cut.second edge)))
      rest →
    ValidFromPrevious prev (edge ∷ rest)

-- The first source edge needs no previous-index comparison.
firstEdgeAndTailValid :
  ∀ {n : Nat}
    (head : Cut.SignedUndirectedEdge n)
    (rest : List (Cut.SignedUndirectedEdge n)) →
  Bounds.AllCanonicalEdgeEndpoints rest →
  Lex.AllAfter Ordered.ParserStrictlyAfterEdge head rest →
  Lex.StrictSorted Ordered.ParserStrictlyAfterEdge rest →
  ValidFromPrevious
    (Decode.previous
      (Fin.toℕ (Cut.first head))
      (Fin.toℕ (Cut.second head)))
    rest
firstEdgeAndTailValid head [] Bounds.canonicalNil
  Lex.afterNil Lex.sortedNil = validNil
firstEdgeAndTailValid head (edge ∷ rest)
  (Bounds.canonicalCons edgeBounds tailBounds)
  (Lex.afterCons headBeforeEdge allHeadBeforeTail)
  (Lex.sortedCons edgeBeforeRest sortedRest) =
  validCons edgeBounds headBeforeEdge
    (firstEdgeAndTailValid
      edge rest tailBounds edgeBeforeRest sortedRest)

-- The actual strong sortedness supplies each successor comparison,
-- and the endpoint proof supplies exactly the numerical range checks.
canonicalValidatorPremises :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n)) →
  Bounds.AllCanonicalEdgeEndpoints edges →
  Lex.StrictSorted Ordered.ParserStrictlyAfterEdge edges →
  ValidFromPrevious Decode.noPrevious edges
canonicalValidatorPremises [] Bounds.canonicalNil Lex.sortedNil =
  validNil
canonicalValidatorPremises (edge ∷ rest)
  (Bounds.canonicalCons edgeBounds tailBounds)
  (Lex.sortedCons edgeBeforeRest sortedRest) =
  validCons edgeBounds refl
    (firstEdgeAndTailValid
      edge rest tailBounds edgeBeforeRest sortedRest)

-- The ORIGINAL signed, four-times scaled complete graph: no parallel
-- construction, no reordering and no imported cut/partition witness.
scaledCompleteGraphValidatorPremises :
  ∀ {n : Nat} (source : Vec.Vec ℤ n) →
  ValidFromPrevious Decode.noPrevious
    (Gen.completeScaledPairEdges source)
scaledCompleteGraphValidatorPremises source =
  canonicalValidatorPremises
    (Gen.completeScaledPairEdges source)
    (Bounds.sourceIndexedScaledCompleteGraphEndpoints source)
    (Ordered.sourceIndexedScaledGraphPassesStrictAfter source)
