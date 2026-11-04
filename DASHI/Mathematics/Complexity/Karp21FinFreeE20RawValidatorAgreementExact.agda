module DASHI.Mathematics.Complexity.Karp21FinFreeE20RawValidatorAgreementExact where

------------------------------------------------------------------------
-- E20/N21: ORIGINAL CANONICAL GRAPH CHECKS AGREE WITH FIN-FREE RUNTIME.
--
-- Reuse the ACTUAL ordered signed complete-graph edge list, original
-- dependent Fin graph validator and the existing fin-free raw runtime.
--
-- The source's previously proved ValidFromPrevious certificate already
-- supplies each inequality and strictAfter result used by BOTH paths.
-- Consequently the fin-free runtime's entire recursive raw validation
-- succeeds on precisely the original E20 generated graph family.
--
-- We also transport the original signed MAX CUT YES iff through the
-- existing dependent raw decoder, without equating proof-function fields.
--
-- This is the E20 IMAGE portion of the N21 same-word frontier, not a
-- universal equality on all input words or an executable bit-tape clock.
-- Golden Agda / transitive --safe / kernel acceptance: NOT YET CHECKED.
--
-- Richard Karp (1972); DASHI original E20 graph, gamma graph parser,
-- canonical raw validator and fin-free N21 runtime proof owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Integer.Base using (ℤ)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact as Raw
import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorPremisesExact as Valid
import DASHI.Mathematics.Complexity.Karp21CanonicalParsedGraphAcceptanceExact as Parsed
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21CanonicalRawValidatorCompleteExact as Validated
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21DecodedWeightedCutSemanticBidiExact as Observed
import DASHI.Mathematics.Complexity.Karp21EncodedGraphSparseBitBoundExact as WireSize
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

------------------------------------------------------------------------
-- The ORIGINAL source-owned parser premises directly discharge all
-- actual recursive checks executed by the Fin-free raw validator.
-- This is structural induction on the SAME edge list, not an oracle.
------------------------------------------------------------------------

canonicalRawRuntimeChecksPass :
  ∀ {n : Nat}
    (prev : Decode.PreviousPair)
    (originals : List (Cut.SignedUndirectedEdge n)) →
  Valid.ValidFromPrevious prev originals →
  Runtime.validRawEdges n prev (Raw.rawOfEdges originals) ≡ true
canonicalRawRuntimeChecksPass prev [] Valid.validNil = refl
canonicalRawRuntimeChecksPass {n} prev (edge ∷ rest)
    (Valid.validCons (ordered , secondBound) strictCheck restValid)
  with NatP._<?_
         (Fin.toℕ (Cut.first edge))
         (Fin.toℕ (Cut.second edge))
     | NatP._<?_
         (Fin.toℕ (Cut.second edge)) n
     | Decode.strictAfter prev
         (Fin.toℕ (Cut.first edge))
         (Fin.toℕ (Cut.second edge))
... | yes _ | yes _ | true =
  canonicalRawRuntimeChecksPass
    (Decode.previous
      (Fin.toℕ (Cut.first edge))
      (Fin.toℕ (Cut.second edge)))
    rest restValid
... | no notLess | _ | _ = ⊥-elim (notLess ordered)
... | yes _ | no notRange | _ = ⊥-elim (notRange secondBound)
... | yes _ | yes _ | false =
  ⊥-elim (Boolean.falseNotTrue strictCheck)

scaledCompleteRuntimeRawValid :
  ∀ {n : Nat} (source : Vec.Vec ℤ n) →
  Runtime.validRawEdges n Decode.noPrevious
    (Raw.rawOfEdges (Gen.completeScaledPairEdges source)) ≡ true
scaledCompleteRuntimeRawValid source =
  canonicalRawRuntimeChecksPass
    Decode.noPrevious
    (Gen.completeScaledPairEdges source)
    (Valid.scaledCompleteGraphValidatorPremises source)

------------------------------------------------------------------------
-- BOTH real validation routes agree on the SAME E20 finite graph.
-- The original dependent parser's returned graph is observationally
-- equivalent to E20 under the real signed threshold and cut score.
------------------------------------------------------------------------

e20FiniteRawParsersAgreeAndPreserveYES :
  ∀ {n : Nat}
    (source : Vec.Vec ℤ n)
    (threshold : ℤ)
    (positive : Threshold.PositiveThreshold threshold) →
  Σ (Cut.WeightedCutGraph n)
    (λ decoded →
      (Decode.validateRawEdges n Decode.noPrevious
        (Raw.rawOfEdges (Gen.completeScaledPairEdges source))
        ≡ just (Cut.edges decoded))
      ×
      (Runtime.validRawEdges n Decode.noPrevious
        (Raw.rawOfEdges (Gen.completeScaledPairEdges source)) ≡ true)
      ×
      PR.Iff
        (Cut.WeightedMaxCutYES
          (Cut.graph (Gen.completeScaledPairEdges source)
            threshold positive))
        (Cut.WeightedMaxCutYES decoded))
e20FiniteRawParsersAgreeAndPreserveYES
    source threshold positive
  with Parsed.scaledRawParsedGraphAcceptanceBidi
    source threshold positive
... | decoded , (parsed , sameYES) =
  decoded ,
    (parsed ,
      (scaledCompleteRuntimeRawValid source ,
       sameYES))

------------------------------------------------------------------------
-- The actual returned Fin edge list has the SAME number of edges as
-- the original source. Therefore the already-proved 2m witness-bit
-- bound for the ORIGINAL graph word applies to the PARSER OUTPUT.
-- This is the exact dependent sparse-guard premise, not a fabricated
-- assumption or a claim about binary tape execution.
------------------------------------------------------------------------

e20DecodedEdgesFitOriginalSparseWord :
  ∀ {n : Nat}
    (source : Vec.Vec ℤ n)
    (threshold : ℤ)
    (positive : Threshold.PositiveThreshold threshold) →
  Σ (List (Cut.SignedUndirectedEdge n))
    (λ decoded →
      (Decode.validateRawEdges n Decode.noPrevious
        (Raw.rawOfEdges (Gen.completeScaledPairEdges source))
        ≡ just decoded)
      ×
      (Sparse.twoPerEdge (length decoded)
        ≤ Word.encodingSize
          (Encode.encodeGraphWord
            (n , Cut.graph (Gen.completeScaledPairEdges source)
              threshold positive))))
e20DecodedEdgesFitOriginalSparseWord {n} source threshold positive
  with Validated.scaledCompleteRawValidatorSuccess source
... | decoded , (parserAccepted , fields) =
  decoded ,
    (parserAccepted ,
      subst
        (λ m →
          Sparse.twoPerEdge m
            ≤ Word.encodingSize
              (Encode.encodeGraphWord
                (n , Cut.graph (Gen.completeScaledPairEdges source)
                  threshold positive)))
        (Observed.sameWeightedEdgeListLength
          (Gen.completeScaledPairEdges source) decoded fields)
        (WireSize.encodedGraphAtLeastSparseBits
          (n , Cut.graph (Gen.completeScaledPairEdges source)
            threshold positive)))
