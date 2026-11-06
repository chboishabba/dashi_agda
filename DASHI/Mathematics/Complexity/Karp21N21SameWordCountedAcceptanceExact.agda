module DASHI.Mathematics.Complexity.Karp21N21SameWordCountedAcceptanceExact where

------------------------------------------------------------------------
-- K05/K06 ORIGINAL N21: ALL-WORD SEMANTICS + INPUT-COST COUNT.
--
-- This is a single consumer of TWO existing ORIGINAL proof owners:
--   AllWords.n21FinFreeVerifierSameWord, for *all* graph/certificate words;
--   Counted.allWordComparisonPolynomialClock, for every graph word,
--   including malformed graph headers, actual original gamma parser.
--
-- It does not invent an alternate SAT, graph or binary language.
-- It does NOT claim that native unary Nat comparisons are constant-time,
-- nor does it supply a full Turing/bit-tape execution bound.
-- Historical source: Richard Karp (1972); Elias gamma;
-- DASHI independent original typed/fin-free word consumers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeAllWordDecoderAgreementExact as SameWord
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact as Counted
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

-- Both claims pertain to the exact same original graph input word.
record SameWordCostedN21Certificate
  (word certificate : Word.BitWord) : Set where
  field
    originalN21VerifierAgreement :
      Runtime.verifyFinFreeSparseGraphWord word certificate
        ≡ Graph.LiteralN21.verifyCanonicalSparseGraphWord word certificate
    originalEndpointComparisonBound :
      Counted.actualAllWordComparisonCount word
        ≤ Counted.comparisonPolynomial (Word.encodingSize word)
    nativePolynomialComparisonBudget :
      Counted.actualAllWordComparisonCount word
        ≤ ERQ.coefficient Counted.comparisonPolynomialBound *
          ERQ.pow (suc (Word.encodingSize word))
            (ERQ.exponent Counted.comparisonPolynomialBound)

-- Every graph word (including rejected/malformed words) and every sparse
-- certificate word satisfy this actual N21 same-object proof contract.
allWordsSameVerifierAndPolynomialComparisonCount :
  (word certificate : Word.BitWord) →
  SameWordCostedN21Certificate word certificate
allWordsSameVerifierAndPolynomialComparisonCount word certificate =
  record
    { originalN21VerifierAgreement =
        SameWord.n21FinFreeVerifierSameWord word certificate
    ; originalEndpointComparisonBound =
        Counted.allWordComparisonCountBound word
    ; nativePolynomialComparisonBudget =
        Counted.allWordComparisonPolynomialClock word
    }

-- This is the exact selected downstream Boolean interpretation.
-- Source/target Karp many-one reduction polynomiality remains a
-- separate obligation; no PR.polynomialTimeVerifier is filled here.
