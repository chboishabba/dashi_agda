module DASHI.Mathematics.Complexity.Karp21FinFreeSparseCertificateWordVerifierSameExact where

------------------------------------------------------------------------
-- N21: SAME ORIGINAL CERTIFICATE WORD, SAME BOOLEAN SIGNED VERIFIER
-- ON EVERY SOURCE-VALIDATED MATCHED RAW/TYPED GRAPH FRAME.
--
-- Combines the ACTUAL Runtime.rawSparseScore Option/ℤ theorem,
-- typed Sparse.encode/decode exact-word inverse, malformed-certificate
-- rejection, and original signed threshold. Works for EVERY input
-- certificate bitword (no accepted-certificate-only assumption).
--
-- At the outer level, proves equality of the existing literal N21
-- graph verifier with Runtime.verifyFinFreeSparseGraphWord provided
-- the two ACTUAL graph-word decoders agree on their original frame.
-- Does not assume n≤bitlength or offDiagonal proof-function equality.
--
-- Remaining: prove all original gamma graph words have the requisite
-- match/rejection (incl sparse 2m budget); binary-machine clock;
-- transitive --safe and Agda exact-head kernel acceptance.
-- Karp 1972; DASHI source original sparse and gamma-code owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
import Data.Integer.Base as Int
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Golden
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe
import DASHI.Mathematics.Complexity.Karp21FinFreeActualSparseScoreAcceptanceExact as Score
import DASHI.Mathematics.Complexity.Karp21FinFreeTypedObservationConsistencyBidiExact as Numeric
import DASHI.Mathematics.Complexity.Karp21FinFreeActualPairwiseConsistencySameExact as Pairs
import DASHI.Mathematics.Complexity.Karp21FinFreeSparseCertificateCanonicalExact as Canon

-- Exact same signed-threshold decision as source Runtime verifier,
-- exposed only after the original outer gamma frame has succeeded.
rawScoreThresholdBool : Int.ℤ → Maybe Int.ℤ → Bool
rawScoreThresholdBool threshold nothing = false
rawScoreThresholdBool threshold (just score) =
  Int._≤ᵇ_ threshold score

rawFrameCertificateVerifier :
  List Graph.RawEdge → Int.ℤ → Word.BitWord → Bool
rawFrameCertificateVerifier raw threshold bits =
  rawScoreThresholdBool threshold
    (Runtime.rawSparseScore raw bits [])

thresholdAfterHistoryDecision :
  (threshold score : Int.ℤ) (accepted : Bool) →
  rawScoreThresholdBool threshold
    (Score.scoreWhenHistoryAccepts accepted score)
    ≡ Golden.andBool accepted (Int._≤ᵇ_ threshold score)
thresholdAfterHistoryDecision threshold score true = refl
thresholdAfterHistoryDecision threshold score false = refl

-- The actual ORIGINAL Fin-free signed result is the original typed
-- Sparse.verifyConsistentSparseCut Boolean on the identical 2m bits.
rawFrameSameTypedOnEncodedBits :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (threshold : Int.ℤ)
    (positive : Threshold.PositiveThreshold threshold)
    (bits : Sparse.EdgeBits typed) →
  rawFrameCertificateVerifier raw threshold
    (Sparse.encodeSparseEdgeBits bits)
    ≡ Sparse.verifyConsistentSparseCut
        (Cut.graph typed threshold positive) bits
rawFrameSameTypedOnEncodedBits raw typed fields threshold positive bits =
  let actualScore = Numeric.originalRawLocalSignedCut
        raw typed fields bits
      typedScore = Sparse.sparseEdgeScore typed bits
      originalGuard = Pairs.rawHistorySameOriginalTypedSparseConsistency
        raw typed fields bits
      originalSigned = Numeric.originalRawLocalSignedCutMatchesTyped
        raw typed fields bits
      exactRuntime = Score.rawSparseScoreExactlyExpected
        raw typed fields bits []
  in trans
       (cong (rawScoreThresholdBool threshold) exactRuntime)
       (trans
         (cong₂
           (λ status value →
             rawScoreThresholdBool threshold
               (Score.scoreWhenHistoryAccepts status value))
           originalGuard originalSigned)
         (thresholdAfterHistoryDecision threshold typedScore
           (Sparse.allEndpointOccurrencesConsistent
             (Sparse.endpointObservations typed bits))))

-- UNCONDITIONAL CERTIFICATE WORD: accepted same 2m code or every
-- rejected/trailing/malformed certificate byte sequence. No
-- certificate-shape premise is passed in by the caller.
rawFrameSameTypedForEveryCertificate :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (threshold : Int.ℤ)
    (positive : Threshold.PositiveThreshold threshold)
    (word : Word.BitWord) →
  rawFrameCertificateVerifier raw threshold word
    ≡ Sparse.verifySparseCutBitWord
        (Cut.graph typed threshold positive) word
rawFrameSameTypedForEveryCertificate
  raw typed fields threshold positive word
  with Sparse.decodeSparseEdgeBits typed word
... | nothing =
  cong (rawScoreThresholdBool threshold)
    (Canon.rawScoreCannotAcceptMalformedSparseBits
      raw typed fields word [] refl)
... | just local =
  trans
    (sym (cong (rawFrameCertificateVerifier raw threshold)
      (Canon.sparseDecodedWordIsExactOriginalEncoding
        typed word local refl)))
    (rawFrameSameTypedOnEncodedBits
      raw typed fields threshold positive local)

------------------------------------------------------------------------
-- SAME ORIGINAL GRAPH WORD, CONDITIONAL ON LITERAL SOURCE DECODER
-- MATCH. The next standalone obligation establishes this hypothesis
-- for ALL gamma words or proves that both decoders reject them.
------------------------------------------------------------------------

n21FinFreeVerifierSameWordOnMatchedFrame :
  ∀ {n : Nat}
    (word certificate : Word.BitWord)
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (threshold : Nat)
    (positive : Threshold.PositiveThreshold (Int.+ threshold)) →
  (Graph.decodeGraphWord word
    ≡ just (n , Cut.graph typed (Int.+ threshold) positive)) →
  (Runtime.readRawGraphWord word
    ≡ just (Runtime.parsed-raw-graph n raw threshold)) →
  Observe.RawEdgeListFieldsSame raw typed →
  Runtime.verifyFinFreeSparseGraphWord word certificate
    ≡ Graph.LiteralN21.verifyCanonicalSparseGraphWord word certificate
n21FinFreeVerifierSameWordOnMatchedFrame
  word certificate raw typed threshold positive
  typedParsed rawParsed fields
  rewrite typedParsed | rawParsed =
  rawFrameSameTypedForEveryCertificate
    raw typed fields (Int.+ threshold) positive certificate

-- Both original readers reject exactly the given graph word:
-- no fresh language predicate is substituted on malformed input.
n21FinFreeVerifierSameWordOnBothRejected :
  (word certificate : Word.BitWord) →
  Graph.decodeGraphWord word ≡ nothing →
  Runtime.readRawGraphWord word ≡ nothing →
  Runtime.verifyFinFreeSparseGraphWord word certificate
    ≡ Graph.LiteralN21.verifyCanonicalSparseGraphWord word certificate
n21FinFreeVerifierSameWordOnBothRejected
  word certificate typedRejected rawRejected
  rewrite typedRejected | rawRejected = refl
