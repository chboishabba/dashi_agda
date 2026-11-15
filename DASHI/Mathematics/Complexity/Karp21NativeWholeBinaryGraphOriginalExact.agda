module DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphOriginalExact where

------------------------------------------------------------------------
-- B6: original signed gamma graph word on EVERY input word.
--
-- Observation is proof-only. Executable code is exactly
-- Whole.readNativeWholeBinaryGraphWord, which operates on bitwords
-- n/m/u/v, a structurally fuel-bounded binary m loop, binary
-- strict-order validation, and the real strictly-positive W reader.
-- No Nat-producing graph reader executes in that native path.
--
-- The RHS uses the actual original Fin-free graph word grammar.
-- All proof dependencies are source candidates until Agda 2.9
-- checks the exact head and transitive original modules.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.List.Base using (List; length)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original
import DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact as Header
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetFuelExact as Fuel
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Valid
import DASHI.Mathematics.Complexity.Karp21NativeBinaryValidRawEdgesOriginalExact as ValidOriginal
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNumericFrameExact as Threshold
import DASHI.Mathematics.Complexity.Karp21NativeOriginalWholeGraphFieldsWeldExact as Fields
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

observeWholeBinaryGraph : Whole.NativeWholeBinaryGraph →
  Original.ParsedRawGraph
observeWholeBinaryGraph (Whole.whole-binary-graph n edges w) =
  Original.parsed-raw-graph (Value.valueLE n)
    (Edge.originalEdgeListObservation edges) (Value.valueLE w)

observeNativeWholeBinaryGraphWord :
  Word.BitWord → Maybe Original.ParsedRawGraph
observeNativeWholeBinaryGraphWord word
  with Whole.readNativeWholeBinaryGraphWord word
... | nothing = nothing
... | just parsed = just (observeWholeBinaryGraph parsed)

-- Factor the actual original source AFTER the gamma n/m headers
-- and source m*3 guard. No alternative decoding contract.
originalGraphAfterHeader :
  Nat → Nat → Word.BitWord → Maybe Original.ParsedRawGraph
originalGraphAfterHeader n m afterM
  with Graph.readRawEdges m afterM
... | nothing = nothing
... | just (edges , afterEdges) =
  Fields.originalTerminal n edges afterEdges

originalGraphViaBudgetedHeader :
  Word.BitWord → Maybe Original.ParsedRawGraph
originalGraphViaBudgetedHeader word
  with Header.readOriginalBudgetedHeader word
... | nothing = nothing
... | just (Header.numeric-header n m afterM) =
  originalGraphAfterHeader n m afterM

-- Definitional factorization of THE ORIGINAL readRawGraphWord,
-- including malformed headers, failed 3m guard and full suffix.
originalGraphViaBudgetedHeaderSameOriginal :
  (word : Word.BitWord) →
  originalGraphViaBudgetedHeader word ≡ Original.readRawGraphWord word
originalGraphViaBudgetedHeaderSameOriginal word
  with Gamma.readGamma word
... | nothing = refl
... | just (n , afterN) with Gamma.readGamma afterN
... | nothing = refl
... | just (m , afterM)
  -- The original literally uses m*3; the binary budget's Nat
  -- reflection uses 3*m. Pay this commutativity explicitly.
  rewrite sym (NatP.*-comm m (suc (suc (suc zero))))
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
... | no _ = refl
... | yes _ with Graph.readRawEdges m afterM
... | nothing = refl
... | just (edges , afterEdges)
  with Gamma.readGamma afterEdges
... | nothing = refl
... | just (zero , suffix) = refl
... | just (suc w , _ ∷ _) = refl
... | just (suc w , [])
  with Original.validRawEdges n Graph.noPrevious edges
... | false = refl
... | true = refl

-- Exact original terminal for the ACTUAL binary u/v validation and
-- native threshold parser, including zero W, trailing suffix,
-- reversed/duplicate edges and noncanonical zero-padded LE fields.
binaryTerminal :
  Word.BitWord → List Edge.BinaryRawEdge →
  Word.BitWord → Maybe Original.ParsedRawGraph
binaryTerminal nLE edges bits
  with Positive.readPositiveGammaLE bits
... | nothing = nothing
... | just (wLE , _ ∷ _) = nothing
... | just (wLE , [])
  with Valid.validNativeBinaryEdges nLE Valid.noPrevious edges
... | false = nothing
... | true = just (observeWholeBinaryGraph
  (Whole.whole-binary-graph nLE edges wLE))

binaryTerminalSameOriginal :
  (nLE : Word.BitWord)
  (edges : List Edge.BinaryRawEdge)
  (bits : Word.BitWord) →
  binaryTerminal nLE edges bits ≡
    Fields.originalTerminal (Value.valueLE nLE)
      (Edge.originalEdgeListObservation edges) bits
binaryTerminalSameOriginal nLE edges bits =
  trans (binaryTerminalSameStrict nLE edges bits)
    (sym (Fields.sourceTerminalSameStrict
      (Value.valueLE nLE)
      (Edge.originalEdgeListObservation edges) bits))
  where
    binaryTerminalSameStrict :
      (n : Word.BitWord)
      (es : List Edge.BinaryRawEdge)
      (suffix : Word.BitWord) →
      binaryTerminal n es suffix ≡
      Fields.strictTerminal (Value.valueLE n)
        (Edge.originalEdgeListObservation es) suffix
    binaryTerminalSameStrict n es suffix
      rewrite sym (Threshold.nativePositiveThresholdParserSameOriginal suffix)
      with Positive.readPositiveGammaLE suffix
    ... | nothing = refl
    ... | just (w , _ ∷ _) = refl
    ... | just (w , [])
      with Valid.validNativeBinaryEdges n Valid.noPrevious es
         | ValidOriginal.nativeBinaryValidRawEdgesSameOriginal
             n Valid.noPrevious es
    ... | false | aligned rewrite sym aligned = refl
    ... | true | aligned rewrite sym aligned = refl

-- A successful budgeted native header necessarily passed the ACTUAL
-- binary 3m guard. This proof does not assume any caller-created
-- 'accepted budget' witness.
budgetedHeaderCarriesGuard :
  (word n m afterM : Word.BitWord) →
  Header.readNativeBinaryBudgetedHeader word
    ≡ just (Header.binary-header n m afterM) →
  Budget.binaryCountBudget m afterM ≡ true
budgetedHeaderCarriesGuard word n m afterM accepted
  with Header.readNativeBinaryGraphHeader word
... | nothing with accepted
... | ()
... | just (Header.binary-header n' m' suffix)
  with Budget.binaryCountBudget m' suffix in paid
... | false with accepted
... | ()
... | true with accepted
... | refl = paid

-- B6 full graph parser observational equality against the literal
-- original signed gamma readRawGraphWord: all words and rejection
-- cases, including failure at every individual grammar field.
nativeWholeBinaryGraphWordSameOriginal :
  (word : Word.BitWord) →
  observeNativeWholeBinaryGraphWord word
    ≡ Original.readRawGraphWord word
nativeWholeBinaryGraphWordSameOriginal word =
  trans (nativeWholeBinaryGraphSameBudgetedOriginal word)
    (originalGraphViaBudgetedHeaderSameOriginal word)
  where
    nativeWholeBinaryGraphSameBudgetedOriginal :
      (word : Word.BitWord) →
      observeNativeWholeBinaryGraphWord word ≡
        originalGraphViaBudgetedHeader word
    nativeWholeBinaryGraphSameBudgetedOriginal word
      with Header.readNativeBinaryBudgetedHeader word in header
         | Header.nativeBinaryBudgetedHeadersSameOriginal word
    ... | nothing | headerEq rewrite sym headerEq = refl
    ... | just (Header.binary-header n m afterM) | headerEq
      rewrite sym headerEq
      with Whole.readBinaryRawEdgesFuel (length afterM) m afterM
         | Fuel.nativeBudgetedBinaryRawEdgesSameOriginal
             m afterM
             (budgetedHeaderCarriesGuard word n m afterM header)
    ... | nothing | edgeEq rewrite sym edgeEq = refl
    ... | just (edges , afterEdges) | edgeEq
      rewrite sym edgeEq =
      binaryTerminalSameOriginal n edges afterEdges
