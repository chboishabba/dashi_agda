module DASHI.Mathematics.Complexity.Karp21NativeSelectedSignedScoreExact where

------------------------------------------------------------------------
-- Karp N21 original rawSparseScore: numerical selected native tokens.
--
-- The actual gamma-native signed raw-edge parser constructs each pair
-- from (raw-edge u v (interpretNativeToken token), token). Hence its
-- fields agree in ℤ. This owner carries that precise proof through
-- original endpointConsistent, 2-bits-per-edge, boolEqual filtering
-- and optional trace reconstruction.
--
-- The native two-lane Ledger still needs a signed-integer observation
-- theorem: this source uses the actual native token numeric observation,
-- not an invented second gamma parser. No cost or NP witness is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base using (ℤ; +_; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact as Paired
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact as Original
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeRawEdgeStreamExact as Stream

data RawTokenAligned : List Paired.PairedRawEdge → Set where
  alignedNil : RawTokenAligned []
  alignedCons :
    ∀ {u v : Nat} {w : ℤ}
      {token : Signed.SignedMagnitudeBits}
      {rest : List Paired.PairedRawEdge} →
    w ≡ Value.interpretNativeToken token →
    RawTokenAligned rest →
    RawTokenAligned
      ((Graph.raw-edge u v w , token) ∷ rest)

data SelectedTokenAligned : List Paired.SelectedPair → Set where
  selectedNil : SelectedTokenAligned []
  selectedCons :
    ∀ {w : ℤ} {token : Signed.SignedMagnitudeBits}
      {rest : List Paired.SelectedPair} →
    w ≡ Value.interpretNativeToken token →
    SelectedTokenAligned rest →
    SelectedTokenAligned ((w , token) ∷ rest)

-- Original selected-edge filtering NEVER changes signed token values,
-- even when the certificate is malformed or an endpoint conflicts.
selectedTraceRetainsNativeNumericalAlignment :
  (paired : List Paired.PairedRawEdge)
  (bits : Word.BitWord)
  (history : List (Nat × Bool)) →
  RawTokenAligned paired →
  (selected : List Paired.SelectedPair) →
  Paired.selectPairedTrace paired bits history ≡ just selected →
  SelectedTokenAligned selected
selectedTraceRetainsNativeNumericalAlignment [] [] history
  alignedNil [] refl = selectedNil
selectedTraceRetainsNativeNumericalAlignment [] (_ ∷ _) history
  alignedNil selected ()
selectedTraceRetainsNativeNumericalAlignment (_ ∷ _) [] history
  aligned selected ()
selectedTraceRetainsNativeNumericalAlignment (_ ∷ _) (_ ∷ []) history
  aligned selected ()
selectedTraceRetainsNativeNumericalAlignment
  ((Graph.raw-edge u v w , token) ∷ rest)
  (a ∷ b ∷ bits) history
  (alignedCons weightEq restAligned) selected result
  with Runtime.endpointConsistent u a history
     | Runtime.endpointConsistent v b history
... | false | _ = caseImpossible result
  where
    caseImpossible : ∀ {A : Set} {x : A} → nothing ≡ just x →
      SelectedTokenAligned selected
    caseImpossible ()
... | true | false = caseImpossible result
  where
    caseImpossible : ∀ {A : Set} {x : A} → nothing ≡ just x →
      SelectedTokenAligned selected
    caseImpossible ()
... | true | true
  with Paired.selectPairedTrace
    rest bits ((u , a) ∷ (v , b) ∷ history)
... | nothing = caseImpossible result
  where
    caseImpossible : ∀ {A : Set} {x : A} → nothing ≡ just x →
      SelectedTokenAligned selected
    caseImpossible ()
... | just selectedRest with Boolean.boolEqual a b
... | true with result
... | refl =
  selectedTraceRetainsNativeNumericalAlignment
    rest bits ((u , a) ∷ (v , b) ∷ history)
    restAligned selectedRest refl
... | false with result
... | refl =
  selectedCons weightEq
    (selectedTraceRetainsNativeNumericalAlignment
      rest bits ((u , a) ∷ (v , b) ∷ history)
      restAligned selectedRest refl)

-- Mathematical ℤ observation of the same actual native tokens that
-- Ledger.accumulateSigned consumes, without pretending it runs a
-- native ℤ subtraction.
nativeSignedTraceSum : List Signed.SignedMagnitudeBits → ℤ
nativeSignedTraceSum [] = + 0
nativeSignedTraceSum (token ∷ rest) =
  Value.interpretNativeToken token + nativeSignedTraceSum rest

alignedSelectedSignedSum :
  (selected : List Paired.SelectedPair) →
  SelectedTokenAligned selected →
  nativeSignedTraceSum (Paired.nativeProjection selected)
    ≡ Original.replayOriginalSignedTrace
        (Paired.originalProjection selected)
alignedSelectedSignedSum [] selectedNil = refl
alignedSelectedSignedSum
  ((w , token) ∷ rest) (selectedCons weightEq tailAligned) =
  trans
    (cong (λ n → Value.interpretNativeToken token + n)
      (alignedSelectedSignedSum rest tailAligned))
    (cong (λ n → n + Original.replayOriginalSignedTrace
      (Paired.originalProjection rest)) (sym weightEq))

nativePairedScoreObservation :
  List Paired.PairedRawEdge →
  Word.BitWord →
  List (Nat × Bool) →
  Maybe ℤ
nativePairedScoreObservation paired bits history
  with Paired.selectPairedTrace paired bits history
... | nothing = nothing
... | just selected =
  just (nativeSignedTraceSum (Paired.nativeProjection selected))

-- A complete signed-ℤ score equivalence over arbitrary raw edge lists,
-- whenever the input token fields are genuinely numerically aligned.
-- The actual source gamma-native edge reader builds this invariant
-- by construction; no claim about the full graph header or tape clock.
nativeAlignedScoreSameOriginalRawSparseScore :
  (paired : List Paired.PairedRawEdge)
  (bits : Word.BitWord)
  (history : List (Nat × Bool)) →
  RawTokenAligned paired →
  nativePairedScoreObservation paired bits history
    ≡ Runtime.rawSparseScore (Paired.rawFromPairs paired) bits history
nativeAlignedScoreSameOriginalRawSparseScore paired bits history coherent
  with Paired.selectPairedTrace paired bits history
     | Paired.pairedTraceOriginalScoreExact paired bits history
... | nothing | equation rewrite sym equation = refl
... | just selected | equation rewrite sym equation =
  cong just
    (alignedSelectedSignedSum selected
      (selectedTraceRetainsNativeNumericalAlignment
        paired bits history coherent selected refl))


------------------------------------------------------------------------
-- The ACTUAL original gamma/native signed-weight parser, not a
-- caller-supplied arbitrary pair, produces numerically aligned tokens.
------------------------------------------------------------------------

originalNativeOneEdgeIsAligned :
  (word : Word.BitWord)
  (pair : Paired.PairedRawEdge)
  (suffix : Word.BitWord) →
  Stream.readOneNativePairedRawEdge word ≡ just (pair , suffix) →
  RawTokenAligned (pair ∷ [])
originalNativeOneEdgeIsAligned word pair suffix successful
  with Stream.readOneNativePairedRawEdge word in observed
... | nothing with successful
... | ()
... | just ((Graph.raw-edge u v w , token) , rest)
  with successful
... | refl
  with Runtime.endpointConsistent u true []
... | _ = alignedCons refl alignedNil

-- Original per-edge pair constructor is the only source of the
-- RawTokenAligned proof; recursion follows actual count and cursor.
nativeRawEdgeStreamIsAligned :
  (count : Nat)
  (word : Word.BitWord)
  (paired : List Paired.PairedRawEdge)
  (suffix : Word.BitWord) →
  Stream.readNativePairedRawEdges count word ≡ just (paired , suffix) →
  RawTokenAligned paired
nativeRawEdgeStreamIsAligned 0 word [] word refl = alignedNil
nativeRawEdgeStreamIsAligned (suc count) word paired suffix success
  with Stream.readOneNativePairedRawEdge word in one
... | nothing with success
... | ()
... | just (edge , rest)
  with Stream.readNativePairedRawEdges count rest in next
... | nothing with success
... | ()
... | just (edges , suffix′) with success
... | refl =
  let alignedHead = originalNativeOneEdgeIsAligned word edge rest one
      alignedTail = nativeRawEdgeStreamIsAligned
        count rest edges suffix′ next
  in combineAlignedHead alignedHead alignedTail
  where
    combineAlignedHead :
      ∀ {edge : Paired.PairedRawEdge}
        {edges : List Paired.PairedRawEdge} →
      RawTokenAligned (edge ∷ []) →
      RawTokenAligned edges →
      RawTokenAligned (edge ∷ edges)
    combineAlignedHead (alignedCons eq alignedNil) tail =
      alignedCons eq tail

-- NO arbitrary aligned-pair assumption remains: the premise is now
-- the ACTUAL parsed source raw signed-edge stream success equation.
nativeRawStreamSignedScoreSameOriginal :
  (count : Nat)
  (word : Word.BitWord)
  (paired : List Paired.PairedRawEdge)
  (suffix bits : Word.BitWord)
  (history : List (Nat × Bool)) →
  Stream.readNativePairedRawEdges count word ≡ just (paired , suffix) →
  nativePairedScoreObservation paired bits history
    ≡ Runtime.rawSparseScore (Paired.rawFromPairs paired) bits history
nativeRawStreamSignedScoreSameOriginal
  count word paired suffix bits history parsed =
  nativeAlignedScoreSameOriginalRawSparseScore
    paired bits history
    (nativeRawEdgeStreamIsAligned count word paired suffix parsed)
