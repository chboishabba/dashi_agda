module DASHI.Mathematics.Complexity.Karp21FractranPairedBinaryTraceExact where

------------------------------------------------------------------------
-- Original N21 edges + native signed tokens in a SINGLE aligned trace.
--
-- Each row holds the actual original Graph.RawEdge and a corresponding
-- native SignedMagnitudeBits. Selecting cut contributions checks the
-- literal Runtime.endpointConsistent / boolEqual and original 2-bit
-- witness. The original signed-ℤ trace is recovered by projection.
--
-- This is the exact shape needed for the subsequent signed-gamma
-- VALUE-and-SUFFIX weld. Merely pairing does not prove that the binary
-- token denotes the original signed weight; no such claim is made.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base using (ℤ)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21FractranOriginalRawTraceReplayExact as Original
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger

PairedRawEdge : Set
PairedRawEdge = Graph.RawEdge × Signed.SignedMagnitudeBits

SelectedPair : Set
SelectedPair = ℤ × Signed.SignedMagnitudeBits

rawFromPairs : List PairedRawEdge → List Graph.RawEdge
rawFromPairs [] = []
rawFromPairs ((edge , binary) ∷ rest) =
  edge ∷ rawFromPairs rest

-- The paired trace is a full original-edge-list traversal, not a
-- generic list-compression proxy. Endpoint history is extended in
-- precisely the same order as the original rawSparseScore definition.
selectPairedTrace :
  List PairedRawEdge →
  Word.BitWord →
  List (Nat × Bool) →
  Maybe (List SelectedPair)
selectPairedTrace [] [] history = just []
selectPairedTrace [] (_ ∷ _) history = nothing
selectPairedTrace (_ ∷ _) [] history = nothing
selectPairedTrace (_ ∷ _) (_ ∷ []) history = nothing
selectPairedTrace
  ((Graph.raw-edge u v w , native) ∷ rest)
  (a ∷ b ∷ bits) history
  with Runtime.endpointConsistent u a history
     | Runtime.endpointConsistent v b history
... | false | _ = nothing
... | true | false = nothing
... | true | true
  with selectPairedTrace
    rest bits ((u , a) ∷ (v , b) ∷ history)
... | nothing = nothing
... | just selected with Boolean.boolEqual a b
...   | true = just selected
...   | false = just ((w , native) ∷ selected)

originalProjection : List SelectedPair → List ℤ
originalProjection [] = []
originalProjection ((weight , token) ∷ rest) =
  weight ∷ originalProjection rest

nativeProjection :
  List SelectedPair → List Signed.SignedMagnitudeBits
nativeProjection [] = []
nativeProjection ((weight , token) ∷ rest) =
  token ∷ nativeProjection rest

projectOriginalMaybe :
  Maybe (List SelectedPair) → Maybe (List ℤ)
projectOriginalMaybe nothing = nothing
projectOriginalMaybe (just selected) =
  just (originalProjection selected)

-- Crucially this theorem needs NO fabricated binary-value equality.
-- It transports EXACT original selected signed weights and rejection.
pairedTraceProjectsToOriginal :
  (paired : List PairedRawEdge)
  (certificate : Word.BitWord)
  (history : List (Nat × Bool)) →
  projectOriginalMaybe
    (selectPairedTrace paired certificate history)
    ≡ Original.rawSelectedTrace
        (rawFromPairs paired) certificate history
pairedTraceProjectsToOriginal [] [] history = refl
pairedTraceProjectsToOriginal [] (_ ∷ _) history = refl
pairedTraceProjectsToOriginal (_ ∷ _) [] history = refl
pairedTraceProjectsToOriginal (_ ∷ _) (_ ∷ []) history = refl
pairedTraceProjectsToOriginal
  ((Graph.raw-edge u v w , native) ∷ rest)
  (a ∷ b ∷ bits) history
  with Runtime.endpointConsistent u a history
     | Runtime.endpointConsistent v b history
... | false | _ = refl
... | true | false = refl
... | true | true
  with selectPairedTrace
    rest bits ((u , a) ∷ (v , b) ∷ history)
     | pairedTraceProjectsToOriginal
         rest bits ((u , a) ∷ (v , b) ∷ history)
... | nothing | induction rewrite sym induction = refl
... | just selected | induction with Boolean.boolEqual a b
...   | true rewrite sym induction = refl
...   | false rewrite sym induction = refl

-- The paired representation therefore reconstructs the actual
-- original optional signed score on EVERY aligned raw edge list.
pairedTraceOriginalScoreExact :
  (paired : List PairedRawEdge)
  (certificate : Word.BitWord)
  (history : List (Nat × Bool)) →
  Original.decodeTraceScore
    (projectOriginalMaybe
      (selectPairedTrace paired certificate history))
    ≡ Runtime.rawSparseScore
        (rawFromPairs paired) certificate history
pairedTraceOriginalScoreExact paired certificate history
  rewrite pairedTraceProjectsToOriginal paired certificate history =
  Original.rawSelectedTraceRebuildsOriginalScore
    (rawFromPairs paired) certificate history

------------------------------------------------------------------------
-- Fully executable native two-lane score ledger *after* the actual
-- original endpoint/2m certificate history guards succeed. This
-- reproduces success/rejection exactly. Numerical score agreement
-- remains gated on source signed-gamma token value identity.
------------------------------------------------------------------------

nativePairedLedger :
  List PairedRawEdge →
  Word.BitWord →
  List (Nat × Bool) →
  Maybe Ledger.SignedLedger
nativePairedLedger paired bits history
  with selectPairedTrace paired bits history
... | nothing = nothing
... | just selected =
  just (Ledger.accumulateSigned
    (nativeProjection selected) Ledger.emptyLedger)

maybeAccepted : {A : Set} → Maybe A → Bool
maybeAccepted nothing = false
maybeAccepted (just _) = true

nativePairedLedgerSameOriginalRejection :
  (paired : List PairedRawEdge)
  (bits : Word.BitWord)
  (history : List (Nat × Bool)) →
  maybeAccepted (nativePairedLedger paired bits history)
    ≡ maybeAccepted
        (Runtime.rawSparseScore
          (rawFromPairs paired) bits history)
nativePairedLedgerSameOriginalRejection paired bits history
  with selectPairedTrace paired bits history
     | pairedTraceOriginalScoreExact paired bits history
... | nothing | equation rewrite sym equation = refl
... | just selected | equation rewrite sym equation = refl
