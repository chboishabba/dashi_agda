module DASHI.Mathematics.Complexity.Karp21NativeBinaryCutLedgerOriginalExact where

------------------------------------------------------------------------
-- B6 source proof: ACTUAL executable binary certificate/history
-- traversal and signed two-register ledger, not an abstract selected
-- token trace. The result is the source original rawSparseScore
-- observed in ℤ, for arbitrary initial history/ledger and all
-- malformed certificates. Only these observations use Nat/ℤ.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.List.Base using (reverse)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)
import Data.Nat.Properties as NatP
import Data.Integer.Properties as IntP
import Data.Integer.Base as Int

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as Weight
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeLedgerIntegerScoreExact as Score
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryOriginalExact as HistoryOriginal
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact as Machine
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Original

-- Same two numerical register observations as the real insertSigned.
-- These are useful independent checks of the signed arithmetic.
actualInsertSignedScore :
  (token : Signed.SignedMagnitudeBits)
  (ledger : Ledger.SignedLedger) →
  Score.observeActualNativeLedger (Ledger.insertSigned token ledger)
  ≡ Int._+_ (Score.observeActualNativeLedger ledger)
              (Weight.interpretNativeToken token)
actualInsertSignedScore (Signed.positive bits) ledger
  rewrite Ledger.insertPositiveValue bits ledger
        | Ledger.insertPositiveNegativePreserved bits ledger
        | NatP.+-comm (Ledger.positiveValue ledger)
            (Ledger.signedMagnitudeValue (Signed.positive bits)) =
  trans
    (Score.integerPositiveStep
      (Ledger.signedMagnitudeValue (Signed.positive bits))
      (Ledger.positiveValue ledger)
      (Ledger.negativeValue ledger))
    (IntP.+-comm
      (Int.+ (Ledger.signedMagnitudeValue (Signed.positive bits)))
      (Score.observeActualNativeLedger ledger))
actualInsertSignedScore (Signed.negative bits) ledger
  rewrite Ledger.insertNegativeValue bits ledger
        | Ledger.insertNegativePositivePreserved bits ledger
        | NatP.+-comm (Ledger.negativeValue ledger)
            (Ledger.signedMagnitudeValue (Signed.negative bits)) =
  trans
    (Score.integerNegativeStep
      (Ledger.signedMagnitudeValue (Signed.negative bits))
      (Ledger.positiveValue ledger)
      (Ledger.negativeValue ledger))
    (trans
      (IntP.+-comm
        (Int.- (Int.+ (Ledger.signedMagnitudeValue (Signed.negative bits))))
        (Score.observeActualNativeLedger ledger))
      (cong
        (Int._+_ (Score.observeActualNativeLedger ledger))
        (sym (Score.negativeTokenInteger bits))))

observedBinaryLedgerRun : Maybe Ledger.SignedLedger → Maybe Int.ℤ
observedBinaryLedgerRun nothing = nothing
observedBinaryLedgerRun (just ledger) =
  just (Score.observeActualNativeLedger ledger)

-- Original raw score is zero-based (right fold); the binary machine
-- is left-accumulating. We need an arbitrary ledger invariant to
-- handle the difference, not only equality at empty initial state.
originalScoreWithInitialLedger :
  Ledger.SignedLedger →
  Maybe Int.ℤ → Maybe Int.ℤ
originalScoreWithInitialLedger ledger nothing = nothing
originalScoreWithInitialLedger ledger (just signed) =
  just (Int._+_ (Score.observeActualNativeLedger ledger) signed)

nativeBinaryCutLedgerSameOriginal :
  (edges : List Edge.BinaryRawEdge)
  (certificate : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger : Ledger.SignedLedger) →
  observedBinaryLedgerRun
    (Machine.readNativeBinaryCutLedger edges certificate history ledger)
  ≡ originalScoreWithInitialLedger ledger
      (Original.rawSparseScore
        (Edge.originalEdgeListObservation edges)
        certificate (History.observedBinaryHistory history))
nativeBinaryCutLedgerSameOriginal [] [] history ledger =
  cong just (sym (IntP.+-identityʳ (Score.observeActualNativeLedger ledger)))
nativeBinaryCutLedgerSameOriginal [] (_ ∷ _) history ledger = refl
nativeBinaryCutLedgerSameOriginal (_ ∷ _) [] history ledger = refl
nativeBinaryCutLedgerSameOriginal (_ ∷ _) (_ ∷ []) history ledger = refl
nativeBinaryCutLedgerSameOriginal
  (Edge.binary-edge u v token ∷ rest)
  (a ∷ b ∷ bits) history ledger
  rewrite
    HistoryOriginal.nativeBinaryEndpointHistorySameOriginal u a history
  | HistoryOriginal.nativeBinaryEndpointHistorySameOriginal v b history
  with Original.endpointConsistent
      (Value.valueLE u)
      a (History.observedBinaryHistory history)
     | Original.endpointConsistent
      (Value.valueLE v)
      b (History.observedBinaryHistory history)
... | false | _ = refl
... | true | false = refl
... | true | true
  with Boolean.boolEqual a b
... | true
  rewrite nativeBinaryCutLedgerSameOriginal rest bits
    (History.recordBinaryEndpointPair u v a b history) ledger
  with Original.rawSparseScore
    (Edge.originalEdgeListObservation rest) bits
    (History.observedBinaryHistory
      (History.recordBinaryEndpointPair u v a b history))
... | nothing = refl
... | just tail = refl
... | false
  rewrite nativeBinaryCutLedgerSameOriginal rest bits
    (History.recordBinaryEndpointPair u v a b history)
    (Ledger.insertSigned token ledger)
  with Original.rawSparseScore
    (Edge.originalEdgeListObservation rest) bits
    (History.observedBinaryHistory
      (History.recordBinaryEndpointPair u v a b history))
... | nothing = refl
... | just tail =
  cong just
    (trans
      (cong (λ z → Int._+_ z tail)
        (actualInsertSignedScore token ledger))
      (IntP.+-assoc
        (Score.observeActualNativeLedger ledger)
        (Weight.interpretNativeToken token)
        tail))
