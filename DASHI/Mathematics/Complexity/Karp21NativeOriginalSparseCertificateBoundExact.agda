module DASHI.Mathematics.Complexity.Karp21NativeOriginalSparseCertificateBoundExact where

------------------------------------------------------------------------
-- G2 ORIGINAL N21 sparse certificate length receipt (SOURCE ONLY).
--
-- This is not a conditional arbitrary certificate constructor:
-- it observes the successful ACTUAL binary sparse verifier cursor
-- and original graph parser, proving exactly TWO original cut-label
-- bits per source raw edge and a bit-length upper bound in the
-- original gamma-encoded graph word. No Nat-valued vertex decoding
-- runs in the executable verifier.
--
-- Not by itself PR.InNP: actual physical bit-TM clock and pinned
-- Agda 2.9 kernel acceptance remain required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.List.Base using (length)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointHistoryExact as History
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Graph
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryVerifierExact as Verifier
import DASHI.Mathematics.Complexity.Karp21NativeRawEdgeInputChargeExact as Input
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Width
import DASHI.Mathematics.Complexity.Karp21NativeWholeGraphEdgeFieldWordBoundExact as EdgeWord
import DASHI.Mathematics.Complexity.Karp21NativeFullEdgeFieldInputBoundExact as Fields

-- Each ACTUAL signed gamma edge has at least one literal original
-- sign/magnitude successor bit. Hence its original source edge-stream
-- bit-charge is >= the number of parsed raw-edge records.
numberOfEdgesAtMostSignedTokenBits :
  (edges : List Edge.BinaryRawEdge) →
  length edges ≤ Input.rawEdgeSignedCharges edges
numberOfEdgesAtMostSignedTokenBits [] = z≤n
numberOfEdgesAtMostSignedTokenBits
  (Edge.binary-edge u v (Signed.positive magnitude) ∷ rest) =
  s≤s
    (NatP.≤-trans
      (numberOfEdgesAtMostSignedTokenBits rest)
      (NatP.≤-trans
        (NatP.m≤m+n
          (Input.rawEdgeSignedCharges rest) (length magnitude))
        (NatP.≤-reflexive
          (NatP.+-comm
            (Input.rawEdgeSignedCharges rest) (length magnitude)))))
numberOfEdgesAtMostSignedTokenBits
  (Edge.binary-edge u v (Signed.negative magnitude) ∷ rest) =
  s≤s
    (NatP.≤-trans
      (numberOfEdgesAtMostSignedTokenBits rest)
      (NatP.≤-trans
        (NatP.m≤m+n
          (Input.rawEdgeSignedCharges rest) (length magnitude))
        (NatP.≤-reflexive
          (NatP.+-comm
            (Input.rawEdgeSignedCharges rest) (length magnitude)))))

-- The whole parsed original binary graph word is the unique source of
-- all edge tokens; its bit length bounds the number of source edges.
actualOriginalGraphEdgeCountAtMostInputBits :
  (word n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Graph.readNativeWholeBinaryGraphWord word
    ≡ just (Graph.whole-binary-graph n edges threshold) →
  length edges ≤ length word
actualOriginalGraphEdgeCountAtMostInputBits word n threshold edges accepted =
  NatP.≤-trans
    (numberOfEdgesAtMostSignedTokenBits edges)
    (NatP.≤-trans
      (rawSignedTokenChargesAtMostAllFields edges)
      (EdgeWord.actualWholeBinaryGraphEdgeFieldWidthAtMostOriginalWord
        word n threshold edges accepted))
  where
    rawSignedTokenChargesAtMostAllFields :
      (es : List Edge.BinaryRawEdge) →
      Input.rawEdgeSignedCharges es
        ≤ Fields.allBinaryRawEdgeRegisterCharges es
    rawSignedTokenChargesAtMostAllFields [] = z≤n
    rawSignedTokenChargesAtMostAllFields
      (Edge.binary-edge u v token ∷ rest) =
      NatP.+-mono-≤
        (NatP.≤-trans
          (NatP.m≤m+n
            (Width.signedTokenBitCharge token)
            (length u + length v))
          (NatP.≤-reflexive
            (trans
              (NatP.+-comm
                (Width.signedTokenBitCharge token)
                (length u + length v))
              (NatP.+-assoc
                (length u) (length v)
                (Width.signedTokenBitCharge token)))))
        (rawSignedTokenChargesAtMostAllFields rest)

-- This source cursor is THE ACTUAL original-word binary sparse
-- verifier: success requires two cut-label bits for each edge and
-- refuses ALL extra bits at the end, irrespective of signed score.
nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge :
  (edges : List Edge.BinaryRawEdge)
  (certificate : Word.BitWord)
  (history : History.BinaryEndpointHistory)
  (ledger result : Ledger.SignedLedger) →
  Verifier.readNativeBinaryCutLedger edges certificate history ledger
    ≡ just result →
  length certificate ≡ length edges + length edges
nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
  [] [] history ledger result success
  with success
... | refl = refl
nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
  [] (_ ∷ _) history ledger result ()
nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
  (_ ∷ _) [] history ledger result ()
nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
  (_ ∷ _) (_ ∷ []) history ledger result ()
nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
  (Edge.binary-edge u v token ∷ rest)
  (a ∷ b ∷ certificate) history ledger result success
  with History.endpointConsistentBinary u a history
     | History.endpointConsistentBinary v b history
... | false | _ with success
... | ()
... | true | false with success
... | ()
... | true | true with Boolean.boolEqual a b
... | true
  rewrite NatP.+-suc (length rest) (length rest) =
  cong suc (cong suc
    (nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
      rest certificate
      (History.recordBinaryEndpointPair u v a b history)
      ledger result success))
... | false
  rewrite NatP.+-suc (length rest) (length rest) =
  cong suc (cong suc
    (nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
      rest certificate
      (History.recordBinaryEndpointPair u v a b history)
      (Ledger.insertSigned token ledger) result success))

-- G2.1: literal completed verifier input. The graph parser is the
-- SAME original source word and the sparse ledger cursor is the
-- executable same-word selected binary path. It may return either
-- original signed-threshold outcome; the size bound is independent
-- of the final score comparison.
actualOriginalN21CertificateBitsBound :
  (word certificate n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge)
  (result : Ledger.SignedLedger) →
  Graph.readNativeWholeBinaryGraphWord word
    ≡ just (Graph.whole-binary-graph n edges threshold) →
  Verifier.readNativeBinaryCutLedger edges certificate []
    Ledger.emptyLedger ≡ just result →
  length certificate ≤ length word + length word
actualOriginalN21CertificateBitsBound
  word certificate n threshold edges result parsed success =
  NatP.≤-trans
    (NatP.≤-reflexive
      (nativeSuccessfulSparseCursorConsumesExactlyTwoBitsPerEdge
        edges certificate [] Ledger.emptyLedger result success))
    (NatP.+-mono-≤
      (actualOriginalGraphEdgeCountAtMostInputBits
        word n threshold edges parsed)
      (actualOriginalGraphEdgeCountAtMostInputBits
        word n threshold edges parsed))
