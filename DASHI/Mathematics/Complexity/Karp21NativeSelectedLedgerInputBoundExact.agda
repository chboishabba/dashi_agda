module DASHI.Mathematics.Complexity.Karp21NativeSelectedLedgerInputBoundExact where

------------------------------------------------------------------------
-- F2.1: source ORIGINAL edge-stream bit length bounds the final
-- real signed TWO-LANE LEDGER for any ordered selection of actually
-- parsed binary signed edges.
--
-- No independent token magnitudes: the SelectedFromParsedEdges
-- witness retains token identity/order from ACTUAL BinaryRawEdge
-- records output by the input-bounded source binary m parser.
-- Source theorem still needs a producer of this witness from the
-- actual Compiled.directStep first-enabled event emitter.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21BinaryNativeSignedLedgerExact as Ledger
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Width
import DASHI.Mathematics.Complexity.Karp21NativeRawEdgeInputChargeExact as Input

-- Exactly the original source edge order and EXACT token identity.
-- Skipping an unselected original edge consumes no signed token.
data SelectedFromParsedEdges :
  List Signed.SignedMagnitudeBits →
  List Edge.BinaryRawEdge → Set where
  selected-empty : SelectedFromParsedEdges [] []
  selected-skip :
    ∀ {tokens edges u v w} →
    SelectedFromParsedEdges tokens edges →
    SelectedFromParsedEdges tokens
      (Edge.binary-edge u v w ∷ edges)
  selected-take :
    ∀ {tokens edges u v w} →
    SelectedFromParsedEdges tokens edges →
    SelectedFromParsedEdges (w ∷ tokens)
      (Edge.binary-edge u v w ∷ edges)

-- The original gamma raw-edge token charges dominate ANY selected
-- substream in their actual chronological order.
selectedActualTokenChargesAtMostRawEdges :
  ∀ {tokens edges} →
  SelectedFromParsedEdges tokens edges →
  Width.selectedTokenCharges tokens ≤ Input.rawEdgeSignedCharges edges
selectedActualTokenChargesAtMostRawEdges selected-empty =
  NatP.≤-refl
selectedActualTokenChargesAtMostRawEdges
  {tokens} {Edge.binary-edge u v w ∷ edges}
  (selected-skip selection) =
  NatP.≤-trans
    (selectedActualTokenChargesAtMostRawEdges selection)
    (NatP.≤-trans
      (NatP.m≤m+n (Input.rawEdgeSignedCharges edges)
        (Width.signedTokenBitCharge w))
      (NatP.≤-reflexive
        (NatP.+-comm
          (Input.rawEdgeSignedCharges edges)
          (Width.signedTokenBitCharge w))))
selectedActualTokenChargesAtMostRawEdges
  (selected-take {w = w} selection) =
  NatP.+-mono-≤ NatP.≤-refl
    (selectedActualTokenChargesAtMostRawEdges selection)

-- Nothing can grow the selected token charges beyond the ACTUAL
-- original raw-edge word's measured bit length.
selectedActualTokenChargesFitOriginalWord :
  ∀ {tokens edges}
  (selection : SelectedFromParsedEdges tokens edges)
  (word suffix mLE : Word.BitWord)
  (fuel : Nat) →
  Whole.readBinaryRawEdgesFuel fuel mLE word
    ≡ Data.Maybe.Base.just (edges , suffix) →
  Width.selectedTokenCharges tokens ≤ length word
selectedActualTokenChargesFitOriginalWord
  {tokens} {edges} selected word suffix mLE fuel parsed =
  NatP.≤-trans
    (selectedActualTokenChargesAtMostRawEdges selected)
    (NatP.≤-trans
      (NatP.m≤m+n
        (Input.rawEdgeSignedCharges edges) (length suffix))
      (Input.nativeRawEdgeStreamSignedChargesFitInput
        fuel mLE word suffix edges parsed))

-- The actual two-lane signed ripple accumulator final register width
-- is now bounded by INITIAL P+N bits + ORIGINAL GRAPH EDGE INPUT
-- length, not an unconstrained list of source-token magnitudes.
actualSelectedLedgerWidthFromOriginalInput :
  ∀ {tokens edges}
  (selection : SelectedFromParsedEdges tokens edges)
  (word suffix mLE : Word.BitWord)
  (fuel : Nat)
  (ledger : Ledger.SignedLedger) →
  Whole.readBinaryRawEdgesFuel fuel mLE word
    ≡ Data.Maybe.Base.just (edges , suffix) →
  Width.actualLedgerWidth (Ledger.accumulateSigned tokens ledger)
    ≤ Width.actualLedgerWidth ledger + length word
actualSelectedLedgerWidthFromOriginalInput
  {tokens} {edges} selected word suffix mLE fuel ledger parsed =
  NatP.≤-trans
    (Width.actualAccumulateSignedWidthBudget tokens ledger)
    (NatP.+-mono-≤ NatP.≤-refl
      (selectedActualTokenChargesFitOriginalWord
        selected word suffix mLE fuel parsed))
