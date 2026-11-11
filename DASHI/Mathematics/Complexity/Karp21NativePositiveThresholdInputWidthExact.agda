module DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdInputWidthExact where

------------------------------------------------------------------------
-- F2.2 original positive W threshold register is ACTUAL source paid.
-- Signed gamma W has its own grammar: W=0 is rejected; original
-- strictly positive gamma successor is transformed into LE bits by
-- the real readPositiveGammaLE/predecessorLE, never unary Nat.
--
-- This module bounds only the retained threshold BIT REGISTER
-- against the original word length and unchanged parser suffix.
-- No claim about temporary copies, cons cells, heap or tape time.
-- All declarations require pinned Agda 2.9 kernel adjudication.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length; reverse)
open import Data.List.Properties as ListP using (length-reverse)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact as Endpoint
import DASHI.Mathematics.Complexity.Karp21NativeSignedGammaInputChargeExact as Charge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact as Header
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Valid
import DASHI.Mathematics.Complexity.Karp21NativeWholeGraphLedgerInputBoundExact as HeaderBound
import DASHI.Mathematics.Complexity.Karp21NativeRawEdgeInputChargeExact as EdgesBound

-- The original strictly-positive gamma W parser may reject, but a
-- successful result returns an actual binary word no longer than
-- the consumed gamma successor bits, preserving the exact suffix.
originalPositiveThresholdRegisterSuffixCharge :
  (word threshold suffix : Word.BitWord) →
  Positive.readPositiveGammaLE word ≡ just (threshold , suffix) →
  length threshold + length suffix ≤ length word
originalPositiveThresholdRegisterSuffixCharge word threshold suffix parsed
  with Gamma.readGammaBinary word in gamma
... | nothing with parsed
... | ()
... | just (successor , after)
  with Positive.anyOne (Positive.predecessorLE (reverse successor))
... | false with parsed
... | ()
... | true with parsed
... | refl =
  subst
    (λ k → k + length after ≤ length word)
    (sym
      (trans
        (Endpoint.predecessorPreservesBitWidth (reverse successor))
        (ListP.length-reverse successor)))
    (Charge.actualGammaBinaryBitCharge word successor after gamma)

-- Same ACTUAL original gamma(n), gamma(m), input-fuel binary edges,
-- positive W, strict validator whole-parser input, not a caller's
-- arbitrary post-edge suffix or independently supplied threshold.
actualWholeBinaryPositiveThresholdRegisterFitsOriginalWord :
  (word n threshold : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Whole.readNativeWholeBinaryGraphWord word
    ≡ just (Whole.whole-binary-graph n edges threshold) →
  length threshold ≤ length word
actualWholeBinaryPositiveThresholdRegisterFitsOriginalWord
  word n threshold edges success
  with Header.readNativeBinaryBudgetedHeader word in header
... | nothing with success
... | ()
... | just (Header.binary-header nLE mLE afterM)
  with Whole.readBinaryRawEdgesFuel (length afterM) mLE afterM in parsedEdges
... | nothing with success
... | ()
... | just (actualEdges , afterEdges)
  with Positive.readPositiveGammaLE afterEdges in parsedW
... | nothing with success
... | ()
... | just (w , _ ∷ _) with success
... | ()
... | just (w , [])
  with Valid.validNativeBinaryEdges nLE Valid.noPrevious actualEdges
... | false with success
... | ()
... | true with success
... | refl =
  NatP.≤-trans
    (NatP.m≤m+n (length w) zero)
    (NatP.≤-trans
      (originalPositiveThresholdRegisterSuffixCharge
        afterEdges w [] parsedW)
      (NatP.≤-trans
        (NatP.≤-trans
          (NatP.m≤m+n
            (length afterEdges)
            (EdgesBound.rawEdgeSignedCharges actualEdges))
          (NatP.≤-trans
            (NatP.≤-reflexive
              (NatP.+-comm
                (length afterEdges)
                (EdgesBound.rawEdgeSignedCharges actualEdges)))
            (EdgesBound.nativeRawEdgeStreamSignedChargesFitInput
              (length afterM) mLE afterM afterEdges
              actualEdges parsedEdges)))
        (HeaderBound.budgetedNativeHeaderSuffixFitsOriginalWord
          word nLE mLE afterM header)))
