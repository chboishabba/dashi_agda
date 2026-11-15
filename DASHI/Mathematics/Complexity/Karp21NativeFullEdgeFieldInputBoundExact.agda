module DASHI.Mathematics.Complexity.Karp21NativeFullEdgeFieldInputBoundExact where

------------------------------------------------------------------------
-- F2.2: ALL THREE ORIGINAL BINARY RAW EDGE REGISTER FIELDS are
-- bounded by the actual source bits consumed by the same parser:
-- gamma(u), gamma(v), signed gamma(w).
--
-- The completed raw edge stream stores NO copied numerical magnitudes
-- whose total binary bit-register widths exceed its original
-- gamma-coded input length. This bounds stored bit registers, NOT
-- Lisp/list cell/pointer overhead, duplicated parse buffers or the
-- cost of physically moving the Turing tape head.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length; reverse)
open import Data.List.Properties as ListP using (length-reverse)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; subst; trans; sym)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact as Endpoint
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Width
import DASHI.Mathematics.Complexity.Karp21NativeSignedGammaInputChargeExact as Token

-- Actual per-edge binary register capacity, before any original Nat
-- or integer observation. The parenthesisation is explicit.
binaryRawEdgeRegisterCharge : Edge.BinaryRawEdge → Nat
binaryRawEdgeRegisterCharge (Edge.binary-edge u v signed) =
  length u + (length v + Width.signedTokenBitCharge signed)

allBinaryRawEdgeRegisterCharges : List Edge.BinaryRawEdge → Nat
allBinaryRawEdgeRegisterCharges [] = zero
allBinaryRawEdgeRegisterCharges (edge ∷ rest) =
  binaryRawEdgeRegisterCharge edge +
  allBinaryRawEdgeRegisterCharges rest

-- The gamma(n+1) predecessor is a representation conversion only:
-- its binary register length is exactly the successor payload length.
actualUnsignedEndpointRegisterFitsInput :
  (word endpoint suffix : Word.BitWord) →
  Endpoint.readGammaNatLE word ≡ just (endpoint , suffix) →
  length endpoint + length suffix ≤ length word
actualUnsignedEndpointRegisterFitsInput word endpoint suffix accepted
  with Gamma.readGammaBinary word in parsed
... | nothing with accepted
... | ()
... | just (successor , after) with accepted
... | refl =
  subst
    (λ k → k + length after ≤ length word)
    (sym
      (trans
        (Endpoint.predecessorPreservesBitWidth (reverse successor))
        (ListP.length-reverse successor)))
    (Token.actualGammaBinaryBitCharge word successor after parsed)

-- The exact arithmetic reassociation required to charge the
-- original u/v/w fields against their three consumed source pieces.
threeFieldChargeReassociate :
  (u v w s : Nat) →
  (u + (v + w)) + s ≡ u + (v + (w + s))
threeFieldChargeReassociate u v w s =
  solve (u ∷ v ∷ w ∷ s ∷ [])

-- This is THE REAL signed raw edge reader and its exact returned
-- suffix, not a numerical reconstruction of the decoded edge.
oneOriginalBinaryEdgeAllRegisterFieldsFitInput :
  (word suffix : Word.BitWord)
  (edge : Edge.BinaryRawEdge) →
  Edge.readOneBinaryRawEdge word ≡ just (edge , suffix) →
  binaryRawEdgeRegisterCharge edge + length suffix ≤ length word
oneOriginalBinaryEdgeAllRegisterFieldsFitInput word suffix edge accepted
  with Endpoint.readGammaNatLE word in first
... | nothing with accepted
... | ()
... | just (u , afterU)
  with Endpoint.readGammaNatLE afterU in second
... | nothing with accepted
... | ()
... | just (v , afterV)
  with Signed.readSignedBinary afterV in signed
... | nothing with accepted
... | ()
... | just (token , afterW) with accepted
... | refl =
  NatP.≤-trans
    (NatP.≤-reflexive
      (threeFieldChargeReassociate
        (length u) (length v)
        (Width.signedTokenBitCharge token)
        (length afterW)))
    (NatP.≤-trans
      (NatP.+-mono-≤ NatP.≤-refl
        (NatP.+-mono-≤ NatP.≤-refl
          (Token.nativeSignedGammaConsumesItsBitCharge
            afterV afterW token signed)))
      (NatP.≤-trans
        (NatP.+-mono-≤ NatP.≤-refl
          (actualUnsignedEndpointRegisterFitsInput
            afterU v afterV second))
        (actualUnsignedEndpointRegisterFitsInput
          word u afterU first)))

-- Any successful ACTUAL structurally fuel-bounded binary-m reader
-- stores at most as many total u,v,w REGISTER BITS as the original
-- raw-edge source input, even with malformed prefixes elsewhere.
nativeRawEdgeStreamAllRegisterFieldsFitInput :
  (fuel : Nat)
  (mLE word suffix : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Whole.readBinaryRawEdgesFuel fuel mLE word
    ≡ just (edges , suffix) →
  allBinaryRawEdgeRegisterCharges edges + length suffix
    ≤ length word
nativeRawEdgeStreamAllRegisterFieldsFitInput zero mLE word suffix edges accepted
  with Positive.anyOne mLE
... | false with accepted
... | refl = NatP.≤-refl
... | true with accepted
... | ()
nativeRawEdgeStreamAllRegisterFieldsFitInput (suc fuel) mLE word suffix edges accepted
  with Positive.anyOne mLE
... | false with accepted
... | refl = NatP.≤-refl
... | true with Edge.readOneBinaryRawEdge word in first
... | nothing with accepted
... | ()
... | just (edge , rest)
  with Whole.readBinaryRawEdgesFuel fuel
    (Positive.predecessorLE mLE) rest in continuation
... | nothing with accepted
... | ()
... | just (following , after) with accepted
... | refl =
  NatP.≤-trans
    (NatP.≤-reflexive
      (NatP.+-assoc
        (binaryRawEdgeRegisterCharge edge)
        (allBinaryRawEdgeRegisterCharges following)
        (length after)))
    (NatP.≤-trans
      (NatP.+-mono-≤ NatP.≤-refl
        (nativeRawEdgeStreamAllRegisterFieldsFitInput
          fuel (Positive.predecessorLE mLE)
          rest after following continuation))
      (oneOriginalBinaryEdgeAllRegisterFieldsFitInput
        word rest edge first))
