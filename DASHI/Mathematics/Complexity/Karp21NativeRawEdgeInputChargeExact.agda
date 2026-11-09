module DASHI.Mathematics.Complexity.Karp21NativeRawEdgeInputChargeExact where

------------------------------------------------------------------------
-- F2: ORIGINAL N21 ACTUAL RAW GRAPH INPUT PAYS SIGNED TOKEN WIDTHS.
--
-- Not an abstract selected-token-list assumption: consume exactly
-- Endpoint.readGammaNatLE (u), Endpoint.readGammaNatLE (v),
-- Signed.readSignedBinary (w), then the actual binary-count/fuel
-- raw-edge parser and its unchanged suffix.
--
-- All successfully parsed signed weight magnitudes together, plus
-- the final parser suffix, fit inside the ACTUAL source edge word
-- supplied after gamma(n),gamma(m). This is the key F2 connection
-- between source input length and subsequent two-lane ledger growth.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact as Endpoint
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointRawEdgeStreamExact as Edge
import DASHI.Mathematics.Complexity.Karp21NativeWholeBinaryGraphRuntimeExact as Whole
import DASHI.Mathematics.Complexity.Karp21NativeSignedLedgerWidthBudgetExact as Charge
import DASHI.Mathematics.Complexity.Karp21NativeSignedGammaInputChargeExact as Token

-- Proof-side measure of the token registers in the ACTUAL parsed
-- binary raw-edge list. The executable parser itself is unchanged.
edgeSignedCharge : Edge.BinaryRawEdge → Nat
edgeSignedCharge (Edge.binary-edge u v signed) =
  Charge.signedTokenBitCharge signed

rawEdgeSignedCharges : List Edge.BinaryRawEdge → Nat
rawEdgeSignedCharges [] = zero
rawEdgeSignedCharges (edge ∷ rest) =
  edgeSignedCharge edge + rawEdgeSignedCharges rest

-- Any accepted gamma(n) successor/suffix must actually shorten the
-- unparsed source word (or preserve length for a vacuous bound).
gammaSuffixLengthBound :
  (word successor suffix : Word.BitWord) →
  Gamma.readGammaBinary word ≡ just (successor , suffix) →
  length suffix ≤ length word
gammaSuffixLengthBound word successor suffix accepted =
  NatP.≤-trans
    (subst
      (λ k → length suffix ≤ k)
      (NatP.+-comm (length suffix) (length successor))
      (NatP.m≤m+n (length suffix) (length successor)))
    (Token.actualGammaBinaryBitCharge word successor suffix accepted)

-- Original unsigned reader is merely gamma-successor decoding plus
-- a binary predecessor. Thus it preserves suffix consumption.
unsignedEndpointSuffixLengthBound :
  (word endpoint suffix : Word.BitWord) →
  Endpoint.readGammaNatLE word ≡ just (endpoint , suffix) →
  length suffix ≤ length word
unsignedEndpointSuffixLengthBound word endpoint suffix accepted
  with Gamma.readGammaBinary word in parsed
... | nothing with accepted
... | ()
... | just (successor , after) with accepted
... | refl = gammaSuffixLengthBound word successor after parsed

-- Every ACTUAL original gamma(u),gamma(v),signed gamma(w) triple
-- pays the binary signed weight's register charge in the input.
oneOriginalBinaryEdgeSignedChargeBound :
  (word suffix : Word.BitWord)
  (edge : Edge.BinaryRawEdge) →
  Edge.readOneBinaryRawEdge word ≡ just (edge , suffix) →
  edgeSignedCharge edge + length suffix ≤ length word
oneOriginalBinaryEdgeSignedChargeBound word suffix edge accepted
  with Endpoint.readGammaNatLE word in first
... | nothing with accepted
... | ()
... | just (u , afterU)
  with Endpoint.readGammaNatLE afterU in second
... | nothing with accepted
... | ()
... | just (v , afterV)
  with Signed.readSignedBinary afterV in weight
... | nothing with accepted
... | ()
... | just (token , afterW) with accepted
... | refl =
  NatP.≤-trans
    (Token.nativeSignedGammaConsumesItsBitCharge
      afterV afterW token weight)
    (NatP.≤-trans
      (unsignedEndpointSuffixLengthBound afterU v afterV second)
      (unsignedEndpointSuffixLengthBound word u afterU first))

-- The original real binary-decrement raw-edge parser has no
-- additional source of signed magnitude bytes: on successful parse
-- their aggregate charge, together with the returned suffix,
-- cannot exceed the input edge-stream length.
nativeRawEdgeStreamSignedChargesFitInput :
  (fuel : Nat)
  (mLE word suffix : Word.BitWord)
  (edges : List Edge.BinaryRawEdge) →
  Whole.readBinaryRawEdgesFuel fuel mLE word
    ≡ just (edges , suffix) →
  rawEdgeSignedCharges edges + length suffix ≤ length word
nativeRawEdgeStreamSignedChargesFitInput zero mLE word suffix edges accepted
  with Positive.anyOne mLE
... | false with accepted
... | refl = NatP.≤-refl
... | true with accepted
... | ()
nativeRawEdgeStreamSignedChargesFitInput (suc fuel) mLE word suffix edges accepted
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
        (edgeSignedCharge edge)
        (rawEdgeSignedCharges following)
        (length after)))
    (NatP.≤-trans
      (NatP.+-mono-≤ NatP.≤-refl
        (nativeRawEdgeStreamSignedChargesFitInput
          fuel (Positive.predecessorLE mLE) rest after
          following continuation))
      (oneOriginalBinaryEdgeSignedChargeBound
        word rest edge first))

-- A source-successful WHOLE binary graph has been assembled from
-- a raw-edge list already bounded by its input source word; this
-- theorem is the core component needed for the global P0-F2 receipt.
