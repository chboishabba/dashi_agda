module DASHI.Analysis.RHQuartic128Monster3BSSPSignedC2IntertwinerExact where

------------------------------------------------------------------------
-- ORIGINAL RH 128 BINARY COEFFICIENT -> ACTUAL EXISTING MONSTER-3B X6
--                                   x SIGNED SSP / FRACTRAN C2 CARRIER
--
-- SOURCE-FAITHFUL OWNERS, DISTINCT SEMANTIC ROLES
--   RH original 128 = 16 (physical) x 2 (Fourier) x 4 (origin)
--   RHQuartic128SevenBitFaceCechGluingExact: seven-bit BIDI chart
--   Monster3BFiniteHeisenbergGeneratorsExact: X6=F_3^6, negate3
--   SignedSSPFRACTRANWeaveExact: signed multiplicity negation
--
-- New finite theorem: chosen embedding
--   2^7 -> (F_3^6) x SignedMultiplicity
-- using the six nonzero trits (neg,pos) and one signed 1-unit.
-- Its left inverse is literal; the 7-bit simultaneous complement
-- INTERTWINES coordinate negation with signed multiplicity negation.
--
-- Important nonpromotion:
--   * This is NOT a Monster group representation/action theorem.
--   * Source original RH coefficient weight does NOT stay invariant under
--     this complement: w(b) w(complement b) = 128, not w(b)=w(complement b).
--   * The nonzero binary image does NOT include the ternary neutral centre.
--   * No selected-W / Gamma / paperFT / zeta-zero action is implemented.
--   * No Fricke/Dirichlet/physical wave involution is identified.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Analysis.RHQuartic128SevenBitFaceCechGluingExact as RH128
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Algebra.Trit as Trit

flipBit : Bool → Bool
flipBit false = true
flipBit true = false

flipBitTwice : (bit : Bool) → flipBit (flipBit bit) ≡ bit
flipBitTwice false = refl
flipBitTwice true = refl

bitTrit : Bool → Trit.Trit
bitTrit false = Trit.neg
bitTrit true = Trit.pos

tritBit : Trit.Trit → Bool
tritBit Trit.neg = false
tritBit Trit.zer = false
tritBit Trit.pos = true

tritBitRoundTrip : (bit : Bool) → tritBit (bitTrit bit) ≡ bit
tritBitRoundTrip false = refl
tritBitRoundTrip true = refl

bitSigned : Bool → SSP.SignedMultiplicity
bitSigned false = SSP.negativeMultiplicity 1
bitSigned true = SSP.positiveMultiplicity 1

signedBit : SSP.SignedMultiplicity → Bool
signedBit (SSP.negativeMultiplicity n) = false
signedBit SSP.zeroMultiplicity = false
signedBit (SSP.positiveMultiplicity n) = true

signedBitRoundTrip : (bit : Bool) → signedBit (bitSigned bit) ≡ bit
signedBitRoundTrip false = refl
signedBitRoundTrip true = refl

tritFlipCommutes :
  (bit : Bool) →
  bitTrit (flipBit bit) ≡ H.negate3 (bitTrit bit)
tritFlipCommutes false = refl
tritFlipCommutes true = refl

signedFlipCommutes :
  (bit : Bool) →
  bitSigned (flipBit bit) ≡ SSP.negateMultiplicity (bitSigned bit)
signedFlipCommutes false = refl
signedFlipCommutes true = refl

SignedX6 : Set
SignedX6 = H.X6 × SSP.SignedMultiplicity

encode :
  RH128.BinarySeven → SignedX6
encode (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1) =
  H.x6 (bitTrit a0) (bitTrit a1) (bitTrit a2)
       (bitTrit a3) (bitTrit b0) (bitTrit c0) ,
  bitSigned c1

decode :
  SignedX6 → RH128.BinarySeven
decode (H.x6 a0 a1 a2 a3 b0 c0 , c1) =
  RH128.binarySeven
    (tritBit a0) (tritBit a1) (tritBit a2)
    (tritBit a3) (tritBit b0) (tritBit c0)
    (signedBit c1)

decodeAfterEncode :
  (state : RH128.BinarySeven) →
  decode (encode state) ≡ state
decodeAfterEncode (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1)
  rewrite tritBitRoundTrip a0
        | tritBitRoundTrip a1
        | tritBitRoundTrip a2
        | tritBitRoundTrip a3
        | tritBitRoundTrip b0
        | tritBitRoundTrip c0
        | signedBitRoundTrip c1 = refl

reverseEq : {A : Set} {x y : A} → x ≡ y → y ≡ x
reverseEq refl = refl

transEq : {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

mapEq : {A B : Set} (f : A → B) {x y : A} →
  x ≡ y → f x ≡ f y
mapEq f refl = refl

encodeInjective :
  {left right : RH128.BinarySeven} →
  encode left ≡ encode right → left ≡ right
encodeInjective {left} {right} equality =
  transEq
    (reverseEq (decodeAfterEncode left))
    (transEq (mapEq decode equality) (decodeAfterEncode right))

complement :
  RH128.BinarySeven → RH128.BinarySeven
complement (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1) =
  RH128.binarySeven
    (flipBit a0) (flipBit a1) (flipBit a2) (flipBit a3)
    (flipBit b0) (flipBit c0) (flipBit c1)

complementTwice :
  (state : RH128.BinarySeven) →
  complement (complement state) ≡ state
complementTwice (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1)
  rewrite flipBitTwice a0 | flipBitTwice a1
        | flipBitTwice a2 | flipBitTwice a3
        | flipBitTwice b0 | flipBitTwice c0
        | flipBitTwice c1 = refl

invertX6 : H.X6 → H.X6
invertX6 (H.x6 a b c d e f) =
  H.x6 (H.negate3 a) (H.negate3 b) (H.negate3 c)
       (H.negate3 d) (H.negate3 e) (H.negate3 f)

invertSignedX6 : SignedX6 → SignedX6
invertSignedX6 (state , signed) =
  invertX6 state , SSP.negateMultiplicity signed

encodeIntertwinesSignedInversion :
  (state : RH128.BinarySeven) →
  encode (complement state) ≡ invertSignedX6 (encode state)
encodeIntertwinesSignedInversion
  (RH128.binarySeven a0 a1 a2 a3 b0 c0 c1)
  rewrite tritFlipCommutes a0 | tritFlipCommutes a1
        | tritFlipCommutes a2 | tritFlipCommutes a3
        | tritFlipCommutes b0 | tritFlipCommutes c0
        | signedFlipCommutes c1 = refl

-- The central zero of X6 and zero signed multiplicity remain fixed under C2.
-- It is NOT in the seven-bit binary image: inverse chart on neutral data
-- requires additional fibre/retraction policy.
neutralSignedX6 : SignedX6
neutralSignedX6 =
  H.x6 Trit.zer Trit.zer Trit.zer Trit.zer Trit.zer Trit.zer ,
  SSP.zeroMultiplicity

neutralInversionFixed :
  invertSignedX6 neutralSignedX6 ≡ neutralSignedX6
neutralInversionFixed = refl

------------------------------------------------------------------------
-- The resulting exact C2-equivariant F3^6 x SSP embedding is a NONTRIVIAL
-- actual existing-carrier map. It does not supply the missing original
-- analytic source realization or a Monster group automorphism.
------------------------------------------------------------------------
