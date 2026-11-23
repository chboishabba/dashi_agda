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
open import Data.Empty using (⊥)

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


------------------------------------------------------------------------
-- C2^7: SEVEN INDEPENDENT GENERATORS ON EXISTING FINITE MODEL CARRIERS.
-- Earlier simultaneous complement/negation is the all-ones group element.
-- Faithfulness is proved by the unique action on the all-false source.
-- The target action consists of six coordinate sign automorphisms
-- of the native F3^6 Heisenberg COORDINATE and the seventh signed SSP
-- inversion. NOT an action of Monster 3^(1+12) itself: a 3-group has
-- no nontrivial involutions. NOT independent RH analytic operations.
------------------------------------------------------------------------

xorBit : Bool → Bool → Bool
xorBit false b = b
xorBit true b = flipBit b

xorBitAssociative : (a b c : Bool) →
  xorBit a (xorBit b c) ≡ xorBit (xorBit a b) c
xorBitAssociative false false false = refl
xorBitAssociative false false true = refl
xorBitAssociative false true false = refl
xorBitAssociative false true true = refl
xorBitAssociative true false false = refl
xorBitAssociative true false true = refl
xorBitAssociative true true false = refl
xorBitAssociative true true true = refl

xorBitCommutes : (a b : Bool) → xorBit a b ≡ xorBit b a
xorBitCommutes false false = refl
xorBitCommutes false true = refl
xorBitCommutes true false = refl
xorBitCommutes true true = refl

xorBitRightFalse : (a : Bool) → xorBit a false ≡ a
xorBitRightFalse false = refl
xorBitRightFalse true = refl

maskXor : RH128.BinarySeven → RH128.BinarySeven → RH128.BinarySeven
maskXor (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1) (RH128.binarySeven na0 na1 na2 na3 nb0 nc0 nc1) =
  RH128.binarySeven
    (xorBit ma0 na0) (xorBit ma1 na1) (xorBit ma2 na2) (xorBit ma3 na3) (xorBit mb0 nb0) (xorBit mc0 nc0) (xorBit mc1 nc1)

maskAct : RH128.BinarySeven → RH128.BinarySeven → RH128.BinarySeven
maskAct = maskXor

allFalse : RH128.BinarySeven
allFalse = RH128.binarySeven false false false false false false false

maskActAtFalse : (mask : RH128.BinarySeven) →
  maskAct mask allFalse ≡ mask
maskActAtFalse (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1)
  rewrite xorBitRightFalse ma0
        | xorBitRightFalse ma1
        | xorBitRightFalse ma2
        | xorBitRightFalse ma3
        | xorBitRightFalse mb0
        | xorBitRightFalse mc0
        | xorBitRightFalse mc1 = refl

maskActLaw : (m n state : RH128.BinarySeven) →
  maskAct m (maskAct n state) ≡ maskAct (maskXor m n) state
maskActLaw (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1) (RH128.binarySeven na0 na1 na2 na3 nb0 nc0 nc1) (RH128.binarySeven sa0 sa1 sa2 sa3 sb0 sc0 sc1)
  rewrite xorBitAssociative ma0 na0 sa0
        | xorBitAssociative ma1 na1 sa1
        | xorBitAssociative ma2 na2 sa2
        | xorBitAssociative ma3 na3 sa3
        | xorBitAssociative mb0 nb0 sb0
        | xorBitAssociative mc0 nc0 sc0
        | xorBitAssociative mc1 nc1 sc1 = refl

maskXorCommutes : (m n : RH128.BinarySeven) →
  maskXor m n ≡ maskXor n m
maskXorCommutes (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1) (RH128.binarySeven na0 na1 na2 na3 nb0 nc0 nc1)
  rewrite xorBitCommutes ma0 na0
        | xorBitCommutes ma1 na1
        | xorBitCommutes ma2 na2
        | xorBitCommutes ma3 na3
        | xorBitCommutes mb0 nb0
        | xorBitCommutes mc0 nc0
        | xorBitCommutes mc1 nc1 = refl

maskActCommutes : (m n state : RH128.BinarySeven) →
  maskAct m (maskAct n state) ≡ maskAct n (maskAct m state)
maskActCommutes m n state =
  transEq (maskActLaw m n state)
    (transEq (mapEq (λ mask → maskAct mask state)
        (maskXorCommutes m n))
      (reverseEq (maskActLaw n m state)))

maskActionFaithful : (mask : RH128.BinarySeven) →
  maskAct mask allFalse ≡ allFalse → mask ≡ allFalse
maskActionFaithful mask eq =
  transEq (reverseEq (maskActAtFalse mask)) eq

maskActionsInjective :
  (m n : RH128.BinarySeven) →
  ((state : RH128.BinarySeven) →
    maskAct m state ≡ maskAct n state) → m ≡ n
maskActionsInjective m n forallEq =
  transEq (reverseEq (maskActAtFalse m))
    (transEq (forallEq allFalse) (maskActAtFalse n))

tritNegateTwice : (x : Trit.Trit) → H.negate3 (H.negate3 x) ≡ x
tritNegateTwice Trit.neg = refl
tritNegateTwice Trit.zer = refl
tritNegateTwice Trit.pos = refl

signedNegateTwice :
  (x : SSP.SignedMultiplicity) →
  SSP.negateMultiplicity (SSP.negateMultiplicity x) ≡ x
signedNegateTwice (SSP.negativeMultiplicity n) = refl
signedNegateTwice SSP.zeroMultiplicity = refl
signedNegateTwice (SSP.positiveMultiplicity n) = refl

actTrit : Bool → Trit.Trit → Trit.Trit
actTrit false x = x
actTrit true x = H.negate3 x

actSigned : Bool → SSP.SignedMultiplicity → SSP.SignedMultiplicity
actSigned false x = x
actSigned true x = SSP.negateMultiplicity x

tritActLaw : (m n : Bool) (x : Trit.Trit) →
  actTrit m (actTrit n x) ≡ actTrit (xorBit m n) x
tritActLaw false false x = refl
tritActLaw false true x = refl
tritActLaw true false x = refl
tritActLaw true true x = tritNegateTwice x

signedActLaw : (m n : Bool) (x : SSP.SignedMultiplicity) →
  actSigned m (actSigned n x) ≡ actSigned (xorBit m n) x
signedActLaw false false x = refl
signedActLaw false true x = refl
signedActLaw true false x = refl
signedActLaw true true x = signedNegateTwice x

actOnNativeSignedX6 : RH128.BinarySeven → SignedX6 → SignedX6
actOnNativeSignedX6 (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1) (H.x6 a0 a1 a2 a3 b0 c0 , c1) =
  H.x6
    (actTrit ma0 a0) (actTrit ma1 a1) (actTrit ma2 a2)
    (actTrit ma3 a3) (actTrit mb0 b0) (actTrit mc0 c0) ,
  actSigned mc1 c1

actOnNativeSignedX6Law : (m n : RH128.BinarySeven) →
  (state : SignedX6) →
  actOnNativeSignedX6 m (actOnNativeSignedX6 n state) ≡
    actOnNativeSignedX6 (maskXor m n) state
actOnNativeSignedX6Law (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1) (RH128.binarySeven na0 na1 na2 na3 nb0 nc0 nc1)
  (H.x6 a0 a1 a2 a3 b0 c0 , c1)
  rewrite tritActLaw ma0 na0 a0
        | tritActLaw ma1 na1 a1
        | tritActLaw ma2 na2 a2
        | tritActLaw ma3 na3 a3
        | tritActLaw mb0 nb0 b0
        | tritActLaw mc0 nc0 c0
        | signedActLaw mc1 nc1 c1 = refl

bitTritMaskIntertwines : (m b : Bool) →
  bitTrit (xorBit m b) ≡ actTrit m (bitTrit b)
bitTritMaskIntertwines false b = refl
bitTritMaskIntertwines true b = tritFlipCommutes b

bitSignedMaskIntertwines : (m b : Bool) →
  bitSigned (xorBit m b) ≡ actSigned m (bitSigned b)
bitSignedMaskIntertwines false b = refl
bitSignedMaskIntertwines true b = signedFlipCommutes b

encodeIntertwinesAllSeven :
  (mask state : RH128.BinarySeven) →
  encode (maskAct mask state) ≡
    actOnNativeSignedX6 mask (encode state)
encodeIntertwinesAllSeven (RH128.binarySeven ma0 ma1 ma2 ma3 mb0 mc0 mc1) (RH128.binarySeven sa0 sa1 sa2 sa3 sb0 sc0 sc1)
  rewrite bitTritMaskIntertwines ma0 sa0
        | bitTritMaskIntertwines ma1 sa1
        | bitTritMaskIntertwines ma2 sa2
        | bitTritMaskIntertwines ma3 sa3
        | bitTritMaskIntertwines mb0 sb0
        | bitTritMaskIntertwines mc0 sc0
        | bitSignedMaskIntertwines mc1 sc1 = refl

nativeActionFaithfulOnEncodedPatch :
  (mask : RH128.BinarySeven) →
  actOnNativeSignedX6 mask (encode allFalse) ≡ encode allFalse →
  mask ≡ allFalse
nativeActionFaithfulOnEncodedPatch mask eq =
  maskActionFaithful mask
    (encodeInjective
      (transEq (encodeIntertwinesAllSeven mask allFalse) eq))

allOnesNativeActionRecoversGlobalInversion :
  (state : SignedX6) →
  actOnNativeSignedX6 RH128.allOnes state ≡ invertSignedX6 state
allOnesNativeActionRecoversGlobalInversion
  (H.x6 a0 a1 a2 a3 b0 c0 , c1) = refl


------------------------------------------------------------------------
-- EXACT ORIGINAL SOURCE-ENDPOINT NEGATIVE CONTROL.
-- All seven source-labelled factor axes are separately action-bearing on
-- the native 3B x SSP finite carrier.  But NONE preserves the selected
-- original full coefficient (all seven labels=1): each sends 128 -> 64.
-- This rules out silently treating the faithful C2^7 representation as
-- seven independent symmetries of the ACTUAL fixed sampleTest normalization.
------------------------------------------------------------------------

data SevenGenerator : Set where
  physical0 physical1 physical2 physical3 : SevenGenerator
  evenFourier : SevenGenerator
  profileOrigin0 profileOrigin1 : SevenGenerator

singleton : SevenGenerator → RH128.BinarySeven
singleton physical0 = RH128.binarySeven true false false false false false false
singleton physical1 = RH128.binarySeven false true false false false false false
singleton physical2 = RH128.binarySeven false false true false false false false
singleton physical3 = RH128.binarySeven false false false true false false false
singleton evenFourier = RH128.binarySeven false false false false true false false
singleton profileOrigin0 = RH128.binarySeven false false false false false true false
singleton profileOrigin1 = RH128.binarySeven false false false false false false true

allSevenGeneratorsMoveOriginalCoefficient :
  (generator : SevenGenerator) →
  RH128.coefficient (maskAct (singleton generator) RH128.allOnes) ≡ 64
allSevenGeneratorsMoveOriginalCoefficient physical0 = refl
allSevenGeneratorsMoveOriginalCoefficient physical1 = refl
allSevenGeneratorsMoveOriginalCoefficient physical2 = refl
allSevenGeneratorsMoveOriginalCoefficient physical3 = refl
allSevenGeneratorsMoveOriginalCoefficient evenFourier = refl
allSevenGeneratorsMoveOriginalCoefficient profileOrigin0 = refl
allSevenGeneratorsMoveOriginalCoefficient profileOrigin1 = refl

noPhysicalSymmetryFromNormalizationFactor :
  (generator : SevenGenerator) →
  RH128.coefficient (maskAct (singleton generator) RH128.allOnes) ≡ 128 →
  ⊥
noPhysicalSymmetryFromNormalizationFactor generator equality
  rewrite allSevenGeneratorsMoveOriginalCoefficient generator = bad equality
  where
  bad : 64 ≡ 128 → ⊥
  bad ()
