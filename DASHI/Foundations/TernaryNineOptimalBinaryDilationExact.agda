module DASHI.Foundations.TernaryNineOptimalBinaryDilationExact where

------------------------------------------------------------------------
-- EXACT STORAGE / LOCALITY TRADEOFF FOR THE REPO-NATIVE T^9 CARRIER
--
-- We now solve the finite graph-embedding question for the nearest-transition
-- geometry used here, rather than extrapolating from one rank codec.
--
-- One 3-trit block is P3^3 with 27 states.  The explicit codec below embeds it
-- into five bits and every primitive nearest transition changes at most two
-- bits.  Three independent blocks therefore give
--
--   T^9 = (T^3)^3 -> (B^5)^3 = B^15
--
-- with the same dilation-two bound and no state loss.
--
-- Dilation one is impossible at storage-optimal width for T^9: the all-centre
-- ternary state has 18 distinct primitive neighbours, while one 15-bit word has
-- only 15 distinct one-bit directions.  The generic Fin pigeonhole theorem
-- therefore blocks an injective one-bit-local centre embedding.
--
-- Thus the correct exact statement at n=9 is:
--
--   optimal 15-bit storage CAN preserve bounded locality, with dilation 2;
--   preserving one-bit primitive locality needs at least 18 bit directions.
--
-- This falsifies the stronger claim that optimal binary storage must have
-- unbounded/locality-destroying dilation at this scale.
--
-- SOURCE / METHOD CALIBRATION
--
-- Zevi Miller, Dan Pritikin, I. H. Sudborough,
-- "Embedding multidimensional grids into optimal hypercubes",
-- Theoretical Computer Science 552 (2014), 52--82.
-- DOI: 10.1016/j.tcs.2014.07.026.
--
-- R. Sundara Rajan, Thomas Kalinowski, Sandi Klavzar, Hamid Mokhtar,
-- T. M. Rajalaxmi,
-- "Lower bounds for dilation, wirelength, and edge congestion of embedding
-- graphs into hypercubes", Journal of Supercomputing 77 (2021), 4135--4150.
-- DOI: 10.1007/s11227-020-03420-w.
--
-- The explicit 27->32 codec and n=9 degree obstruction below are local DASHI
-- constructions; the papers calibrate graph-embedding/dilation vocabulary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinProps
import Data.Nat.Properties as NatProps

import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact as Branch
import DASHI.Foundations.SSPTritCarrier as SSP

record Bit5 : Set where
  constructor bits5
  field
    b0 b1 b2 b3 b4 : Bool

open Bit5 public

bitDistance : Bool -> Bool -> Nat
bitDistance false false = 0
bitDistance false true = 1
bitDistance true false = 1
bitDistance true true = 0

hamming5 : Bit5 -> Bit5 -> Nat
hamming5 (bits5 a0 a1 a2 a3 a4) (bits5 c0 c1 c2 c3 c4) =
  bitDistance a0 c0
  + bitDistance a1 c1
  + bitDistance a2 c2
  + bitDistance a3 c3
  + bitDistance a4 c4

Block3 : Set
Block3 = Branch.Triple SSP.SSPTrit

------------------------------------------------------------------------
-- Explicit optimal-width 3-trit -> 5-bit block codec.
------------------------------------------------------------------------

encodeBlock : Block3 -> Bit5
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = bits5 true false true true false
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = bits5 false false true false false
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = bits5 false false true false true
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = bits5 true false false false false
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspZero) = bits5 false false false false true
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = bits5 false false true true true
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = bits5 true false false true false
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = bits5 true false false true true
encodeBlock (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = bits5 true false true false true
encodeBlock (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = bits5 false true true true false
encodeBlock (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspZero) = bits5 false false false true false
encodeBlock (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = bits5 false false false true true
encodeBlock (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = bits5 false true false false false
encodeBlock (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = bits5 false false false false false
encodeBlock (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = bits5 false false true true false
encodeBlock (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = bits5 true true false false false
encodeBlock (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspZero) = bits5 true false false false true
encodeBlock (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = bits5 true false true false false
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = bits5 false true false true true
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = bits5 false true false true false
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = bits5 false true true true true
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = bits5 false true true false true
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspZero) = bits5 false true false false true
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = bits5 false true true false false
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = bits5 true true true false false
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = bits5 true true false false true
encodeBlock (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = bits5 true true true false true

decodeBlock : Bit5 -> Block3
decodeBlock (bits5 false false false false false) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
decodeBlock (bits5 false false false false true) = Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspZero
decodeBlock (bits5 false false false true false) = Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspZero
decodeBlock (bits5 false false false true true) = Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspPosOne
decodeBlock (bits5 false false true false false) = Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspZero
decodeBlock (bits5 false false true false true) = Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne
decodeBlock (bits5 false false true true false) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne
decodeBlock (bits5 false false true true true) = Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspPosOne
decodeBlock (bits5 false true false false false) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne
decodeBlock (bits5 false true false false true) = Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspZero
decodeBlock (bits5 false true false true false) = Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspZero
decodeBlock (bits5 false true false true true) = Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne
decodeBlock (bits5 false true true false false) = Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspPosOne
decodeBlock (bits5 false true true false true) = Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspNegOne
decodeBlock (bits5 false true true true false) = Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspNegOne
decodeBlock (bits5 false true true true true) = Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne
decodeBlock (bits5 true false false false false) = Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspNegOne
decodeBlock (bits5 true false false false true) = Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspZero
decodeBlock (bits5 true false false true false) = Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne
decodeBlock (bits5 true false false true true) = Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspZero
decodeBlock (bits5 true false true false false) = Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspPosOne
decodeBlock (bits5 true false true false true) = Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne
decodeBlock (bits5 true false true true false) = Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne
decodeBlock (bits5 true false true true true) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
decodeBlock (bits5 true true false false false) = Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspNegOne
decodeBlock (bits5 true true false false true) = Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspZero
decodeBlock (bits5 true true false true false) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
decodeBlock (bits5 true true false true true) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
decodeBlock (bits5 true true true false false) = Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne
decodeBlock (bits5 true true true false true) = Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne
decodeBlock (bits5 true true true true false) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero
decodeBlock (bits5 true true true true true) = Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero

decodeEncodeBlock : (block : Block3) -> decodeBlock (encodeBlock block) ≡ block
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspZero SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
decodeEncodeBlock (Branch.triple SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

encodeBlockInjective :
  ∀ {left right : Block3} ->
  encodeBlock left ≡ encodeBlock right ->
  left ≡ right
encodeBlockInjective {left} {right} same =
  trans
    (sym (decodeEncodeBlock left))
    (trans
      (cong decodeBlock same)
      (decodeEncodeBlock right))

------------------------------------------------------------------------
-- Primitive nearest transitions and exact dilation-two certificate.
------------------------------------------------------------------------

data BlockForwardStep : Block3 -> Block3 -> Set where
  stepFirstNegZero :
    (b c : SSP.SSPTrit) ->
    BlockForwardStep
      (Branch.triple SSP.sspNegOne b c)
      (Branch.triple SSP.sspZero b c)
  stepFirstZeroPos :
    (b c : SSP.SSPTrit) ->
    BlockForwardStep
      (Branch.triple SSP.sspZero b c)
      (Branch.triple SSP.sspPosOne b c)
  stepSecondNegZero :
    (a c : SSP.SSPTrit) ->
    BlockForwardStep
      (Branch.triple a SSP.sspNegOne c)
      (Branch.triple a SSP.sspZero c)
  stepSecondZeroPos :
    (a c : SSP.SSPTrit) ->
    BlockForwardStep
      (Branch.triple a SSP.sspZero c)
      (Branch.triple a SSP.sspPosOne c)
  stepThirdNegZero :
    (a b : SSP.SSPTrit) ->
    BlockForwardStep
      (Branch.triple a b SSP.sspNegOne)
      (Branch.triple a b SSP.sspZero)
  stepThirdZeroPos :
    (a b : SSP.SSPTrit) ->
    BlockForwardStep
      (Branch.triple a b SSP.sspZero)
      (Branch.triple a b SSP.sspPosOne)

zero≤two : 0 ≤ 2
zero≤two = z≤n

one≤two : 1 ≤ 2
one≤two = s≤s z≤n

two≤two : 2 ≤ 2
two≤two = s≤s (s≤s z≤n)

blockCodecDilationAtMostTwo :
  ∀ {left right : Block3} ->
  BlockForwardStep left right ->
  hamming5 (encodeBlock left) (encodeBlock right) ≤ 2
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspNegOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspNegOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspNegOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspZero SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspZero SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspZero SSP.sspPosOne) = one≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspPosOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspPosOne SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepFirstNegZero SSP.sspPosOne SSP.sspPosOne) = one≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspNegOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspNegOne SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspNegOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspZero SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspZero SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspZero SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspPosOne SSP.sspNegOne) = one≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspPosOne SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepFirstZeroPos SSP.sspPosOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspNegOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspNegOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspNegOne SSP.sspPosOne) = one≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspZero SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspZero SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspZero SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspPosOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspPosOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepSecondNegZero SSP.sspPosOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspNegOne SSP.sspNegOne) = one≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspNegOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspNegOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspZero SSP.sspNegOne) = one≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspZero SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspZero SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspPosOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspPosOne SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepSecondZeroPos SSP.sspPosOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspNegOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspNegOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspNegOne SSP.sspPosOne) = one≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspZero SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspZero SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspZero SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspPosOne SSP.sspNegOne) = one≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspPosOne SSP.sspZero) = one≤two
blockCodecDilationAtMostTwo (stepThirdNegZero SSP.sspPosOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspNegOne SSP.sspNegOne) = one≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspNegOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspNegOne SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspZero SSP.sspNegOne) = one≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspZero SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspZero SSP.sspPosOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspPosOne SSP.sspNegOne) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspPosOne SSP.sspZero) = two≤two
blockCodecDilationAtMostTwo (stepThirdZeroPos SSP.sspPosOne SSP.sspPosOne) = one≤two

------------------------------------------------------------------------
-- Product lift: 3 blocks / 9 trits -> 15 bits with the same local dilation.
------------------------------------------------------------------------

record NineTrit : Set where
  constructor nineTrit
  field
    block0 block1 block2 : Block3

open NineTrit public

record Bit15 : Set where
  constructor bits15
  field
    word0 word1 word2 : Bit5

open Bit15 public

encodeNine : NineTrit -> Bit15
encodeNine (nineTrit x y z) =
  bits15 (encodeBlock x) (encodeBlock y) (encodeBlock z)

decodeNine : Bit15 -> NineTrit
decodeNine (bits15 x y z) =
  nineTrit (decodeBlock x) (decodeBlock y) (decodeBlock z)

decodeEncodeNine : (state : NineTrit) -> decodeNine (encodeNine state) ≡ state
decodeEncodeNine (nineTrit x y z)
  rewrite decodeEncodeBlock x | decodeEncodeBlock y | decodeEncodeBlock z = refl

encodeNineInjective :
  ∀ {left right : NineTrit} ->
  encodeNine left ≡ encodeNine right ->
  left ≡ right
encodeNineInjective {left} {right} same =
  trans
    (sym (decodeEncodeNine left))
    (trans (cong decodeNine same) (decodeEncodeNine right))

data NineForwardStep : NineTrit -> NineTrit -> Set where
  stepBlock0 :
    ∀ {x x'} (y z : Block3) ->
    BlockForwardStep x x' ->
    NineForwardStep (nineTrit x y z) (nineTrit x' y z)
  stepBlock1 :
    ∀ (x : Block3) {y y'} (z : Block3) ->
    BlockForwardStep y y' ->
    NineForwardStep (nineTrit x y z) (nineTrit x y' z)
  stepBlock2 :
    ∀ (x y : Block3) {z z'} ->
    BlockForwardStep z z' ->
    NineForwardStep (nineTrit x y z) (nineTrit x y z')

hamming15 : Bit15 -> Bit15 -> Nat
hamming15 (bits15 x0 x1 x2) (bits15 y0 y1 y2) =
  hamming5 x0 y0 + hamming5 x1 y1 + hamming5 x2 y2

bitDistanceSelfZero : (bit : Bool) -> bitDistance bit bit ≡ 0
bitDistanceSelfZero false = refl
bitDistanceSelfZero true = refl

hamming5SelfZero : (word : Bit5) -> hamming5 word word ≡ 0
hamming5SelfZero (bits5 a b c d e)
  rewrite bitDistanceSelfZero a
        | bitDistanceSelfZero b
        | bitDistanceSelfZero c
        | bitDistanceSelfZero d
        | bitDistanceSelfZero e = refl

nineCodecDilationAtMostTwo :
  ∀ {left right : NineTrit} ->
  NineForwardStep left right ->
  hamming15 (encodeNine left) (encodeNine right) ≤ 2
nineCodecDilationAtMostTwo (stepBlock0 y z step)
  rewrite hamming5SelfZero (encodeBlock y)
        | hamming5SelfZero (encodeBlock z) =
  blockCodecDilationAtMostTwo step
nineCodecDilationAtMostTwo (stepBlock1 x z step)
  rewrite hamming5SelfZero (encodeBlock x)
        | hamming5SelfZero (encodeBlock z) =
  blockCodecDilationAtMostTwo step
nineCodecDilationAtMostTwo (stepBlock2 x y step)
  rewrite hamming5SelfZero (encodeBlock x)
        | hamming5SelfZero (encodeBlock y) =
  blockCodecDilationAtMostTwo step

------------------------------------------------------------------------
-- Universal degree obstruction to dilation one at 15 bits.
--
-- A one-bit-local embedding of all primitive centre neighbours supplies an
-- injective assignment of source neighbour directions to target bit axes.
-- Finite pigeonhole blocks Fin 18 -> Fin 15.
------------------------------------------------------------------------

record OneBitCentreLocality (sourceDirections targetBits : Nat) : Set₁ where
  constructor oneBitCentreLocality
  field
    axisDirection : Fin sourceDirections -> Fin targetBits
    axisDirectionInjective :
      ∀ {i j} ->
      axisDirection i ≡ axisDirection j ->
      i ≡ j

open OneBitCentreLocality public

tooManySourceDirectionsBlockOneBitLocality :
  ∀ {sourceDirections targetBits : Nat} ->
  targetBits < sourceDirections ->
  OneBitCentreLocality sourceDirections targetBits ->
  ⊥
tooManySourceDirectionsBlockOneBitLocality fewer locality =
  FinProps.<⇒notInjective fewer
    (axisDirectionInjective locality)

fifteenLessThanEighteen : 15 < 18
fifteenLessThanEighteen =
  NatProps.<-trans
    (NatProps.n<1+n 15)
    (NatProps.<-trans
      (NatProps.n<1+n 16)
      (NatProps.n<1+n 17))

compactNineOneBitLocalityImpossible :
  OneBitCentreLocality 18 15 ->
  ⊥
compactNineOneBitLocalityImpossible =
  tooManySourceDirectionsBlockOneBitLocality fifteenLessThanEighteen

ternaryNineStateCount : Nat
ternaryNineStateCount = 19683

fifteenBitCapacity : Nat
fifteenBitCapacity = 32768

unusedCompactCodewords : Nat
unusedCompactCodewords = 13085

compactCapacitySplitsExactly :
  fifteenBitCapacity ≡ ternaryNineStateCount + unusedCompactCodewords
compactCapacitySplitsExactly = refl

record TernaryNineOptimalBinaryDilationBoundary : Set where
  constructor ternaryNineOptimalBinaryDilationBoundary
  field
    fifteenBitsCanEncodeNineTritsInjectively : Bool
    explicitFifteenBitCodecHasDilationAtMostTwo : Bool
    oneBitLocalityPossibleAtFifteenBits : Bool
    eighteenBitPerTritPairingIsStorageMinimal : Bool
    compactBinaryMustHaveUnboundedDilation : Bool
    storageAndLocalityAreSameOptimizationObjective : Bool

canonicalTernaryNineOptimalBinaryDilationBoundary :
  TernaryNineOptimalBinaryDilationBoundary
canonicalTernaryNineOptimalBinaryDilationBoundary =
  ternaryNineOptimalBinaryDilationBoundary
    true true false false false false
