module DASHI.Cognition.PNF.X369DirectedRouterConditionalCodecExact where

------------------------------------------------------------------------
-- ORIGINAL-SOURCE C3 DIRECTED CHANNEL COMPRESSION:
-- two directed channels PLUS an independently available total/DC value
-- reconstruct the third channel exactly. Without that side information
-- two channels are NOT sufficient for every original router head.
--
-- The original triadic feature definitions, attribution and integer
-- solver are owned by X369OriginalDirectedTriadC3PolynomialCandidate.
-- Do not call this an actual neural bit saving: code costs and the
-- availability of the total/DC side value require source evidence.
--
-- Proposed Agda kernel proof; no checker executed in this session.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; _+_; _*_; _-_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; _:*_; con; _:=_)
open import Data.Product using (_×_; _,_)
import DASHI.Cognition.PNF.X369OriginalDirectedTriadC3PolynomialCandidate as Original
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

record Directed : Set where
  constructor directed
  field
    sourceSelf sourceForward sourceReverse : ℤ
open Directed public

originalDirected :
  (a b c A B C : ℤ) → Directed
originalDirected a b c A B C =
  directed
    (Original.originalSelf a b c A B C)
    (Original.originalCyclic a b c A B C)
    (Original.originalAnticyclic a b c A B C)

-- This is the exact ORIGINAL all-three-channels sum, not an invented
-- 3-channel abstraction. It is the product of both triad DC sums.
sourceDC : (a b c A B C : ℤ) → ℤ
sourceDC a b c A B C =
  ((a + b) + c) * ((A + B) + C)

originalDirectedTotal : Directed → ℤ
originalDirectedTotal d =
  (sourceSelf d + sourceForward d) + sourceReverse d

originalDirectedTotalEqualsSourceDC :
  (a b c A B C : ℤ) →
  originalDirectedTotal (originalDirected a b c A B C)
    ≡ sourceDC a b c A B C
originalDirectedTotalEqualsSourceDC a b c A B C =
  solve 6
    (λ a b c A B C →
      (((((a :* A) :+ (b :* B)) :+ (c :* C))
       :+ (((a :* B) :+ (b :* C)) :+ (c :* A)))
       :+ (((a :* C) :+ (b :* A)) :+ (c :* B)))
       := (((a :+ b) :+ c) :* ((A :+ B) :+ C)))
    refl a b c A B C

-- Code consists of 2 directed numbers. Consumer must already know
-- the TOTAL from its source/history side state.
encodeDirectedTwo : Directed → ℤ × ℤ
encodeDirectedTwo d = sourceSelf d , sourceForward d

decodeDirectedWithKnownDC : ℤ → ℤ × ℤ → Directed
decodeDirectedWithKnownDC total (s , f) =
  directed s f ((total - s) - f)

recoverThirdFromTotal :
  (s f r : ℤ) →
  (((s + f) + r) - s) - f ≡ r
recoverThirdFromTotal s f r =
  solve 3
    (λ s f r →
      (((((s :+ f) :+ r) :- s) :- f) := r))
    refl s f r

twoDirectedPlusTotalReconstructsOriginal :
  (d : Directed) →
  decodeDirectedWithKnownDC
    (originalDirectedTotal d)
    (encodeDirectedTwo d)
  ≡ d
twoDirectedPlusTotalReconstructsOriginal (directed s f r)
  rewrite recoverThirdFromTotal s f r = refl

twoDirectedPlusSourceDCCorrect :
  (a b c A B C : ℤ) →
  decodeDirectedWithKnownDC
    (sourceDC a b c A B C)
    (encodeDirectedTwo (originalDirected a b c A B C))
  ≡ originalDirected a b c A B C
twoDirectedPlusSourceDCCorrect a b c A B C
  rewrite
    -- Replace independently computed original DC by exactly the
    -- source's three-channel total, without postulating equality.
    sym (originalDirectedTotalEqualsSourceDC a b c A B C) =
  twoDirectedPlusTotalReconstructsOriginal
    (originalDirected a b c A B C)
  where
    sym : ∀ {X : Set}{x y : X} → x ≡ y → y ≡ x
    sym refl = refl

------------------------------------------------------------------------
-- Counterexample using ACTUAL original T formula:
-- same retained (self,forward) = (0,0), but reverse = 0 vs 1.
-- Without original DC or a suitable restriction on the head,
-- the two-channel projection is NOT consumer-sufficient.
------------------------------------------------------------------------

sourceA sourceB : Directed
sourceA =
  originalDirected (+ 1) (+ 0) (+ 0)
                   (+ 0) (+ 0) (+ 0)
sourceB =
  originalDirected (+ 1) (+ 0) (+ 0)
                   (+ 0) (+ 0) (+ 1)

sourceAIsZero : sourceA ≡ directed (+ 0) (+ 0) (+ 0)
sourceAIsZero = refl

sourceBIsReverseOne : sourceB ≡ directed (+ 0) (+ 0) (+ 1)
sourceBIsReverseOne = refl

sameTwoEncodedDifferentReverse :
  encodeDirectedTwo sourceA ≡ encodeDirectedTwo sourceB
sameTwoEncodedDifferentReverse = refl

reverseConsumer : Directed → ℤ
reverseConsumer = sourceReverse

differentReverseConsumer :
  reverseConsumer sourceA ≡ reverseConsumer sourceB → ⊥
differentReverseConsumer ()

twoDirectedWithoutDCNotSufficient :
  Descent.ConsumerSufficient
    encodeDirectedTwo reverseConsumer → ⊥
twoDirectedWithoutDCNotSufficient sufficient =
  differentReverseConsumer
    (sufficient sourceA sourceB sameTwoEncodedDifferentReverse)

-- Consumer indexed: any original head depending on reverse may
-- distinguish the collision. If the head depends ONLY on the two
-- stored channels, the same projection is already sufficient.
anyTwoChannelConsumerSufficient :
  ∀ {Outcome : Set}
  (head : ℤ × ℤ → Outcome) →
  Descent.ConsumerSufficient encodeDirectedTwo
    (λ d → head (encodeDirectedTwo d))
anyTwoChannelConsumerSufficient head x y same =
  cong head same
  where
    cong : ∀ {A B : Set}{x y : A} →
      (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

-- The exact saved-variable claim is CONDITIONAL:
-- 3 original directed scalars ↔ 2 directed scalars + supplied total.
-- A total/DC value computed and stored per expert would restore the
-- third scalar's cost; no universal physical compression is asserted.
