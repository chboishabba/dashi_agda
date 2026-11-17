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


------------------------------------------------------------------------
-- P0 SCORE SUFFICIENCY: a THREE-weight original directed readout
-- can be evaluated from TWO directed coordinates and known DC,
-- with a deterministic transported weight triple.
--
-- This goes beyond reconstructing r: it shows the actual weighted
-- router logit can be computed directly without materialising r.
-- In particular with sourceDC=0 the two-channel consumer needs
-- NO side scalar, although source representation/precision cost
-- must still be established independently.
------------------------------------------------------------------------

directedWeightedScore : ℤ → ℤ → ℤ → Directed → ℤ
directedWeightedScore ws wf wr d =
  ((ws * sourceSelf d) + (wf * sourceForward d))
  + (wr * sourceReverse d)

twoDirectedWeightedScoreWithTotal :
  ℤ → ℤ → ℤ → ℤ → (ℤ × ℤ) → ℤ
twoDirectedWeightedScoreWithTotal ws wf wr total (s , f) =
  (((ws - wr) * s) + ((wf - wr) * f)) + (wr * total)

rawWeightedScoreFactorization :
  (s f r ws wf wr : ℤ) →
  (((ws * s) + (wf * f)) + (wr * r))
  ≡ ((((ws - wr) * s) + ((wf - wr) * f))
      + (wr * ((s + f) + r)))
rawWeightedScoreFactorization s f r ws wf wr =
  solve 6
    (λ s f r ws wf wr →
      ((((ws :* s) :+ (wf :* f)) :+ (wr :* r))
      := (((((ws :- wr) :* s) :+ ((wf :- wr) :* f))
            :+ (wr :* ((s :+ f) :+ r))))))
    refl s f r ws wf wr

weightedScoreFactorsThroughTwoPlusTotal :
  (ws wf wr : ℤ) (d : Directed) →
  directedWeightedScore ws wf wr d
  ≡ twoDirectedWeightedScoreWithTotal
      ws wf wr (originalDirectedTotal d) (encodeDirectedTwo d)
weightedScoreFactorsThroughTwoPlusTotal ws wf wr (directed s f r) =
  rawWeightedScoreFactorization s f r ws wf wr

originalWeightedScoreTwoPlusSourceDC :
  (a b c A B C ws wf wr : ℤ) →
  directedWeightedScore ws wf wr (originalDirected a b c A B C)
  ≡ twoDirectedWeightedScoreWithTotal ws wf wr
      (sourceDC a b c A B C)
      (encodeDirectedTwo (originalDirected a b c A B C))
originalWeightedScoreTwoPlusSourceDC a b c A B C ws wf wr =
  trans
    (weightedScoreFactorsThroughTwoPlusTotal
      ws wf wr (originalDirected a b c A B C))
    (cong
      (λ total → twoDirectedWeightedScoreWithTotal
         ws wf wr total
         (encodeDirectedTwo (originalDirected a b c A B C)))
      (originalDirectedTotalEqualsSourceDC a b c A B C))
  where
    trans : ∀ {X : Set}{x y z : X} → x ≡ y → y ≡ z → x ≡ z
    trans refl eq = eq
    cong : ∀ {X Y : Set}{x y : X} →
      (fn : X → Y) → x ≡ y → fn x ≡ fn y
    cong fn refl = refl

-- In the DC-zero source subspace, the original all-three channel
-- head is exactly a TWO-channel head with transported weights.
-- This is a conditional representational reduction, not an
-- unconditional data-free reduction of arbitrary source inputs.
zeroDCWeightedScoreNeedsOnlyTwo :
  (a b c A B C ws wf wr : ℤ) →
  sourceDC a b c A B C ≡ (+ 0) →
  directedWeightedScore ws wf wr (originalDirected a b c A B C)
  ≡ twoDirectedWeightedScoreWithTotal ws wf wr (+ 0)
      (encodeDirectedTwo (originalDirected a b c A B C))
zeroDCWeightedScoreNeedsOnlyTwo a b c A B C ws wf wr zeroDC =
  trans
    (originalWeightedScoreTwoPlusSourceDC
      a b c A B C ws wf wr)
    (cong
      (λ total → twoDirectedWeightedScoreWithTotal
        ws wf wr total
        (encodeDirectedTwo (originalDirected a b c A B C)))
      zeroDC)
  where
    trans : ∀ {X : Set}{x y z : X} → x ≡ y → y ≡ z → x ≡ z
    trans refl eq = eq
    cong : ∀ {X Y : Set}{x y : X} →
      (fn : X → Y) → x ≡ y → fn x ≡ fn y
    cong fn refl = refl

-- A finite quantizer changes arithmetic identities unless exact
-- rounding laws and decision margins are provided. This module
-- proves ℤ source semantics only and makes no float equality claim.


------------------------------------------------------------------------
-- P0 adversarial scope: the original feature map itself reaches
-- every integer triple (choose x=(1,0,0), history=(A,B,C)).
-- Thus the missing third directed coordinate is not a hidden
-- universal algebraic identity on unrestricted original states.
-- This is NOT a no-injection theorem for arbitrary ℤ³ -> ℤ²
-- encoders, since such non-linear set-theoretic encodings exist.
------------------------------------------------------------------------

originalFeatureRealizesEveryDirectedTriple :
  (s f r : ℤ) →
  originalDirected (+ 1) (+ 0) (+ 0) s f r
  ≡ directed s f r
originalFeatureRealizesEveryDirectedTriple s f r = refl

------------------------------------------------------------------------
-- P0 quantisation / approximation algebra:
-- if a quantizer perturbs each retained coordinate by es, ef and
-- the supplied DC total by eD, then the learned two-channel
-- score error is EXACTLY
--   (ws-wr)*es + (wf-wr)*ef + wr*eD.
--
-- This is an error-IDENTITY, not a bound on rounding error or a
-- TopK decision guarantee. The latter requires independently
-- verified quantizer tolerances and strict source router margins.
------------------------------------------------------------------------

rawTwoChannelQuantizationError :
  (ws wf wr total s f eD es ef : ℤ) →
  (twoDirectedWeightedScoreWithTotal
      ws wf wr (total + eD) ((s + es) , (f + ef))
    - twoDirectedWeightedScoreWithTotal
      ws wf wr total (s , f))
  ≡ (((ws - wr) * es) + ((wf - wr) * ef)) + (wr * eD)
rawTwoChannelQuantizationError ws wf wr total s f eD es ef =
  solve 9
    (λ ws wf wr total s f eD es ef →
      ((((((ws :- wr) :* (s :+ es))
          :+ ((wf :- wr) :* (f :+ ef)))
          :+ (wr :* (total :+ eD)))
        :- ((((ws :- wr) :* s)
          :+ ((wf :- wr) :* f))
          :+ (wr :* total)))
       := (((((ws :- wr) :* es)
          :+ ((wf :- wr) :* ef))
          :+ (wr :* eD)))))
    refl ws wf wr total s f eD es ef

-- Equal exact scores do not establish the same routed experts if
-- quantized scores perturb near a top-k tie, nor do equal expert
-- sets imply identical softmax mixture weights or future histories.


------------------------------------------------------------------------
-- P0 C3 PHASE PRESERVATION IN THE TWO-CHANNEL CENTERED QUOTIENT
--
-- If original directed sum=0, the full three-channel action
--   (s,f,r) -> (r,s,f)
-- becomes the exact two-channel linear action
--   (s,f) -> (-s-f,s).
-- Its THIRD iterate is identity. Thus a two-channel code can
-- retain the full C3 action when centered source admission
-- is explicitly proved, unlike the invariant-only quotient no-go.
------------------------------------------------------------------------

rotateFullDirected : Directed → Directed
rotateFullDirected (directed s f r) = directed r s f

rotateFullDirectedCubed : (d : Directed) →
  rotateFullDirected
    (rotateFullDirected (rotateFullDirected d)) ≡ d
rotateFullDirectedCubed (directed s f r) = refl

rotateCenteredTwo : (ℤ × ℤ) → (ℤ × ℤ)
rotateCenteredTwo (s , f) =
  (((+ 0) - s) - f) , s

rawCenteredTwoTwiceFirst :
  (s f : ℤ) →
  ((+ 0) - (((+ 0) - s) - f)) - s ≡ f
rawCenteredTwoTwiceFirst s f =
  solve 2
    (λ s f →
      (((con (+ 0) :- ((con (+ 0) :- s) :- f)) :- s) := f))
    refl s f

rotateCenteredTwoSquared :
  (s f : ℤ) →
  rotateCenteredTwo (rotateCenteredTwo (s , f))
    ≡ (f , (((+ 0) - s) - f))
rotateCenteredTwoSquared s f =
  cong₂ _,_ (rawCenteredTwoTwiceFirst s f) refl
  where
    cong₂ : ∀ {X Y Z : Set}
      {a b : X}{c d : Y}
      (fn : X → Y → Z) →
      a ≡ b → c ≡ d → fn a c ≡ fn b d
    cong₂ fn refl refl = refl

rawCenteredTwoThriceFirst :
  (s f : ℤ) →
  ((+ 0) - f) - (((+ 0) - s) - f) ≡ s
rawCenteredTwoThriceFirst s f =
  solve 2
    (λ s f →
      (((con (+ 0) :- f) :- ((con (+ 0) :- s) :- f)) := s))
    refl s f

rotateCenteredTwoCubed :
  (s f : ℤ) →
  rotateCenteredTwo
    (rotateCenteredTwo (rotateCenteredTwo (s , f)))
  ≡ (s , f)
rotateCenteredTwoCubed s f
  rewrite rotateCenteredTwoSquared s f
        | rawCenteredTwoThriceFirst s f = refl

thirdFromZeroTotal :
  (s f r : ℤ) →
  ((s + f) + r) ≡ (+ 0) →
  r ≡ (((+ 0) - s) - f)
thirdFromZeroTotal s f r zeroTotal =
  sym (cong sourceReverse (trans
    (cong
      (λ total → decodeDirectedWithKnownDC total (s , f))
      (sym zeroTotal))
    (twoDirectedPlusTotalReconstructsOriginal (directed s f r))))
  where
    sym : ∀ {X : Set}{x y : X} → x ≡ y → y ≡ x
    sym refl = refl
    trans : ∀ {X : Set}{x y z : X} → x ≡ y → y ≡ z → x ≡ z
    trans refl eq = eq
    cong : ∀ {X Y : Set}{x y : X} →
      (fn : X → Y) → x ≡ y → fn x ≡ fn y
    cong fn refl = refl

sourceCenteredC3TwoChannelIntertwines :
  (d : Directed) →
  originalDirectedTotal d ≡ (+ 0) →
  encodeDirectedTwo (rotateFullDirected d)
    ≡ rotateCenteredTwo (encodeDirectedTwo d)
sourceCenteredC3TwoChannelIntertwines (directed s f r) zeroTotal =
  cong₂ _,_ (thirdFromZeroTotal s f r zeroTotal) refl
  where
    cong₂ : ∀ {X Y Z : Set}
      {a b : X}{c d : Y}
      (fn : X → Y → Z) →
      a ≡ b → c ≡ d → fn a c ≡ fn b d
    cong₂ fn refl refl = refl

-- The zero-DC quotient retains a nontrivial 2D C3 action and any
-- selected original linear head under the transported two-weight
-- scoring law. Whether the original trained states actually satisfy
-- zero-DC and whether quantized future-history transitions commute
-- still require source evidence and a separate formal weld.


------------------------------------------------------------------------
-- P0 stronger consumer reduction: SAME DC across TWO expert candidates
-- suffices for exact RELATIVE score preservation. DC need NOT be zero.
--
-- Original HistoryOrbitMoE shares one learned directed head w across
-- experts. The per-expert DC contribution wr*D_e is then common
-- when D_e=D_j, and cancels from score differences/softmax ratios.
-- The feature triple itself need not be reconstructible from two
-- channels without the missing DC; this is strictly a selected
-- router-score consumer theorem.
------------------------------------------------------------------------

twoChannelRelativeScore :
  (ws wf wr : ℤ) →
  (ℤ × ℤ) → (ℤ × ℤ) → ℤ
twoChannelRelativeScore ws wf wr (si , fi) (sj , fj) =
  (((ws - wr) * si) + ((wf - wr) * fi))
  - (((ws - wr) * sj) + ((wf - wr) * fj))

rawCommonDCCancels :
  (ws wf wr common si fi sj fj : ℤ) →
  (twoDirectedWeightedScoreWithTotal
      ws wf wr common (si , fi)
  - twoDirectedWeightedScoreWithTotal
      ws wf wr common (sj , fj))
  ≡ twoChannelRelativeScore ws wf wr
      (si , fi) (sj , fj)
rawCommonDCCancels ws wf wr common si fi sj fj =
  solve 8
    (λ ws wf wr common si fi sj fj →
      ((((((ws :- wr) :* si) :+ ((wf :- wr) :* fi))
        :+ (wr :* common))
       :- (((((ws :- wr) :* sj) :+ ((wf :- wr) :* fj))
        :+ (wr :* common)))
      := (((((ws :- wr) :* si) :+ ((wf :- wr) :* fi))
        :- (((ws :- wr) :* sj) :+ ((wf :- wr) :* fj)))))
    refl ws wf wr common si fi sj fj

originalSameDCRelativeScoreFactors :
  (ws wf wr : ℤ) (di dj : Directed) →
  originalDirectedTotal di ≡ originalDirectedTotal dj →
  (directedWeightedScore ws wf wr di
    - directedWeightedScore ws wf wr dj)
  ≡ twoChannelRelativeScore ws wf wr
      (encodeDirectedTwo di) (encodeDirectedTwo dj)
originalSameDCRelativeScoreFactors ws wf wr
  (directed si fi ri) (directed sj fj rj) sameDC
  rewrite weightedScoreFactorsThroughTwoPlusTotal
            ws wf wr (directed si fi ri)
        | weightedScoreFactorsThroughTwoPlusTotal
            ws wf wr (directed sj fj rj)
        | sameDC =
  rawCommonDCCancels
    ws wf wr (originalDirectedTotal (directed sj fj rj))
    si fi sj fj

-- Operational hypothesis still OPEN: original expert histories
-- must have identical DC sums (or the shared activation has
-- zero DC) on the source states being routed. Shared learned
-- weights alone DO NOT imply D_e identical across experts.
