module DASHI.Physics.Closure.NSWholeSpaceBishopFiniteCoherentGramSquareExact where

------------------------------------------------------------------------
-- A / FINITE COHERENT GRAM COLLAPSE ON THE LITERAL BISHOP C^3 CARRIER
--
-- Pairwise majorisation of an off-diagonal Gram before integration creates a
-- free R^3 variable.  The correct object is the complete signed Gram:
--
--   sum_{i,j} w_i w_j Re <V_i,V_j>
--      = || sum_i w_i V_i ||^2.
--
-- This owner proves that identity exactly on the same BishopComplex3 carrier
-- used by the Euclidean Navier--Stokes realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Unnormalised using (_/_; +_; Κ)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray

two : BishopReal.ℝ
two = BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ

complexAdd :
  Physical.BishopComplex →
  Physical.BishopComplex →
  Physical.BishopComplex
complexAdd a b =
  Physical.bishop-complex
    (BishopReal._+_ (Physical.realPart a) (Physical.realPart b))
    (BishopReal._+_ (Physical.imaginaryPart a) (Physical.imaginaryPart b))

complex3Add :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
complex3Add a b =
  Physical.bishop-complex3
    (complexAdd (Physical.cx a) (Physical.cx b))
    (complexAdd (Physical.cy a) (Physical.cy b))
    (complexAdd (Physical.cz a) (Physical.cz b))

zeroComplex : Physical.BishopComplex
zeroComplex =
  Physical.bishop-complex BishopReal.0ℝ BishopReal.0ℝ

zeroComplex3 : Physical.BishopComplex3
zeroComplex3 =
  Physical.bishop-complex3 zeroComplex zeroComplex zeroComplex

realScaleComplex3 :
  BishopReal.ℝ →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
realScaleComplex3 scalar value =
  Physical.bishop-complex3
    (Output.realScaleComplex scalar (Physical.cx value))
    (Output.realScaleComplex scalar (Physical.cy value))
    (Output.realScaleComplex scalar (Physical.cz value))

realHermitianCross :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
realHermitianCross a b =
  BishopReal._+_
    (BishopReal._+_
      (BishopReal._*_
        (Physical.realPart (Physical.cx a))
        (Physical.realPart (Physical.cx b)))
      (BishopReal._*_
        (Physical.imaginaryPart (Physical.cx a))
        (Physical.imaginaryPart (Physical.cx b))))
    (BishopReal._+_
      (BishopReal._+_
        (BishopReal._*_
          (Physical.realPart (Physical.cy a))
          (Physical.realPart (Physical.cy b)))
        (BishopReal._*_
          (Physical.imaginaryPart (Physical.cy a))
          (Physical.imaginaryPart (Physical.cy b))))
      (BishopReal._+_
        (BishopReal._*_
          (Physical.realPart (Physical.cz a))
          (Physical.realPart (Physical.cz b)))
        (BishopReal._*_
          (Physical.imaginaryPart (Physical.cz a))
          (Physical.imaginaryPart (Physical.cz b)))))

crossSelfIsNormSquared :
  (value : Physical.BishopComplex3) →
  BishopReal._≃_
    (realHermitianCross value value)
    (Leray.complex3NormSquared value)
crossSelfIsNormSquared value =
  BishopP.≃-refl (Leray.complex3NormSquared value)

crossAddRight :
  (a b c : Physical.BishopComplex3) →
  BishopReal._≃_
    (realHermitianCross a (complex3Add b c))
    (BishopReal._+_
      (realHermitianCross a b)
      (realHermitianCross a c))
crossAddRight
    (Physical.bishop-complex3
      (Physical.bishop-complex arx aix)
      (Physical.bishop-complex ary aiy)
      (Physical.bishop-complex arz aiz))
    (Physical.bishop-complex3
      (Physical.bishop-complex brx bix)
      (Physical.bishop-complex bry biy)
      (Physical.bishop-complex brz biz))
    (Physical.bishop-complex3
      (Physical.bishop-complex crx cix)
      (Physical.bishop-complex cry ciy)
      (Physical.bishop-complex crz ciz)) =
  let open BishopP.ℝ-Solver
  in solve 18
    (λ arx' aix' ary' aiy' arz' aiz'
       brx' bix' bry' biy' brz' biz'
       crx' cix' cry' ciy' crz' ciz' →
      ((arx' ⊗ (brx' ⊕ crx') ⊕ aix' ⊗ (bix' ⊕ cix'))
       ⊕
       ((ary' ⊗ (bry' ⊕ cry') ⊕ aiy' ⊗ (biy' ⊕ ciy'))
        ⊕
        (arz' ⊗ (brz' ⊕ crz') ⊕ aiz' ⊗ (biz' ⊕ ciz'))))
      ⊜
      (((arx' ⊗ brx' ⊕ aix' ⊗ bix')
        ⊕
        ((ary' ⊗ bry' ⊕ aiy' ⊗ biy')
         ⊕ (arz' ⊗ brz' ⊕ aiz' ⊗ biz')))
       ⊕
       ((arx' ⊗ crx' ⊕ aix' ⊗ cix')
        ⊕
        ((ary' ⊗ cry' ⊕ aiy' ⊗ ciy')
         ⊕ (arz' ⊗ crz' ⊕ aiz' ⊗ ciz')))))
    BishopP.≃-refl
    arx aix ary aiy arz aiz
    brx bix bry biy brz biz
    crx cix cry ciy crz ciz

crossScaleLeft :
  (scalar : BishopReal.ℝ) →
  (a b : Physical.BishopComplex3) →
  BishopReal._≃_
    (realHermitianCross (realScaleComplex3 scalar a) b)
    (BishopReal._*_ scalar (realHermitianCross a b))
crossScaleLeft scalar
    (Physical.bishop-complex3
      (Physical.bishop-complex arx aix)
      (Physical.bishop-complex ary aiy)
      (Physical.bishop-complex arz aiz))
    (Physical.bishop-complex3
      (Physical.bishop-complex brx bix)
      (Physical.bishop-complex bry biy)
      (Physical.bishop-complex brz biz)) =
  let open BishopP.ℝ-Solver
  in solve 13
    (λ s arx' aix' ary' aiy' arz' aiz'
       brx' bix' bry' biy' brz' biz' →
      (((s ⊗ arx') ⊗ brx' ⊕ (s ⊗ aix') ⊗ bix')
       ⊕
       (((s ⊗ ary') ⊗ bry' ⊕ (s ⊗ aiy') ⊗ biy')
        ⊕
        ((s ⊗ arz') ⊗ brz' ⊕ (s ⊗ aiz') ⊗ biz')))
      ⊜
      s ⊗
      ((arx' ⊗ brx' ⊕ aix' ⊗ bix')
       ⊕
       ((ary' ⊗ bry' ⊕ aiy' ⊗ biy')
        ⊕ (arz' ⊗ brz' ⊕ aiz' ⊗ biz'))))
    BishopP.≃-refl
    scalar arx aix ary aiy arz aiz
    brx bix bry biy brz biz

crossScaleRight :
  (scalar : BishopReal.ℝ) →
  (a b : Physical.BishopComplex3) →
  BishopReal._≃_
    (realHermitianCross a (realScaleComplex3 scalar b))
    (BishopReal._*_ scalar (realHermitianCross a b))
crossScaleRight scalar
    (Physical.bishop-complex3
      (Physical.bishop-complex arx aix)
      (Physical.bishop-complex ary aiy)
      (Physical.bishop-complex arz aiz))
    (Physical.bishop-complex3
      (Physical.bishop-complex brx bix)
      (Physical.bishop-complex bry biy)
      (Physical.bishop-complex brz biz)) =
  let open BishopP.ℝ-Solver
  in solve 13
    (λ s arx' aix' ary' aiy' arz' aiz'
       brx' bix' bry' biy' brz' biz' →
      ((arx' ⊗ (s ⊗ brx') ⊕ aix' ⊗ (s ⊗ bix'))
       ⊕
       ((ary' ⊗ (s ⊗ bry') ⊕ aiy' ⊗ (s ⊗ biy'))
        ⊕
        (arz' ⊗ (s ⊗ brz') ⊕ aiz' ⊗ (s ⊗ biz'))))
      ⊜
      s ⊗
      ((arx' ⊗ brx' ⊕ aix' ⊗ bix')
       ⊕
       ((ary' ⊗ bry' ⊕ aiy' ⊗ biy')
        ⊕ (arz' ⊗ brz' ⊕ aiz' ⊗ biz'))))
    BishopP.≃-refl
    scalar arx aix ary aiy arz aiz
    brx bix bry biy brz biz

crossZeroRight :
  (a : Physical.BishopComplex3) →
  BishopReal._≃_
    (realHermitianCross a zeroComplex3)
    BishopReal.0ℝ
crossZeroRight
    (Physical.bishop-complex3
      (Physical.bishop-complex arx aix)
      (Physical.bishop-complex ary aiy)
      (Physical.bishop-complex arz aiz)) =
  let open BishopP.ℝ-Solver
  in solve 6
    (λ arx' aix' ary' aiy' arz' aiz' →
      ((arx' ⊗ Κ (+ 0 / 1) ⊕ aix' ⊗ Κ (+ 0 / 1))
       ⊕
       ((ary' ⊗ Κ (+ 0 / 1) ⊕ aiy' ⊗ Κ (+ 0 / 1))
        ⊕
        (arz' ⊗ Κ (+ 0 / 1) ⊕ aiz' ⊗ Κ (+ 0 / 1))))
      ⊜ Κ (+ 0 / 1))
    BishopP.≃-refl
    arx aix ary aiy arz aiz

zeroNormSquared :
  BishopReal._≃_
    (Leray.complex3NormSquared zeroComplex3)
    BishopReal.0ℝ
zeroNormSquared =
  let open BishopP.ℝ-Solver
  in solve 0
    (Κ (+ 0 / 1) ⊜ Κ (+ 0 / 1))
    BishopP.≃-refl

record WeightedComplex3Cell : Set where
  constructor weighted-complex3-cell
  field
    weight : BishopReal.ℝ
    value : Physical.BishopComplex3

open WeightedComplex3Cell public

weightedValue : WeightedComplex3Cell → Physical.BishopComplex3
weightedValue cell = realScaleComplex3 (weight cell) (value cell)

foldWeighted : List WeightedComplex3Cell → Physical.BishopComplex3
foldWeighted [] = zeroComplex3
foldWeighted (cell ∷ rest) =
  complex3Add (weightedValue cell) (foldWeighted rest)

rowGram :
  WeightedComplex3Cell →
  List WeightedComplex3Cell →
  BishopReal.ℝ
rowGram head [] = BishopReal.0ℝ
rowGram head (cell ∷ rest) =
  BishopReal._+_
    (realHermitianCross (weightedValue head) (weightedValue cell))
    (rowGram head rest)

completeGram :
  List WeightedComplex3Cell → BishopReal.ℝ
completeGram [] = BishopReal.0ℝ
completeGram (head ∷ rest) =
  BishopReal._+_
    (realHermitianCross (weightedValue head) (weightedValue head))
    (BishopReal._+_
      (BishopReal._*_ two (rowGram head rest))
      (completeGram rest))

rowGramIsCrossFold :
  (head : WeightedComplex3Cell) →
  (rest : List WeightedComplex3Cell) →
  BishopReal._≃_
    (rowGram head rest)
    (realHermitianCross (weightedValue head) (foldWeighted rest))
rowGramIsCrossFold head [] =
  BishopP.≃-symm (crossZeroRight (weightedValue head))
rowGramIsCrossFold head (cell ∷ rest) =
  BishopP.≃-trans
    (BishopP.+-congˡ
      (BishopP.≃-refl
        (realHermitianCross (weightedValue head) (weightedValue cell)))
      (rowGramIsCrossFold head rest))
    (BishopP.≃-symm
      (crossAddRight
        (weightedValue head)
        (weightedValue cell)
        (foldWeighted rest)))

normAddExpansion :
  (a b : Physical.BishopComplex3) →
  BishopReal._≃_
    (Leray.complex3NormSquared (complex3Add a b))
    (BishopReal._+_
      (Leray.complex3NormSquared a)
      (BishopReal._+_
        (BishopReal._*_ two (realHermitianCross a b))
        (Leray.complex3NormSquared b)))
normAddExpansion
    (Physical.bishop-complex3
      (Physical.bishop-complex arx aix)
      (Physical.bishop-complex ary aiy)
      (Physical.bishop-complex arz aiz))
    (Physical.bishop-complex3
      (Physical.bishop-complex brx bix)
      (Physical.bishop-complex bry biy)
      (Physical.bishop-complex brz biz)) =
  let open BishopP.ℝ-Solver
  in solve 13
    (λ t arx' aix' ary' aiy' arz' aiz'
       brx' bix' bry' biy' brz' biz' →
      (((arx' ⊕ brx') ⊗ (arx' ⊕ brx')
        ⊕ (aix' ⊕ bix') ⊗ (aix' ⊕ bix'))
       ⊕
       (((ary' ⊕ bry') ⊗ (ary' ⊕ bry')
         ⊕ (aiy' ⊕ biy') ⊗ (aiy' ⊕ biy'))
        ⊕
        ((arz' ⊕ brz') ⊗ (arz' ⊕ brz')
         ⊕ (aiz' ⊕ biz') ⊗ (aiz' ⊕ biz'))))
      ⊜
      ((arx' ⊗ arx' ⊕ aix' ⊗ aix')
       ⊕ ((ary' ⊗ ary' ⊕ aiy' ⊗ aiy')
        ⊕ (arz' ⊗ arz' ⊕ aiz' ⊗ aiz')))
      ⊕
      ((t ⊗
        ((arx' ⊗ brx' ⊕ aix' ⊗ bix')
         ⊕ ((ary' ⊗ bry' ⊕ aiy' ⊗ biy')
          ⊕ (arz' ⊗ brz' ⊕ aiz' ⊗ biz'))))
       ⊕
       ((brx' ⊗ brx' ⊕ bix' ⊗ bix')
        ⊕ ((bry' ⊗ bry' ⊕ biy' ⊗ biy')
         ⊕ (brz' ⊗ brz' ⊕ biz' ⊗ biz')))))
    BishopP.≃-refl
    two arx aix ary aiy arz aiz brx bix bry biy brz biz

completeGramIsFoldNormSquared :
  (cells : List WeightedComplex3Cell) →
  BishopReal._≃_
    (completeGram cells)
    (Leray.complex3NormSquared (foldWeighted cells))
completeGramIsFoldNormSquared [] =
  BishopP.≃-symm zeroNormSquared
completeGramIsFoldNormSquared (head ∷ rest) =
  BishopP.≃-trans
    (BishopP.+-cong
      (crossSelfIsNormSquared (weightedValue head))
      (BishopP.+-cong
        (BishopP.*-congˡ (rowGramIsCrossFold head rest))
        (completeGramIsFoldNormSquared rest)))
    (BishopP.≃-symm
      (normAddExpansion
        (weightedValue head)
        (foldWeighted rest)))

completeGramNonnegative :
  (cells : List WeightedComplex3Cell) →
  BishopReal.NonNegative (completeGram cells)
completeGramNonnegative cells =
  BishopP.0≤x⇒nonNegx
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm
        (completeGramIsFoldNormSquared cells))
      (BishopP.nonNegx⇒0≤x
        (Leray.complex3NormSquaredNonnegative
          (foldWeighted cells))))

finiteCoherentGramCollapseClosed : Bool
finiteCoherentGramCollapseClosed = true

pairwisePositiveMajorizationUsed : Bool
pairwisePositiveMajorizationUsed = false

freePairCoordinateIntroduced : Bool
freePairCoordinateIntroduced = false

clayPromotion : Bool
clayPromotion = false

finiteCoherentGramCollapseClosedIsTrue :
  finiteCoherentGramCollapseClosed ≡ true
finiteCoherentGramCollapseClosedIsTrue = refl

pairwisePositiveMajorizationUsedIsFalse :
  pairwisePositiveMajorizationUsed ≡ false
pairwisePositiveMajorizationUsedIsFalse = refl

freePairCoordinateIntroducedIsFalse :
  freePairCoordinateIntroduced ≡ false
freePairCoordinateIntroducedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
