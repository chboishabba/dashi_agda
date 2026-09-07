module DASHI.Physics.Closure.NSTriadKNHelicalSignedGramSplitRound474Exact where

------------------------------------------------------------------------
-- ROUND474 / EXACT ++ / -- SPLIT OF THE SIGNED R383 GRAM FORM
--
-- Lean sibling `TransverseFrameSplit.lean` shows over the real carrier that a
-- fixed nonzero output has two scalar transverse polarizations and that both
-- pairing and mass split without cross terms.
--
-- Agda already has a native same-carrier version of the algebra: the periodic
-- helical projectors P+ and P- sum to a transverse vector, and R287 proves the
-- mixed real-Hermitian Gram terms vanish for ANY two same-output cells.
--
-- This owner propagates that pairwise fact through R383's exact signed finite
-- Gram fold.  No absolute value, row sum, Schur kernel or estimate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287

F : C3.RealField _
F = Rational.rationalRealField

plusCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
plusCell E I S k = Helical.helicalProjectorPlus E I S k

minusCell :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
minusCell E I S k = Helical.helicalProjectorMinus E I S k

mapPlus :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode → List (C3.Complex3 F) → List (C3.Complex3 F)
mapPlus E I S k [] = []
mapPlus E I S k (cell ∷ cells) =
  plusCell E I S k cell ∷ mapPlus E I S k cells

mapMinus :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode → List (C3.Complex3 F) → List (C3.Complex3 F)
mapMinus E I S k [] = []
mapMinus E I S k (cell ∷ cells) =
  minusCell E I S k cell ∷ mapMinus E I S k cells

data AllTransverse
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode) :
    List (C3.Complex3 F) → Set where
  transverse[] : AllTransverse E k []
  transverse∷ :
    ∀ {cell cells} →
    Helical.Transverse E k cell →
    AllTransverse E k cells →
    AllTransverse E k (cell ∷ cells)

pairGramHelicalSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (u v : C3.Complex3 F) →
  Helical.Transverse E k u →
  Helical.Transverse E k v →
  R383.pairGram u v
  ≡ R383.pairGram (plusCell E I S k u) (plusCell E I S k v)
      + R383.pairGram (minusCell E I S k u) (minusCell E I S k v)
pairGramHelicalSplit E I S L k u v uT vT =
  let
    up = plusCell E I S k u
    um = minusCell E I S k u
    vp = plusCell E I S k v
    vm = minusCell E I S k v

    uSplit : C3.complex3Add up um ≡ u
    uSplit = Helical.velocityHelicalDecomposition L k u uT

    vSplit : C3.complex3Add vp vm ≡ v
    vSplit = Helical.velocityHelicalDecomposition L k v vT

    expandedCross :
      R179.realHermitianCross
        (C3.complex3Add up um) (C3.complex3Add vp vm)
      ≡
      (R179.realHermitianCross up vp + R179.realHermitianCross up vm)
      + (R179.realHermitianCross um vp + R179.realHermitianCross um vm)
    expandedCross =
      trans
        (R291.realCrossAddLeft up um (C3.complex3Add vp vm))
        (cong₂ _+_
          (R291.realCrossAddRight up vp vm)
          (R291.realCrossAddRight um vp vm))

    plusMinusZero : R179.realHermitianCross up vm ≡ 0ℚ
    plusMinusZero = R287.outputPlusMinusRealGramZero E I S L k u v

    minusPlusZero : R179.realHermitianCross um vp ≡ 0ℚ
    minusPlusZero = R287.outputMinusPlusRealGramZero E I S L k u v

    surviving :
      R291.two *
        ((R179.realHermitianCross up vp + R179.realHermitianCross up vm)
        + (R179.realHermitianCross um vp + R179.realHermitianCross um vm))
      ≡ R383.pairGram up vp + R383.pairGram um vm
    surviving rewrite plusMinusZero | minusPlusZero =
      solve
        (R179.realHermitianCross up vp
          ∷ R179.realHermitianCross um vm ∷ [])
  in
  trans
    (cong₂ R383.pairGram (sym uSplit) (sym vSplit))
    (trans
      (cong (R291.two *_) expandedCross)
      surviving)

headPairSumHelicalSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (left : C3.Complex3 F) →
  (rest : List (C3.Complex3 F)) →
  Helical.Transverse E k left →
  AllTransverse E k rest →
  R383.headPairSum left rest
  ≡ R383.headPairSum (plusCell E I S k left) (mapPlus E I S k rest)
      + R383.headPairSum (minusCell E I S k left) (mapMinus E I S k rest)
headPairSumHelicalSplit E I S L k left [] leftT transverse[] = solve []
headPairSumHelicalSplit E I S L k left (right ∷ rest) leftT
    (transverse∷ rightT restT) =
  let
    pair = pairGramHelicalSplit E I S L k left right leftT rightT
    tail = headPairSumHelicalSplit E I S L k left rest leftT restT

    lp = R383.pairGram
      (plusCell E I S k left) (plusCell E I S k right)
    lm = R383.pairGram
      (minusCell E I S k left) (minusCell E I S k right)
    tp = R383.headPairSum
      (plusCell E I S k left) (mapPlus E I S k rest)
    tm = R383.headPairSum
      (minusCell E I S k left) (mapMinus E I S k rest)
  in
  trans
    (cong₂ _+_ pair tail)
    (solve (lp ∷ lm ∷ tp ∷ tm ∷ []))

allPairSumHelicalSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (cells : List (C3.Complex3 F)) →
  AllTransverse E k cells →
  R383.allPairSum cells
  ≡ R383.allPairSum (mapPlus E I S k cells)
      + R383.allPairSum (mapMinus E I S k cells)
allPairSumHelicalSplit E I S L k [] transverse[] = solve []
allPairSumHelicalSplit E I S L k (cell ∷ cells)
    (transverse∷ cellT cellsT) =
  let
    head = headPairSumHelicalSplit E I S L k cell cells cellT cellsT
    tail = allPairSumHelicalSplit E I S L k cells cellsT

    hp = R383.headPairSum
      (plusCell E I S k cell) (mapPlus E I S k cells)
    hm = R383.headPairSum
      (minusCell E I S k cell) (mapMinus E I S k cells)
    tp = R383.allPairSum (mapPlus E I S k cells)
    tm = R383.allPairSum (mapMinus E I S k cells)
  in
  trans
    (cong₂ _+_ head tail)
    (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

round474SignedGramHelicitySplitClosed : Bool
round474SignedGramHelicitySplitClosed = true

round474MixedHelicityGramTermsExactlyZero : Bool
round474MixedHelicityGramTermsExactlyZero = true

round474AbsoluteValueIntroduced : Bool
round474AbsoluteValueIntroduced = false

round474ConcreteL2MassSplitWelded : Bool
round474ConcreteL2MassSplitWelded = false

round474PhysicalScalarPlusGramBoundClosed : Bool
round474PhysicalScalarPlusGramBoundClosed = false

round474PhysicalScalarMinusGramBoundClosed : Bool
round474PhysicalScalarMinusGramBoundClosed = false

round474PackageAClosed : Bool
round474PackageAClosed = false

round474ClayPromotion : Bool
round474ClayPromotion = false

round474AbsoluteValueIntroducedIsFalse :
  round474AbsoluteValueIntroduced ≡ false
round474AbsoluteValueIntroducedIsFalse = refl

round474ConcreteL2MassSplitWeldedIsFalse :
  round474ConcreteL2MassSplitWelded ≡ false
round474ConcreteL2MassSplitWeldedIsFalse = refl
