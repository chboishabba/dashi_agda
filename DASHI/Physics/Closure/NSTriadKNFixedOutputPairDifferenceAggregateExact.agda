module DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceAggregateExact where

------------------------------------------------------------------------
-- P2 / COMPLETE-GRAPH PAIR-DIFFERENCE MASS IS THE LITERAL R574 NORM SUM
--
-- P1 (NSTriadKNFixedOutputPairDifferenceDebtExact) lifts the Balaban finite
-- rational complete-graph identity to the six real coordinates of Complex3.
-- This owner pays the aggregate same-object seam left by P1:
--
--   pairDifferenceMass3(cells)
--     = sum_{i<j} ||cells_i - cells_j||^2
--
-- and then specializes that equality to R207's literal fixed-output partner
-- list.  Finally the same sum is written through PR #890's R205 -> R574/R446
-- adapter, so every summand is literally the norm square of the already-owned
-- R574 difference value.
--
-- No lower bound is introduced here.  In particular this file does not infer
-- radial/angular depletion, centered second-moment gain, shell uniformity,
-- spacetime control or Clay promotion.  The remaining physical problem is the
-- lower bound on this now-literal aggregate pair-difference mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.YangMills.BalabanFiniteRationalCauchyExact as YM

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNCauchyVectorPolarizationRound574Exact as R574
import DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact as Adapter
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceDebtExact as P1

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Literal complete-graph sum of Complex3 difference norm squares.
------------------------------------------------------------------------

pairNormFrom3 : C3.Complex3 F → List (C3.Complex3 F) → ℚ
pairNormFrom3 left [] = 0ℚ
pairNormFrom3 left (right ∷ rest) =
  L2.complex3NormSquared (C3.complex3Subtract left right)
  + pairNormFrom3 left rest

pairNormMass3 : List (C3.Complex3 F) → ℚ
pairNormMass3 [] = 0ℚ
pairNormMass3 (head ∷ rest) =
  pairNormFrom3 head rest + pairNormMass3 rest

coordinatePairDifferenceFrom3 :
  C3.Complex3 F → List (C3.Complex3 F) → ℚ
coordinatePairDifferenceFrom3 value values =
  YM.pairDifferenceFrom (P1.xReal value) (P1.coordinateList P1.xReal values)
  + YM.pairDifferenceFrom (P1.xImag value) (P1.coordinateList P1.xImag values)
  + YM.pairDifferenceFrom (P1.yReal value) (P1.coordinateList P1.yReal values)
  + YM.pairDifferenceFrom (P1.yImag value) (P1.coordinateList P1.yImag values)
  + YM.pairDifferenceFrom (P1.zReal value) (P1.coordinateList P1.zReal values)
  + YM.pairDifferenceFrom (P1.zImag value) (P1.coordinateList P1.zImag values)

pairNormFrom3IsCoordinatePairDifferenceFrom3 :
  ∀ value values →
  pairNormFrom3 value values ≡ coordinatePairDifferenceFrom3 value values
pairNormFrom3IsCoordinatePairDifferenceFrom3 value [] =
  solve []
pairNormFrom3IsCoordinatePairDifferenceFrom3
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi))
    (C3.complex3
      (C3.complex ar ai)
      (C3.complex br bi)
      (C3.complex cr ci) ∷ rest)
  rewrite pairNormFrom3IsCoordinatePairDifferenceFrom3
    (C3.complex3
      (C3.complex xr xi)
      (C3.complex yr yi)
      (C3.complex zr zi)) rest =
  solve
    ( xr ∷ xi ∷ yr ∷ yi ∷ zr ∷ zi
    ∷ ar ∷ ai ∷ br ∷ bi ∷ cr ∷ ci
    ∷ YM.pairDifferenceFrom xr (P1.coordinateList P1.xReal rest)
    ∷ YM.pairDifferenceFrom xi (P1.coordinateList P1.xImag rest)
    ∷ YM.pairDifferenceFrom yr (P1.coordinateList P1.yReal rest)
    ∷ YM.pairDifferenceFrom yi (P1.coordinateList P1.yImag rest)
    ∷ YM.pairDifferenceFrom zr (P1.coordinateList P1.zReal rest)
    ∷ YM.pairDifferenceFrom zi (P1.coordinateList P1.zImag rest)
    ∷ [])

pairDifferenceMass3IsPairNormMass3 : ∀ cells →
  P1.pairDifferenceMass3 cells ≡ pairNormMass3 cells
pairDifferenceMass3IsPairNormMass3 [] = refl
pairDifferenceMass3IsPairNormMass3 (head ∷ rest)
  rewrite pairNormFrom3IsCoordinatePairDifferenceFrom3 head rest
        | pairDifferenceMass3IsPairNormMass3 rest =
  solve
    ( YM.pairDifferenceFrom (P1.xReal head) (P1.coordinateList P1.xReal rest)
    ∷ YM.pairDifferenceFrom (P1.xImag head) (P1.coordinateList P1.xImag rest)
    ∷ YM.pairDifferenceFrom (P1.yReal head) (P1.coordinateList P1.yReal rest)
    ∷ YM.pairDifferenceFrom (P1.yImag head) (P1.coordinateList P1.yImag rest)
    ∷ YM.pairDifferenceFrom (P1.zReal head) (P1.coordinateList P1.zReal rest)
    ∷ YM.pairDifferenceFrom (P1.zImag head) (P1.coordinateList P1.zImag rest)
    ∷ YM.pairDifferenceEnergy (P1.coordinateList P1.xReal rest)
    ∷ YM.pairDifferenceEnergy (P1.coordinateList P1.xImag rest)
    ∷ YM.pairDifferenceEnergy (P1.coordinateList P1.yReal rest)
    ∷ YM.pairDifferenceEnergy (P1.coordinateList P1.yImag rest)
    ∷ YM.pairDifferenceEnergy (P1.coordinateList P1.zReal rest)
    ∷ YM.pairDifferenceEnergy (P1.coordinateList P1.zImag rest)
    ∷ [])

------------------------------------------------------------------------
-- 2. Literal fixed-output specialization.
------------------------------------------------------------------------

fixedOutputPairDifferenceIsLiteralNormMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output)) →
  P1.fixedOutputPairDifferenceMass entries
  ≡ pairNormMass3 (R207.fixedOutputPartnerCells entries)
fixedOutputPairDifferenceIsLiteralNormMass entries =
  pairDifferenceMass3IsPairNormMass3 (R207.fixedOutputPartnerCells entries)

------------------------------------------------------------------------
-- 3. The same aggregate written literally through the PR #890 R574 adapter.
------------------------------------------------------------------------

r574PairNormFrom :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode} →
  (rate : ℚ) → Positive rate →
  R207.FixedOutputLocalizedComparablePartner system output →
  List (R207.FixedOutputLocalizedComparablePartner system output) → ℚ
r574PairNormFrom rate ratePositive head [] = 0ℚ
r574PairNormFrom rate ratePositive head (other ∷ rest) =
  L2.complex3NormSquared
    (R446.value
      (R574.toDifferenceCell574
        (Adapter.toR574PartnerDifference
          rate ratePositive (R207.partner head) (R207.partner other))))
  + r574PairNormFrom rate ratePositive head rest

r574PairNormMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode} →
  (rate : ℚ) → Positive rate →
  List (R207.FixedOutputLocalizedComparablePartner system output) → ℚ
r574PairNormMass rate ratePositive [] = 0ℚ
r574PairNormMass rate ratePositive (head ∷ rest) =
  r574PairNormFrom rate ratePositive head rest
  + r574PairNormMass rate ratePositive rest

r574PairNormFromIsLiteralCellNormFrom :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (head : R207.FixedOutputLocalizedComparablePartner system output)
    (rest : List (R207.FixedOutputLocalizedComparablePartner system output)) →
  r574PairNormFrom rate ratePositive head rest
  ≡ pairNormFrom3
      (Adapter.compressedPartnerVector (R207.partner head))
      (R207.fixedOutputPartnerCells rest)
r574PairNormFromIsLiteralCellNormFrom rate ratePositive head [] = refl
r574PairNormFromIsLiteralCellNormFrom rate ratePositive head (other ∷ rest)
  rewrite Adapter.r446DifferenceValueIsCompressedPartnerDifference
            rate ratePositive (R207.partner head) (R207.partner other)
        | r574PairNormFromIsLiteralCellNormFrom
            rate ratePositive head rest =
  refl

r574PairNormMassIsLiteralFixedOutputNormMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output)) →
  r574PairNormMass rate ratePositive entries
  ≡ pairNormMass3 (R207.fixedOutputPartnerCells entries)
r574PairNormMassIsLiteralFixedOutputNormMass rate ratePositive [] = refl
r574PairNormMassIsLiteralFixedOutputNormMass
    rate ratePositive (head ∷ rest)
  rewrite r574PairNormFromIsLiteralCellNormFrom
            rate ratePositive head rest
        | r574PairNormMassIsLiteralFixedOutputNormMass
            rate ratePositive rest =
  refl

fixedOutputPairDifferenceMassIsR574PairNormMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    {output : DASHI.Physics.Closure.NSIntegerFourierLattice.FourierMode}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (entries : List (R207.FixedOutputLocalizedComparablePartner system output)) →
  P1.fixedOutputPairDifferenceMass entries
  ≡ r574PairNormMass rate ratePositive entries
fixedOutputPairDifferenceMassIsR574PairNormMass
    rate ratePositive entries =
  trans
    (fixedOutputPairDifferenceIsLiteralNormMass entries)
    (sym
      (r574PairNormMassIsLiteralFixedOutputNormMass
        rate ratePositive entries))

------------------------------------------------------------------------
-- Status: P2 aggregate same-object splice closed; P3 lower bound remains.
------------------------------------------------------------------------

fixedOutputPairDifferenceAggregateClosed : Bool
fixedOutputPairDifferenceAggregateClosed = true

fixedOutputPairDifferenceAggregateUsesR574LiteralDifferences : Bool
fixedOutputPairDifferenceAggregateUsesR574LiteralDifferences = true

fixedOutputPairDifferenceLowerBoundClosed : Bool
fixedOutputPairDifferenceLowerBoundClosed = false

fixedOutputPairDifferenceAggregateClayPromotion : Bool
fixedOutputPairDifferenceAggregateClayPromotion = false

fixedOutputPairDifferenceAggregateClosedIsTrue :
  fixedOutputPairDifferenceAggregateClosed ≡ true
fixedOutputPairDifferenceAggregateClosedIsTrue = refl

fixedOutputPairDifferenceAggregateUsesR574LiteralDifferencesIsTrue :
  fixedOutputPairDifferenceAggregateUsesR574LiteralDifferences ≡ true
fixedOutputPairDifferenceAggregateUsesR574LiteralDifferencesIsTrue = refl

fixedOutputPairDifferenceLowerBoundClosedIsFalse :
  fixedOutputPairDifferenceLowerBoundClosed ≡ false
fixedOutputPairDifferenceLowerBoundClosedIsFalse = refl

fixedOutputPairDifferenceAggregateClayPromotionIsFalse :
  fixedOutputPairDifferenceAggregateClayPromotion ≡ false
fixedOutputPairDifferenceAggregateClayPromotionIsFalse = refl
