module DASHI.Physics.Closure.NSTriadKNMixedHelicityCellEnergyProductBidiExact where

------------------------------------------------------------------------
-- MIXED-HELICITY CELL -> MODAL ENERGY PRODUCT
--
-- Reuse only existing exact rational owners:
--   R475: ||u||^2 = ||u+||^2 + ||u-||^2 on a transverse mode;
--   R105: ||a x b||^2 <= ||a||^2 ||b||^2.
--
-- Hence each helical component is norm-dominated by the original mode and the
-- literal R224 mixedPlusMinus cell satisfies
--
--   ||u_p+ x u_q-||^2 <= ||u_p||^2 ||u_q||^2.
--
-- No shell count, fibre cardinality, statistical closure, or new analytic
-- hypothesis is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Rational.Base using (ℚ; _*_; _+_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeEnergyProductRound105Exact as R105
import DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact as R475

F : C3.RealField _
F = Rational.rationalRealField

helicalPlusNormBelowFull :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (u : C3.Complex3 F) →
  Helical.Transverse E k u →
  L2.complex3NormSquared (Helical.helicalProjectorPlus E I S k u)
  ≤ L2.complex3NormSquared u
helicalPlusNormBelowFull E I S L k u transverse =
  let
    plus = Helical.helicalProjectorPlus E I S k u
    minus = Helical.helicalProjectorMinus E I S k u
    split = R475.l2NormHelicalSplit E I S L k u transverse
    minusNN = Separation.complex3NormSquaredNonnegative minus
    plusBelowSum :
      L2.complex3NormSquared plus
      ≤ L2.complex3NormSquared plus + L2.complex3NormSquared minus
    plusBelowSum =
      subst
        (λ lower → lower ≤ L2.complex3NormSquared plus + L2.complex3NormSquared minus)
        (sym (ℚP.+-identityʳ (L2.complex3NormSquared plus)))
        (ℚP.+-mono-≤ ℚP.≤-refl minusNN)
  in
  subst
    (L2.complex3NormSquared plus ≤_)
    (sym split)
    plusBelowSum

helicalMinusNormBelowFull :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (u : C3.Complex3 F) →
  Helical.Transverse E k u →
  L2.complex3NormSquared (Helical.helicalProjectorMinus E I S k u)
  ≤ L2.complex3NormSquared u
helicalMinusNormBelowFull E I S L k u transverse =
  let
    plus = Helical.helicalProjectorPlus E I S k u
    minus = Helical.helicalProjectorMinus E I S k u
    split = R475.l2NormHelicalSplit E I S L k u transverse
    plusNN = Separation.complex3NormSquaredNonnegative plus
    minusBelowSum :
      L2.complex3NormSquared minus
      ≤ L2.complex3NormSquared plus + L2.complex3NormSquared minus
    minusBelowSum =
      ℚP.≤-trans
        (subst
          (λ lower → lower ≤ L2.complex3NormSquared minus + L2.complex3NormSquared plus)
          (sym (ℚP.+-identityʳ (L2.complex3NormSquared minus)))
          (ℚP.+-mono-≤ ℚP.≤-refl plusNN))
        (ℚP.≤-reflexive
          (ℚP.+-comm (L2.complex3NormSquared minus) (L2.complex3NormSquared plus)))
  in
  subst
    (L2.complex3NormSquared minus ≤_)
    (sym split)
    minusBelowSum

mixedPlusMinusCellBelowEnergyProduct :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  ((mode : Z3.FourierMode) → Helical.Transverse E mode (velocity mode)) →
  (tau : Physical.PhysicalTriadIncidence) →
  L2.complex3NormSquared (R224.mixedPlusMinus S velocity tau)
  ≤ L2.complex3NormSquared (velocity (Physical.p tau))
      * L2.complex3NormSquared (velocity (Physical.q tau))
mixedPlusMinusCellBelowEnergyProduct E I S L velocity velocityTransverse tau =
  let
    p = Physical.p tau
    q = Physical.q tau
    uP = velocity p
    uQ = velocity q
    pPlus = Helical.helicalProjectorPlus E I S p uP
    qMinus = Helical.helicalProjectorMinus E I S q uQ

    crossBound = R105.crossNormSquaredBelowProduct pPlus qMinus
    pBound = helicalPlusNormBelowFull E I S L p uP (velocityTransverse p)
    qBound = helicalMinusNormBelowFull E I S L q uQ (velocityTransverse q)

    qMinusNN = Separation.complex3NormSquaredNonnegative qMinus
    pFullNN = Separation.complex3NormSquaredNonnegative uP

    firstProduct :
      L2.complex3NormSquared pPlus * L2.complex3NormSquared qMinus
      ≤ L2.complex3NormSquared uP * L2.complex3NormSquared qMinus
    firstProduct =
      let instance qNN = nonNegative qMinusNN
      in ℚP.*-monoʳ-≤-nonNeg (L2.complex3NormSquared qMinus) pBound

    secondProduct :
      L2.complex3NormSquared uP * L2.complex3NormSquared qMinus
      ≤ L2.complex3NormSquared uP * L2.complex3NormSquared uQ
    secondProduct =
      let instance pNN = nonNegative pFullNN
      in ℚP.*-monoˡ-≤-nonNeg (L2.complex3NormSquared uP) qBound
  in
  ℚP.≤-trans crossBound (ℚP.≤-trans firstProduct secondProduct)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

mixedHelicityCellEnergyProductClosed : Bool
mixedHelicityCellEnergyProductClosed = true

mixedHelicityCellBoundIntroducesCardinalityTax : Bool
mixedHelicityCellBoundIntroducesCardinalityTax = false

mixedHelicityWeightedFoldUniformityClosed : Bool
mixedHelicityWeightedFoldUniformityClosed = false

clayPromotion : Bool
clayPromotion = false
