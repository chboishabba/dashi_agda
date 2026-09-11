module DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact where

------------------------------------------------------------------------
-- TIMESTAMP
-- 2026-09-11 20:46 AEST (UTC+10)
--
-- PURPOSE
-- Thin same-object adaptor for the homochiral part of R571.
--
-- On the exact rational physical carrier:
--   R571 signed curl eigenvalues  ->  R311 signed radial differences
--   R311 signed radial difference -> Round27 radial multiplier commutator.
--
-- This owner introduces NO analytic estimate.  In particular it does not
-- manufacture the radial-near amplitude certificate, a six-three gain, an
-- R568 spacetime budget, or any heterochiral promotion.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralThreeLegWaleffeCommonAmplitudeRound93Exact as R93
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNInnerHelicalComponentCommutatorRound571Exact as R571

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- 1. Helicity-sign transport into R311's scalar route classifier.
------------------------------------------------------------------------

toR311Sign : Helical.HelicitySign → R311.HelicitySign
toR311Sign Helical.plus = R311.plus
toR311Sign Helical.minus = R311.minus

radialMultiplier :
  R311.HelicitySign →
  Helical.HelicalModeScalars F →
  R27.MultiplierDualCarrier
radialMultiplier sign S =
  R27.multiplier-dual-carrier
    (λ mode → R311.signedRadius sign (Helical.modeNorm S mode))

------------------------------------------------------------------------
-- 2. Round27 already owns the signed translation-multiplier commutator.
--    Here we only identify its coefficient with R311 when k-l = input.
------------------------------------------------------------------------

round27RadialDifferenceAt :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars F) →
  (shift output input : Z3.FourierMode) →
  R27.shiftedMode shift output ≡ input →
  R27.multiplierSymbol
    (R27.multiplierDifference
      (radialMultiplier sign S)
      (R27.translateMultiplierSymbol shift (radialMultiplier sign S)))
    output
  ≡
  R311.innerMultiplierDifference sign sign
    (Helical.modeNorm S input)
    (Helical.modeNorm S output)
round27RadialDifferenceAt sign S shift output input shiftedIsInput
  rewrite shiftedIsInput = refl

round27RadialTranslationMultiplierCommutatorExact :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars F) →
  (shift : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (output : Z3.FourierMode) →
  R27.stateCoefficient
    (R27.translationMultiplierCommutator
      (radialMultiplier sign S) shift state) output
  ≡
  R27.stateCoefficient
    (R27.signedDifferenceCommutator
      (radialMultiplier sign S) shift state) output
round27RadialTranslationMultiplierCommutatorExact sign S =
  R27.translationMultiplierCommutatorExact (radialMultiplier sign S)

------------------------------------------------------------------------
-- 3. Literal R571 physical carrier -> exact R311 homochiral scalar gap.
------------------------------------------------------------------------

module PhysicalHomochiral
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module C = R571.Componentwise system S L velocityTransverse

  plusEigenvalueDifferenceIsR311 :
    (tau : Physical.PhysicalTriadIncidence) →
    (pRadius : R455.ExplicitRadiusWitness E I S (Physical.p tau)) →
    (qRadius : R455.ExplicitRadiusWitness E I S (Physical.q tau)) →
    C3.complexSubtract
      (C.signedEigenvalue Helical.plus (Physical.q tau))
      (C.signedEigenvalue Helical.plus (Physical.p tau))
    ≡
    C3.realEmbed F
      (R311.innerMultiplierDifference R311.plus R311.plus
        (R455.radius pRadius) (R455.radius qRadius))
  plusEigenvalueDifferenceIsR311 tau pRadius qRadius
    rewrite R455.radiusMeaning pRadius | R455.radiusMeaning qRadius =
    trans
      (R93.realEmbedSubtract
        (Helical.modeNorm S (Physical.q tau))
        (Helical.modeNorm S (Physical.p tau)))
      (cong (C3.realEmbed F)
        (solve
          ( Helical.modeNorm S (Physical.p tau)
          ∷ Helical.modeNorm S (Physical.q tau)
          ∷ [])))

  minusEigenvalueDifferenceIsR311 :
    (tau : Physical.PhysicalTriadIncidence) →
    (pRadius : R455.ExplicitRadiusWitness E I S (Physical.p tau)) →
    (qRadius : R455.ExplicitRadiusWitness E I S (Physical.q tau)) →
    C3.complexSubtract
      (C.signedEigenvalue Helical.minus (Physical.q tau))
      (C.signedEigenvalue Helical.minus (Physical.p tau))
    ≡
    C3.realEmbed F
      (R311.innerMultiplierDifference R311.minus R311.minus
        (R455.radius pRadius) (R455.radius qRadius))
  minusEigenvalueDifferenceIsR311 tau pRadius qRadius
    rewrite R455.radiusMeaning pRadius | R455.radiusMeaning qRadius =
    trans
      (R93.realEmbedSubtract
        (- Helical.modeNorm S (Physical.q tau))
        (- Helical.modeNorm S (Physical.p tau)))
      (cong (C3.realEmbed F)
        (solve
          ( Helical.modeNorm S (Physical.p tau)
          ∷ Helical.modeNorm S (Physical.q tau)
          ∷ [])))

  homochiralRadialVector :
    (routeSign : R311.HelicitySign) →
    (helicalSign : Helical.HelicitySign) →
    (tau : Physical.PhysicalTriadIncidence) →
    C3.Complex3 F
  homochiralRadialVector routeSign helicalSign tau =
    C3.complex3Scale
      (C3.realEmbed F
        (R311.innerMultiplierDifference routeSign routeSign
          (Helical.modeNorm S (Physical.p tau))
          (Helical.modeNorm S (Physical.q tau))))
      (C3.lerayProject3 E I (Physical.k tau)
        (Cross.complex3Cross
          (C.component helicalSign (Physical.p tau))
          (C.component helicalSign (Physical.q tau))))

  plusMultiplierDifferenceVectorIsRadial :
    (tau : Physical.PhysicalTriadIncidence) →
    C.multiplierDifferenceVector tau Helical.plus Helical.plus
    ≡ homochiralRadialVector R311.plus Helical.plus tau
  plusMultiplierDifferenceVectorIsRadial tau =
    cong
      (λ scalar →
        C3.complex3Scale scalar
          (C3.lerayProject3 E I (Physical.k tau)
            (Cross.complex3Cross
              (C.component Helical.plus (Physical.p tau))
              (C.component Helical.plus (Physical.q tau)))))
      (trans
        (R93.realEmbedSubtract
          (Helical.modeNorm S (Physical.q tau))
          (Helical.modeNorm S (Physical.p tau)))
        (cong (C3.realEmbed F)
          (solve
            ( Helical.modeNorm S (Physical.p tau)
            ∷ Helical.modeNorm S (Physical.q tau)
            ∷ []))))

  minusMultiplierDifferenceVectorIsRadial :
    (tau : Physical.PhysicalTriadIncidence) →
    C.multiplierDifferenceVector tau Helical.minus Helical.minus
    ≡ homochiralRadialVector R311.minus Helical.minus tau
  minusMultiplierDifferenceVectorIsRadial tau =
    cong
      (λ scalar →
        C3.complex3Scale scalar
          (C3.lerayProject3 E I (Physical.k tau)
            (Cross.complex3Cross
              (C.component Helical.minus (Physical.p tau))
              (C.component Helical.minus (Physical.q tau)))))
      (trans
        (R93.realEmbedSubtract
          (- Helical.modeNorm S (Physical.q tau))
          (- Helical.modeNorm S (Physical.p tau)))
        (cong (C3.realEmbed F)
          (solve
            ( Helical.modeNorm S (Physical.p tau)
            ∷ Helical.modeNorm S (Physical.q tau)
            ∷ []))))

------------------------------------------------------------------------
-- Status / firewalls.
------------------------------------------------------------------------

r571HomochiralRadialCarrierWeldClosed : Bool
r571HomochiralRadialCarrierWeldClosed = true

r571Round27RadialMultiplierSpecializationClosed : Bool
r571Round27RadialMultiplierSpecializationClosed = true

r571RadialNearAnalyticGainClosed : Bool
r571RadialNearAnalyticGainClosed = false

r571HeterochiralPromotionIntroduced : Bool
r571HeterochiralPromotionIntroduced = false

r571R568SpacetimeBudgetClosedHere : Bool
r571R568SpacetimeBudgetClosedHere = false

r571HomochiralRadialCarrierWeldClosedIsTrue :
  r571HomochiralRadialCarrierWeldClosed ≡ true
r571HomochiralRadialCarrierWeldClosedIsTrue = refl

r571RadialNearAnalyticGainClosedIsFalse :
  r571RadialNearAnalyticGainClosed ≡ false
r571RadialNearAnalyticGainClosedIsFalse = refl

r571HeterochiralPromotionIntroducedIsFalse :
  r571HeterochiralPromotionIntroduced ≡ false
r571HeterochiralPromotionIntroducedIsFalse = refl
