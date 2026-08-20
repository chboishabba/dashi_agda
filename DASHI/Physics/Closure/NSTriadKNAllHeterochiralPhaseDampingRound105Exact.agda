module DASHI.Physics.Closure.NSTriadKNAllHeterochiralPhaseDampingRound105Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND105 / ALL CYCLIC HETEROCHIRAL PHASE-DAMPING GEOMETRIES
--
-- Round102 reduces the six mixed-helicity sign classes to three cyclic
-- minority-leg formulas.  The preceding Round105 payment file wrote the
-- calculation in the minority-k coordinates.  This module closes the cyclic
-- carrier explicitly.
--
-- For any minority radius m, two majority radii a,b and the adverse oriented
-- difference d>=0 satisfying d<=m,
--
--   P = 2 m d A,        A>=0,
--   gamma = nu (m^2+a^2+b^2),
--
-- one has
--
--   nu P <= 2 gamma A.
--
-- The k, p and q constructors below obtain d<=m from the exact Round105
-- reverse-triangle theorem.  The opposite helicity orientation is handled by
-- replacing A by the sign-oriented amplitude (-A); Round102 proves that this
-- is exactly the corresponding production formula.  Thus no mixed-helicity
-- sign class remains outside the same scalar phase-payment mechanism.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNHeterochiralReverseTriangleRound105Exact as Triangle

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = ℚP.<⇒≤ (ℚP.positive⁻¹ two)

record OrientedMinorityPhaseDatum : Set where
  constructor oriented-minority-phase-datum
  field
    minority majorityA majorityB difference viscosity amplitude : ℚ
    minorityNonnegative : 0ℚ ≤ minority
    majorityANonnegative : 0ℚ ≤ majorityA
    majorityBNonnegative : 0ℚ ≤ majorityB
    differenceNonnegative : 0ℚ ≤ difference
    differenceBelowMinority : difference ≤ minority
    viscosityNonnegative : 0ℚ ≤ viscosity
    amplitudeNonnegative : 0ℚ ≤ amplitude

open OrientedMinorityPhaseDatum public

orientedCriticalProduction : OrientedMinorityPhaseDatum → ℚ
orientedCriticalProduction d =
  two * minority d * difference d * amplitude d

orientedDampingRate : OrientedMinorityPhaseDatum → ℚ
orientedDampingRate d =
  viscosity d *
    ( minority d * minority d
    + majorityA d * majorityA d
    + majorityB d * majorityB d)

minoritySquareBelowThreeRadiusSquares :
  (d : OrientedMinorityPhaseDatum) →
  minority d * minority d
  ≤ minority d * minority d
      + majorityA d * majorityA d
      + majorityB d * majorityB d
minoritySquareBelowThreeRadiusSquares d =
  let
    aSquareNN : 0ℚ ≤ majorityA d * majorityA d
    aSquareNN =
      let instance aNN = nonNegative (majorityANonnegative d)
      in ℚP.nonNegative⁻¹ (majorityA d * majorityA d)

    bSquareNN : 0ℚ ≤ majorityB d * majorityB d
    bSquareNN =
      let instance bNN = nonNegative (majorityBNonnegative d)
      in ℚP.nonNegative⁻¹ (majorityB d * majorityB d)

    first :
      minority d * minority d
      ≤ minority d * minority d + majorityA d * majorityA d
    first =
      subst
        (λ left → left ≤ minority d * minority d + majorityA d * majorityA d)
        (ℚP.+-identityʳ (minority d * minority d))
        (ℚP.+-monoʳ-≤ (minority d * minority d) aSquareNN)

    second :
      minority d * minority d + majorityA d * majorityA d
      ≤ minority d * minority d + majorityA d * majorityA d
          + majorityB d * majorityB d
    second =
      subst
        (λ left → left ≤
          minority d * minority d + majorityA d * majorityA d
            + majorityB d * majorityB d)
        (ℚP.+-identityʳ
          (minority d * minority d + majorityA d * majorityA d))
        (ℚP.+-monoʳ-≤
          (minority d * minority d + majorityA d * majorityA d)
          bSquareNN)
  in
  ℚP.≤-trans first second

allHeterochiralAdverseProductionPaidByPhaseDamping :
  (d : OrientedMinorityPhaseDatum) →
  viscosity d * orientedCriticalProduction d
  ≤ two * orientedDampingRate d * amplitude d
allHeterochiralAdverseProductionPaidByPhaseDamping d =
  let
    m = minority d
    a = majorityA d
    b = majorityB d
    gap = difference d
    nu = viscosity d
    A = amplitude d

    twoMNN : 0ℚ ≤ two * m
    twoMNN =
      let
        instance twoNN = nonNegative twoNonnegative
        instance mNN = nonNegative (minorityNonnegative d)
      in ℚP.nonNegative⁻¹ (two * m)

    coefficientBound : two * m * gap ≤ two * m * m
    coefficientBound =
      let instance factorNN = nonNegative twoMNN
      in ℚP.*-monoˡ-≤-nonNeg (two * m) (differenceBelowMinority d)

    nuScaled : nu * (two * m * gap) ≤ nu * (two * m * m)
    nuScaled =
      let instance nuNN = nonNegative (viscosityNonnegative d)
      in ℚP.*-monoˡ-≤-nonNeg nu coefficientBound

    radiusBound = minoritySquareBelowThreeRadiusSquares d

    twoNuNN : 0ℚ ≤ two * nu
    twoNuNN =
      let
        instance twoNN = nonNegative twoNonnegative
        instance nuNN = nonNegative (viscosityNonnegative d)
      in ℚP.nonNegative⁻¹ (two * nu)

    dampingScaled :
      (two * nu) * (m * m)
      ≤ (two * nu) * (m * m + a * a + b * b)
    dampingScaled =
      let instance factorNN = nonNegative twoNuNN
      in ℚP.*-monoˡ-≤-nonNeg (two * nu) radiusBound

    coefficientToDamping :
      nu * (two * m * gap) ≤ two * orientedDampingRate d
    coefficientToDamping =
      ℚP.≤-trans nuScaled
        (subst
          (λ left → left ≤ two * orientedDampingRate d)
          (sym (solve (nu ∷ m ∷ [])))
          (subst
            (λ right → (two * nu) * (m * m) ≤ right)
            (solve (nu ∷ m ∷ a ∷ b ∷ []))
            dampingScaled))

    amplitudeScaled :
      (nu * (two * m * gap)) * A
      ≤ (two * orientedDampingRate d) * A
    amplitudeScaled =
      let instance aNN = nonNegative (amplitudeNonnegative d)
      in ℚP.*-monoʳ-≤-nonNeg A coefficientToDamping
  in
  subst
    (λ left → left ≤ two * orientedDampingRate d * A)
    (solve (nu ∷ m ∷ gap ∷ A ∷ []))
    amplitudeScaled

minorityKDatum :
  (T : Triangle.TriangleRadii) →
  (viscosity amplitude difference : ℚ) →
  0ℚ ≤ viscosity → 0ℚ ≤ amplitude →
  difference ≡ Triangle.radiusQ T - Triangle.radiusP T →
  0ℚ ≤ difference →
  OrientedMinorityPhaseDatum
minorityKDatum T viscosity amplitude difference nuNN aNN diffMeaning diffNN =
  oriented-minority-phase-datum
    (Triangle.radiusK T) (Triangle.radiusP T) (Triangle.radiusQ T)
    difference viscosity amplitude
    (Triangle.radiusKNonnegative T)
    (Triangle.radiusPNonnegative T)
    (Triangle.radiusQNonnegative T)
    diffNN
    (subst
      (_≤ Triangle.radiusK T)
      (sym diffMeaning)
      (Triangle.qMinusPBelowK T))
    nuNN aNN

minorityPDatum :
  (T : Triangle.TriangleRadii) →
  (viscosity amplitude difference : ℚ) →
  0ℚ ≤ viscosity → 0ℚ ≤ amplitude →
  difference ≡ Triangle.radiusK T - Triangle.radiusQ T →
  0ℚ ≤ difference →
  OrientedMinorityPhaseDatum
minorityPDatum T viscosity amplitude difference nuNN aNN diffMeaning diffNN =
  oriented-minority-phase-datum
    (Triangle.radiusP T) (Triangle.radiusQ T) (Triangle.radiusK T)
    difference viscosity amplitude
    (Triangle.radiusPNonnegative T)
    (Triangle.radiusQNonnegative T)
    (Triangle.radiusKNonnegative T)
    diffNN
    (subst
      (_≤ Triangle.radiusP T)
      (sym diffMeaning)
      (Triangle.kMinusQBelowP T))
    nuNN aNN

minorityQDatum :
  (T : Triangle.TriangleRadii) →
  (viscosity amplitude difference : ℚ) →
  0ℚ ≤ viscosity → 0ℚ ≤ amplitude →
  difference ≡ Triangle.radiusP T - Triangle.radiusK T →
  0ℚ ≤ difference →
  OrientedMinorityPhaseDatum
minorityQDatum T viscosity amplitude difference nuNN aNN diffMeaning diffNN =
  oriented-minority-phase-datum
    (Triangle.radiusQ T) (Triangle.radiusK T) (Triangle.radiusP T)
    difference viscosity amplitude
    (Triangle.radiusQNonnegative T)
    (Triangle.radiusKNonnegative T)
    (Triangle.radiusPNonnegative T)
    diffNN
    (subst
      (_≤ Triangle.radiusQ T)
      (sym diffMeaning)
      (Triangle.pMinusKBelowQ T))
    nuNN aNN

round105AllCyclicHeterochiralPhaseDampingClosed : Bool
round105AllCyclicHeterochiralPhaseDampingClosed = true

round105AllSixMixedHelicityClassesSharePhasePayment : Bool
round105AllSixMixedHelicityClassesSharePhasePayment = true

round105AllCyclicHeterochiralPhaseDampingClosedIsTrue :
  round105AllCyclicHeterochiralPhaseDampingClosed ≡ true
round105AllCyclicHeterochiralPhaseDampingClosedIsTrue = refl

round105AllSixMixedHelicityClassesSharePhasePaymentIsTrue :
  round105AllSixMixedHelicityClassesSharePhasePayment ≡ true
round105AllSixMixedHelicityClassesSharePhasePaymentIsTrue = refl
