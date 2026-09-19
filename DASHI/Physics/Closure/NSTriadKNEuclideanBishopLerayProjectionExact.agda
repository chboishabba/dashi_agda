module DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayProjectionExact where

------------------------------------------------------------------------
-- A / LITERAL BISHOP-REAL LERAY PROJECTOR ON R^3 \ {0}
--
-- For q = |xi|^2 > 0 define
--
--   P_xi v = v - xi q^{-1} (xi dot v).
--
-- Coordinate expansion gives the exact Pythagorean identity
--
--   |P_xi v|^2
--      ~= |v|^2 - q^{-1} |xi dot v|^2,
--
-- hence squared norm contraction.  This is the whole-space Bishop-real
-- counterpart of NSTriadKNRationalComplex3LerayPythagoras and uses only the
-- constructive reciprocal law on the punctured frequency region.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopCauchyGramExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

complexSubtract :
  Physical.BishopComplex →
  Physical.BishopComplex →
  Physical.BishopComplex
complexSubtract a b =
  Physical.bishop-complex
    (BishopReal._-_
      (Physical.realPart a)
      (Physical.realPart b))
    (BishopReal._-_
      (Physical.imaginaryPart a)
      (Physical.imaginaryPart b))

record PuncturedFrequency : Set where
  constructor punctured-frequency
  field
    frequency : Euclidean.R3Frequency
    normSquaredPositive :
      BishopReal._<_ BishopReal.0ℝ
        (Heat.frequencyNormSquared frequency)

open PuncturedFrequency public

normSquaredNonzero :
  (point : PuncturedFrequency) →
  BishopReal._≄0
    (Heat.frequencyNormSquared (frequency point))
normSquaredNonzero point =
  Reciprocal.xNonzero (normSquaredPositive point)

inverseNormSquared :
  PuncturedFrequency → BishopReal.ℝ
inverseNormSquared point =
  BishopInverse._⁻¹
    (Heat.frequencyNormSquared (frequency point))
    (normSquaredNonzero point)

inverseNormSquaredNonnegative :
  (point : PuncturedFrequency) →
  BishopReal.NonNegative (inverseNormSquared point)
inverseNormSquaredNonnegative point =
  BishopP.pos⇒nonNeg
    (BishopInverse.posx⇒posx⁻¹
      (normSquaredNonzero point)
      (BishopP.0<x⇒posx (normSquaredPositive point)))

coordinateCorrection :
  BishopReal.ℝ →
  BishopReal.ℝ →
  Physical.BishopComplex →
  Physical.BishopComplex
coordinateCorrection inverse coordinate dot =
  Output.realScaleComplex
    (BishopReal._*_ inverse coordinate)
    dot

lerayProject :
  PuncturedFrequency →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
lerayProject point value =
  let
    xi = frequency point
    inverse = inverseNormSquared point
    dot = Output.frequencyDot xi value
  in
  Physical.bishop-complex3
    (complexSubtract
      (Physical.cx value)
      (coordinateCorrection inverse (Euclidean.x xi) dot))
    (complexSubtract
      (Physical.cy value)
      (coordinateCorrection inverse (Euclidean.y xi) dot))
    (complexSubtract
      (Physical.cz value)
      (coordinateCorrection inverse (Euclidean.z xi) dot))

lerayCorrection :
  PuncturedFrequency →
  Physical.BishopComplex3 →
  BishopReal.ℝ
lerayCorrection point value =
  BishopReal._*_
    (inverseNormSquared point)
    (Cauchy.complexModulusSquared
      (Output.frequencyDot (frequency point) value))

inverseSquaredTimesNorm :
  (point : PuncturedFrequency) →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_
        (inverseNormSquared point)
        (inverseNormSquared point))
      (Heat.frequencyNormSquared (frequency point)))
    (inverseNormSquared point)
inverseSquaredTimesNorm point =
  let
    q = Heat.frequencyNormSquared (frequency point)
    iq = inverseNormSquared point
    law = BishopInverse.*-inverseˡ q (normSquaredNonzero point)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 2
      (λ i q' →
        (i ⊗ i) ⊗ q'
        ⊜ i ⊗ (q' ⊗ i))
      BishopP.≃-refl
      iq q)
    (BishopP.≃-trans
      (BishopP.*-congˡ law)
      (BishopP.*-identityʳ iq))

lerayPythagoras :
  (point : PuncturedFrequency) →
  (value : Physical.BishopComplex3) →
  BishopReal._≃_
    (Cauchy.complex3NormSquared
      (lerayProject point value))
    (BishopReal._-_
      (Cauchy.complex3NormSquared value)
      (lerayCorrection point value))
lerayPythagoras point
    (Physical.bishop-complex3
      (Physical.bishop-complex xr xi)
      (Physical.bishop-complex yr yi)
      (Physical.bishop-complex zr zi)) =
  let
    k = frequency point
    kx = Euclidean.x k
    ky = Euclidean.y k
    kz = Euclidean.z k
    inverse = inverseNormSquared point

    dr =
      Cauchy.realDot3 k xr yr zr
    di =
      Cauchy.realDot3 k xi yi zi

    q = Heat.frequencyNormSquared k
    dotNorm =
      BishopReal._+_
        (Cauchy.square dr)
        (Cauchy.square di)
    valueNorm =
      Cauchy.complex3NormSquared
        (Physical.bishop-complex3
          (Physical.bishop-complex xr xi)
          (Physical.bishop-complex yr yi)
          (Physical.bishop-complex zr zi))

    inverseSquareNorm =
      inverseSquaredTimesNorm point

    open BishopP.ℝ-Solver

    expanded :
      BishopReal._≃_
        (Cauchy.complex3NormSquared
          (lerayProject point
            (Physical.bishop-complex3
              (Physical.bishop-complex xr xi)
              (Physical.bishop-complex yr yi)
              (Physical.bishop-complex zr zi))))
        (BishopReal._+_
          valueNorm
          (BishopReal._*_
            (BishopReal._-_
              (BishopReal._-_
                (BishopReal._*_
                  (BishopReal._*_ inverse inverse)
                  q)
                inverse)
              inverse)
            dotNorm))
    expanded =
      solve 10
        (λ kx' ky' kz' xr' xi' yr' yi' zr' zi' inv →
          (((xr' ⊖ ((inv ⊗ kx') ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr'))))
            ⊗
            (xr' ⊖ ((inv ⊗ kx') ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr')))))
           ⊕
           ((xi' ⊖ ((inv ⊗ kx') ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi'))))
            ⊗
            (xi' ⊖ ((inv ⊗ kx') ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi'))))))
          ⊕
          ((((yr' ⊖ ((inv ⊗ ky') ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr'))))
            ⊗
            (yr' ⊖ ((inv ⊗ ky') ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr')))))
           ⊕
           ((yi' ⊖ ((inv ⊗ ky') ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi'))))
            ⊗
            (yi' ⊖ ((inv ⊗ ky') ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi'))))))
           ⊕
           (((zr' ⊖ ((inv ⊗ kz') ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr'))))
            ⊗
            (zr' ⊖ ((inv ⊗ kz') ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr')))))
           ⊕
           ((zi' ⊖ ((inv ⊗ kz') ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi'))))
            ⊗
            (zi' ⊖ ((inv ⊗ kz') ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi')))))))
          ⊜
          (((xr'⊗xr' ⊕ xi'⊗xi')
            ⊕ ((yr'⊗yr' ⊕ yi'⊗yi')
              ⊕ (zr'⊗zr' ⊕ zi'⊗zi')))
           ⊕
           ((((inv⊗inv)
              ⊗
              ((kx'⊗kx') ⊕ ((ky'⊗ky') ⊕ (kz'⊗kz'))))
             ⊖ inv ⊖ inv)
            ⊗
            (((kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr'))
              ⊗
              (kx'⊗xr' ⊕ (ky'⊗yr' ⊕ kz'⊗zr')))
             ⊕
             ((kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi'))
              ⊗
              (kx'⊗xi' ⊕ (ky'⊗yi' ⊕ kz'⊗zi')))))))
        BishopP.≃-refl
        kx ky kz xr xi yr yi zr zi inverse

    reduceCoefficient :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._-_
            (BishopReal._*_
              (BishopReal._*_ inverse inverse)
              q)
            inverse)
          inverse)
        (BishopReal.-_ inverse)
    reduceCoefficient =
      BishopP.≃-trans
        (BishopP.-cong
          (BishopP.-cong inverseSquareNorm
            (BishopP.≃-refl inverse))
          (BishopP.≃-refl inverse))
        (solve 1
          (λ i → (i ⊖ i ⊖ i) ⊜ ⊝ i)
          BishopP.≃-refl
          inverse)

    reduced :
      BishopReal._≃_
        (BishopReal._+_
          valueNorm
          (BishopReal._*_
            (BishopReal._-_
              (BishopReal._-_
                (BishopReal._*_
                  (BishopReal._*_ inverse inverse)
                  q)
                inverse)
              inverse)
            dotNorm))
        (BishopReal._-_
          valueNorm
          (BishopReal._*_ inverse dotNorm))
    reduced =
      BishopP.≃-trans
        (BishopP.+-congʳ
          (BishopP.*-cong
            reduceCoefficient
            (BishopP.≃-refl dotNorm)))
        (solve 3
          (λ v i d →
            v ⊕ ((⊝ i) ⊗ d)
            ⊜ v ⊖ (i ⊗ d))
          BishopP.≃-refl
          valueNorm inverse dotNorm)
  in
  BishopP.≃-trans expanded reduced

lerayCorrectionNonnegative :
  (point : PuncturedFrequency) →
  (value : Physical.BishopComplex3) →
  BishopReal.NonNegative (lerayCorrection point value)
lerayCorrectionNonnegative point value =
  BishopP.nonNegx,y⇒nonNegx*y
    (inverseNormSquaredNonnegative point)
    (Cauchy.complexModulusSquaredNonnegative
      (Output.frequencyDot (frequency point) value))

lerayNormSquaredContraction :
  (point : PuncturedFrequency) →
  (value : Physical.BishopComplex3) →
  BishopReal._≤_
    (Cauchy.complex3NormSquared
      (lerayProject point value))
    (Cauchy.complex3NormSquared value)
lerayNormSquaredContraction point value =
  let
    correctionNN =
      BishopP.nonNegx⇒0≤x
        (lerayCorrectionNonnegative point value)
    subtractBelow =
      BishopP.+-monoʳ-≤
        (Cauchy.complex3NormSquared value)
        (BishopP.neg-mono-≤ correctionNN)
    normalized =
      BishopP.≤-respʳ-≃
        (BishopP.+-identityʳ
          (Cauchy.complex3NormSquared value))
        subtractBelow
  in
  BishopP.≤-respˡ-≃
    (lerayPythagoras point value)
    normalized

bishopEuclideanLerayPythagorasClosed : Bool
bishopEuclideanLerayPythagorasClosed = true

bishopEuclideanLerayContractionClosed : Bool
bishopEuclideanLerayContractionClosed = true

lerayNeedsPeriodicGap : Bool
lerayNeedsPeriodicGap = false

originProjectorDefinedHere : Bool
originProjectorDefinedHere = false

clayPromotion : Bool
clayPromotion = false

bishopEuclideanLerayContractionClosedIsTrue :
  bishopEuclideanLerayContractionClosed ≡ true
bishopEuclideanLerayContractionClosedIsTrue = refl

originProjectorDefinedHereIsFalse :
  originProjectorDefinedHere ≡ false
originProjectorDefinedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
