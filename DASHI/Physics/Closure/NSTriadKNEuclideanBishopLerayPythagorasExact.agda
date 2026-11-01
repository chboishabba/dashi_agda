module DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact where

------------------------------------------------------------------------
-- A / CONTINUOUS BISHOP-REAL LERAY PYTHAGORAS
--
-- Continuous-carrier port of NSTriadKNRationalComplex3LerayPythagoras.
--
-- For output frequency xi != 0 and an inverse q^{-1} of
--
--   q = |xi|^2,
--
-- define
--
--   P_xi v = v - q^{-1} xi (xi . v).
--
-- On the Bishop-complex C^3 carrier used by the Euclidean Fourier stack:
--
--   ||P_xi v||^2
--     ~= ||v||^2 - q^{-1} |xi . v|^2.
--
-- The correction is nonnegative when q^{-1} is nonnegative, so Leray is a
-- squared-norm contraction.  This is the exact continuous counterpart of the
-- mature periodic theorem; no new PDE estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopSquareNonnegativeExact as SquareNN
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

complexNormSquared :
  Physical.BishopComplex → BishopReal.ℝ
complexNormSquared z =
  BishopReal._+_
    (square (Physical.realPart z))
    (square (Physical.imaginaryPart z))

complex3NormSquared :
  Physical.BishopComplex3 → BishopReal.ℝ
complex3NormSquared v =
  BishopReal._+_
    (complexNormSquared (Physical.cx v))
    (BishopReal._+_
      (complexNormSquared (Physical.cy v))
      (complexNormSquared (Physical.cz v)))

complexModulusSquared :
  Physical.BishopComplex → BishopReal.ℝ
complexModulusSquared = complexNormSquared

record ContinuousLerayInverse
    (output : Euclidean.R3Frequency) : Set where
  constructor continuous-leray-inverse
  field
    inverseNormSquared : BishopReal.ℝ

    inverseLaw :
      BishopReal._≃_
        (BishopReal._*_
          inverseNormSquared
          (Heat.frequencyNormSquared output))
        BishopReal.1ℝ

    inverseNonnegative :
      BishopReal.NonNegative inverseNormSquared

open ContinuousLerayInverse public

realScaleComplex3 :
  BishopReal.ℝ →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
realScaleComplex3 scalar v =
  Physical.bishop-complex3
    (Output.realScaleComplex scalar (Physical.cx v))
    (Output.realScaleComplex scalar (Physical.cy v))
    (Output.realScaleComplex scalar (Physical.cz v))

frequencyAsComplex3 :
  Euclidean.R3Frequency →
  Physical.BishopComplex3
frequencyAsComplex3 output =
  Physical.bishop-complex3
    (Physical.bishop-complex
      (Euclidean.x output) BishopReal.0ℝ)
    (Physical.bishop-complex
      (Euclidean.y output) BishopReal.0ℝ)
    (Physical.bishop-complex
      (Euclidean.z output) BishopReal.0ℝ)

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

complex3Subtract :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
complex3Subtract a b =
  Physical.bishop-complex3
    (complexSubtract (Physical.cx a) (Physical.cx b))
    (complexSubtract (Physical.cy a) (Physical.cy b))
    (complexSubtract (Physical.cz a) (Physical.cz b))

lerayProject :
  (output : Euclidean.R3Frequency) →
  ContinuousLerayInverse output →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
lerayProject output inverseData value =
  let
    dotValue = Output.frequencyDot output value
    coefficient =
      Output.realScaleComplex
        (inverseNormSquared inverseData)
        dotValue
    longitudinal =
      Output.complexScale3
        coefficient
        (frequencyAsComplex3 output)
  in
  complex3Subtract value longitudinal

complex3NormSquaredNonnegative :
  (v : Physical.BishopComplex3) →
  BishopReal.NonNegative (complex3NormSquared v)
complex3NormSquaredNonnegative v =
  BishopP.nonNegx,y⇒nonNegx+y
    (BishopP.nonNegx,y⇒nonNegx+y
      (SquareNN.bishopSquareNonnegative
        (Physical.realPart (Physical.cx v)))
      (SquareNN.bishopSquareNonnegative
        (Physical.imaginaryPart (Physical.cx v))))
    (BishopP.nonNegx,y⇒nonNegx+y
      (BishopP.nonNegx,y⇒nonNegx+y
        (SquareNN.bishopSquareNonnegative
          (Physical.realPart (Physical.cy v)))
        (SquareNN.bishopSquareNonnegative
          (Physical.imaginaryPart (Physical.cy v))))
      (BishopP.nonNegx,y⇒nonNegx+y
        (SquareNN.bishopSquareNonnegative
          (Physical.realPart (Physical.cz v)))
        (SquareNN.bishopSquareNonnegative
          (Physical.imaginaryPart (Physical.cz v)))))

complexModulusSquaredNonnegative :
  (z : Physical.BishopComplex) →
  BishopReal.NonNegative (complexModulusSquared z)
complexModulusSquaredNonnegative z =
  BishopP.nonNegx,y⇒nonNegx+y
    (SquareNN.bishopSquareNonnegative (Physical.realPart z))
    (SquareNN.bishopSquareNonnegative (Physical.imaginaryPart z))

lerayCorrection :
  (output : Euclidean.R3Frequency) →
  ContinuousLerayInverse output →
  Physical.BishopComplex3 →
  BishopReal.ℝ
lerayCorrection output inverseData value =
  BishopReal._*_
    (inverseNormSquared inverseData)
    (complexModulusSquared
      (Output.frequencyDot output value))

lerayCorrectionNonnegative :
  (output : Euclidean.R3Frequency) →
  (inverseData : ContinuousLerayInverse output) →
  (value : Physical.BishopComplex3) →
  BishopReal.NonNegative
    (lerayCorrection output inverseData value)
lerayCorrectionNonnegative output inverseData value =
  BishopP.nonNegx,y⇒nonNegx*y
    (inverseNonnegative inverseData)
    (complexModulusSquaredNonnegative
      (Output.frequencyDot output value))

lerayPythagoreanIdentity :
  (output : Euclidean.R3Frequency) →
  (inverseData : ContinuousLerayInverse output) →
  (value : Physical.BishopComplex3) →
  BishopReal._≃_
    (complex3NormSquared
      (lerayProject output inverseData value))
    (BishopReal._-_
      (complex3NormSquared value)
      (lerayCorrection output inverseData value))
lerayPythagoreanIdentity
    (Euclidean.r3-frequency ox oy oz)
    inverseData
    (Physical.bishop-complex3
      (Physical.bishop-complex xr xi)
      (Physical.bishop-complex yr yi)
      (Physical.bishop-complex zr zi)) =
  let
    inv = inverseNormSquared inverseData

    inverseSquaredNorm :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ inv inv)
          (BishopReal._+_
            (square ox)
            (BishopReal._+_ (square oy) (square oz))))
        inv
    inverseSquaredNorm =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 2
          (λ i q → (i ⊗ i) ⊗ q ⊜ i ⊗ (i ⊗ q))
          BishopP.≃-refl inv
          (BishopReal._+_
            (square ox)
            (BishopReal._+_ (square oy) (square oz))))
        (BishopP.*-congˡ (inverseLaw inverseData))

    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 10
      (λ ox' oy' oz' xr' xi' yr' yi' zr' zi' i →
        let
          dr = ox' ⊗ xr' ⊕ (oy' ⊗ yr' ⊕ oz' ⊗ zr')
          di = ox' ⊗ xi' ⊕ (oy' ⊗ yi' ⊕ oz' ⊗ zi')
        in
        ((xr' ⊖ (i ⊗ dr) ⊗ ox')
          ⊗ (xr' ⊖ (i ⊗ dr) ⊗ ox')
         ⊕
         (xi' ⊖ (i ⊗ di) ⊗ ox')
          ⊗ (xi' ⊖ (i ⊗ di) ⊗ ox'))
        ⊕
        (((yr' ⊖ (i ⊗ dr) ⊗ oy')
          ⊗ (yr' ⊖ (i ⊗ dr) ⊗ oy')
         ⊕
         (yi' ⊖ (i ⊗ di) ⊗ oy')
          ⊗ (yi' ⊖ (i ⊗ di) ⊗ oy'))
         ⊕
         ((zr' ⊖ (i ⊗ dr) ⊗ oz')
          ⊗ (zr' ⊖ (i ⊗ dr) ⊗ oz')
         ⊕
         (zi' ⊖ (i ⊗ di) ⊗ oz')
          ⊗ (zi' ⊖ (i ⊗ di) ⊗ oz')))
        ⊜
        ((xr' ⊗ xr' ⊕ xi' ⊗ xi')
         ⊕
         ((yr' ⊗ yr' ⊕ yi' ⊗ yi')
          ⊕ (zr' ⊗ zr' ⊕ zi' ⊗ zi')))
        ⊕
        ((((i ⊗ i)
           ⊗
           ((ox' ⊗ ox')
            ⊕ ((oy' ⊗ oy') ⊕ (oz' ⊗ oz'))))
          ⊖ (i ⊕ i))
         ⊗
         ((dr ⊗ dr) ⊕ (di ⊗ di))))
      BishopP.≃-refl
      ox oy oz xr xi yr yi zr zi inv)
    (BishopP.≃-trans
      (BishopP.+-congˡ
        (BishopP.*-congʳ
          (BishopP.-cong
            inverseSquaredNorm
            (BishopP.≃-refl (BishopReal._+_ inv inv)))))
      (solve 3
        (λ n i d →
          n ⊕ ((i ⊖ (i ⊕ i)) ⊗ d)
          ⊜ n ⊖ (i ⊗ d))
        BishopP.≃-refl
        (complex3NormSquared
          (Physical.bishop-complex3
            (Physical.bishop-complex xr xi)
            (Physical.bishop-complex yr yi)
            (Physical.bishop-complex zr zi)))
        inv
        (complexModulusSquared
          (Output.frequencyDot
            (Euclidean.r3-frequency ox oy oz)
            (Physical.bishop-complex3
              (Physical.bishop-complex xr xi)
              (Physical.bishop-complex yr yi)
              (Physical.bishop-complex zr zi))))))

lerayNormSquaredContraction :
  (output : Euclidean.R3Frequency) →
  (inverseData : ContinuousLerayInverse output) →
  (value : Physical.BishopComplex3) →
  BishopReal._≤_
    (complex3NormSquared
      (lerayProject output inverseData value))
    (complex3NormSquared value)
lerayNormSquaredContraction output inverseData value =
  let
    correctionNN =
      lerayCorrectionNonnegative output inverseData value

    subtractionBelow :
      BishopReal._≤_
        (BishopReal._-_
          (complex3NormSquared value)
          (lerayCorrection output inverseData value))
        (complex3NormSquared value)
    subtractionBelow =
      BishopP.0≤y-x⇒x≤y
        (let open BishopP.ℝ-Solver
         in
         BishopP.≤-respʳ-≃
           (solve 2
             (λ n c → n ⊖ (n ⊖ c) ⊜ c)
             BishopP.≃-refl
             (complex3NormSquared value)
             (lerayCorrection output inverseData value))
           (BishopP.nonNegx⇒0≤x correctionNN))
  in
  BishopP.≤-respˡ-≃
    (lerayPythagoreanIdentity output inverseData value)
    subtractionBelow

continuousBishopLerayPythagorasClosed : Bool
continuousBishopLerayPythagorasClosed = true

continuousBishopLerayContractionClosed : Bool
continuousBishopLerayContractionClosed = true

portedFromPeriodicRationalLerayStructure : Bool
portedFromPeriodicRationalLerayStructure = true

physicalProjectedCellWeldClosedHere : Bool
physicalProjectedCellWeldClosedHere = false

clayPromotion : Bool
clayPromotion = false

continuousBishopLerayPythagorasClosedIsTrue :
  continuousBishopLerayPythagorasClosed ≡ true
continuousBishopLerayPythagorasClosedIsTrue = refl

continuousBishopLerayContractionClosedIsTrue :
  continuousBishopLerayContractionClosed ≡ true
continuousBishopLerayContractionClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
