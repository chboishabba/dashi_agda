module DASHI.Physics.Closure.NSTriadKNEuclideanBishopCauchyGramExact where

------------------------------------------------------------------------
-- A / CONCRETE BISHOP-REAL CAUCHY + GRAM YOUNG
--
-- No abstract Hilbert-space authority is needed for the literal C^3 Fourier
-- carrier.  We prove the polynomial Lagrange identity coordinatewise:
--
--   |xi|^2 |u|^2 - |xi dot u|^2
--     = sum_{i<j} |xi_i u_j - xi_j u_i|^2 >= 0.
--
-- For complex u this is applied to real and imaginary parts.  Consequently
--
--   |xi dot u|^2 <= |xi|^2 |u|^2.
--
-- We also prove the exact real-Hermitian Young bound
--
--   2 Re <A,B> <= |A|^2 + |B|^2
--
-- from |A-B|^2 >= 0.  These are the two polynomial estimates needed to turn
-- the divergence-form output factor into a quadratic Gram majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramOutputQuadraticExact as Gram
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

squareNonnegative :
  (x : BishopReal.ℝ) →
  BishopReal.NonNegative (square x)
squareNonnegative x =
  BishopP.nonNegx,y⇒nonNegx*y
    (BishopP.nonNeg∣x∣ x)
    (BishopP.nonNeg∣x∣ x)
  where
  -- x^2 is represented directly below; this local proof is replaced by the
  -- standard constructive square theorem through order transport.
  -- The absolute-value presentation keeps no sign assumption on x.

-- A direct, sign-free square nonnegativity owner using x*x.
directSquareNonnegative :
  (x : BishopReal.ℝ) →
  BishopReal.NonNegative (BishopReal._*_ x x)
directSquareNonnegative x =
  BishopP.0≤x⇒nonNegx
    (BishopP.squareNonnegative x)

complexModulusSquared :
  Physical.BishopComplex → BishopReal.ℝ
complexModulusSquared z =
  BishopReal._+_
    (square (Physical.realPart z))
    (square (Physical.imaginaryPart z))

complex3NormSquared :
  Physical.BishopComplex3 → BishopReal.ℝ
complex3NormSquared v =
  BishopReal._+_
    (complexModulusSquared (Physical.cx v))
    (BishopReal._+_
      (complexModulusSquared (Physical.cy v))
      (complexModulusSquared (Physical.cz v)))

complexModulusSquaredNonnegative :
  (z : Physical.BishopComplex) →
  BishopReal.NonNegative (complexModulusSquared z)
complexModulusSquaredNonnegative z =
  BishopP.+-nonNeg
    (directSquareNonnegative (Physical.realPart z))
    (directSquareNonnegative (Physical.imaginaryPart z))

complex3NormSquaredNonnegative :
  (v : Physical.BishopComplex3) →
  BishopReal.NonNegative (complex3NormSquared v)
complex3NormSquaredNonnegative v =
  BishopP.+-nonNeg
    (complexModulusSquaredNonnegative (Physical.cx v))
    (BishopP.+-nonNeg
      (complexModulusSquaredNonnegative (Physical.cy v))
      (complexModulusSquaredNonnegative (Physical.cz v)))

realDot3 :
  Euclidean.R3Frequency →
  BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ →
  BishopReal.ℝ
realDot3 xi ux uy uz =
  BishopReal._+_
    (BishopReal._*_ (Euclidean.x xi) ux)
    (BishopReal._+_
      (BishopReal._*_ (Euclidean.y xi) uy)
      (BishopReal._*_ (Euclidean.z xi) uz))

lagrangeRemainder :
  Euclidean.R3Frequency →
  BishopReal.ℝ → BishopReal.ℝ → BishopReal.ℝ →
  BishopReal.ℝ
lagrangeRemainder xi ux uy uz =
  BishopReal._+_
    (square
      (BishopReal._-_
        (BishopReal._*_ (Euclidean.x xi) uy)
        (BishopReal._*_ (Euclidean.y xi) ux)))
    (BishopReal._+_
      (square
        (BishopReal._-_
          (BishopReal._*_ (Euclidean.x xi) uz)
          (BishopReal._*_ (Euclidean.z xi) ux)))
      (square
        (BishopReal._-_
          (BishopReal._*_ (Euclidean.y xi) uz)
          (BishopReal._*_ (Euclidean.z xi) uy))))

lagrangeIdentity :
  (xi : Euclidean.R3Frequency) →
  (ux uy uz : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._*_
        (Heat.frequencyNormSquared xi)
        (BishopReal._+_
          (square ux)
          (BishopReal._+_ (square uy) (square uz))))
      (square (realDot3 xi ux uy uz)))
    (lagrangeRemainder xi ux uy uz)
lagrangeIdentity xi ux uy uz =
  let
    x = Euclidean.x xi
    y = Euclidean.y xi
    z = Euclidean.z xi
    open BishopP.ℝ-Solver
  in
  solve 6
    (λ x' y' z' a b c →
      (((x' ⊗ x') ⊕ ((y' ⊗ y') ⊕ (z' ⊗ z')))
       ⊗
       ((a ⊗ a) ⊕ ((b ⊗ b) ⊕ (c ⊗ c))))
      ⊖
      ((x' ⊗ a ⊕ (y' ⊗ b ⊕ z' ⊗ c))
       ⊗
       (x' ⊗ a ⊕ (y' ⊗ b ⊕ z' ⊗ c)))
      ⊜
      (((x' ⊗ b ⊖ y' ⊗ a) ⊗ (x' ⊗ b ⊖ y' ⊗ a))
       ⊕
       (((x' ⊗ c ⊖ z' ⊗ a) ⊗ (x' ⊗ c ⊖ z' ⊗ a))
        ⊕
        ((y' ⊗ c ⊖ z' ⊗ b) ⊗ (y' ⊗ c ⊖ z' ⊗ b)))))
    BishopP.≃-refl
    x y z ux uy uz

lagrangeRemainderNonnegative :
  (xi : Euclidean.R3Frequency) →
  (ux uy uz : BishopReal.ℝ) →
  BishopReal.NonNegative (lagrangeRemainder xi ux uy uz)
lagrangeRemainderNonnegative xi ux uy uz =
  BishopP.+-nonNeg
    (directSquareNonnegative
      (BishopReal._-_
        (BishopReal._*_ (Euclidean.x xi) uy)
        (BishopReal._*_ (Euclidean.y xi) ux)))
    (BishopP.+-nonNeg
      (directSquareNonnegative
        (BishopReal._-_
          (BishopReal._*_ (Euclidean.x xi) uz)
          (BishopReal._*_ (Euclidean.z xi) ux)))
      (directSquareNonnegative
        (BishopReal._-_
          (BishopReal._*_ (Euclidean.y xi) uz)
          (BishopReal._*_ (Euclidean.z xi) uy))))

realDotSquareBelow :
  (xi : Euclidean.R3Frequency) →
  (ux uy uz : BishopReal.ℝ) →
  BishopReal._≤_
    (square (realDot3 xi ux uy uz))
    (BishopReal._*_
      (Heat.frequencyNormSquared xi)
      (BishopReal._+_
        (square ux)
        (BishopReal._+_ (square uy) (square uz))))
realDotSquareBelow xi ux uy uz =
  let
    lhs = square (realDot3 xi ux uy uz)
    rhs =
      BishopReal._*_
        (Heat.frequencyNormSquared xi)
        (BishopReal._+_
          (square ux)
          (BishopReal._+_ (square uy) (square uz)))
    remainder = lagrangeRemainder xi ux uy uz

    diffNN =
      BishopP.nonNegx⇒0≤x
        (lagrangeRemainderNonnegative xi ux uy uz)

    zeroBelowDifference :
      BishopReal._≤_ BishopReal.0ℝ
        (BishopReal._-_ rhs lhs)
    zeroBelowDifference =
      BishopP.≤-respʳ-≃
        (BishopP.≃-symm (lagrangeIdentity xi ux uy uz))
        diffNN
  in
  BishopP.0≤y-x⇒x≤y zeroBelowDifference

frequencyDotModulusSquared :
  (xi : Euclidean.R3Frequency) →
  (u : Physical.BishopComplex3) →
  BishopReal._≃_
    (complexModulusSquared (Output.frequencyDot xi u))
    (BishopReal._+_
      (square
        (realDot3 xi
          (Physical.realPart (Physical.cx u))
          (Physical.realPart (Physical.cy u))
          (Physical.realPart (Physical.cz u))))
      (square
        (realDot3 xi
          (Physical.imaginaryPart (Physical.cx u))
          (Physical.imaginaryPart (Physical.cy u))
          (Physical.imaginaryPart (Physical.cz u)))))
frequencyDotModulusSquared xi u = BishopP.≃-refl _

frequencyDotCauchySquared :
  (xi : Euclidean.R3Frequency) →
  (u : Physical.BishopComplex3) →
  BishopReal._≤_
    (complexModulusSquared (Output.frequencyDot xi u))
    (BishopReal._*_
      (Heat.frequencyNormSquared xi)
      (complex3NormSquared u))
frequencyDotCauchySquared xi u =
  let
    realBound =
      realDotSquareBelow xi
        (Physical.realPart (Physical.cx u))
        (Physical.realPart (Physical.cy u))
        (Physical.realPart (Physical.cz u))
    imagBound =
      realDotSquareBelow xi
        (Physical.imaginaryPart (Physical.cx u))
        (Physical.imaginaryPart (Physical.cy u))
        (Physical.imaginaryPart (Physical.cz u))

    summed = BishopP.+-mono-≤ realBound imagBound

    open BishopP.ℝ-Solver
    regroup :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (Heat.frequencyNormSquared xi)
            (BishopReal._+_
              (square (Physical.realPart (Physical.cx u)))
              (BishopReal._+_
                (square (Physical.realPart (Physical.cy u)))
                (square (Physical.realPart (Physical.cz u))))))
          (BishopReal._*_
            (Heat.frequencyNormSquared xi)
            (BishopReal._+_
              (square (Physical.imaginaryPart (Physical.cx u)))
              (BishopReal._+_
                (square (Physical.imaginaryPart (Physical.cy u)))
                (square (Physical.imaginaryPart (Physical.cz u)))))))
        (BishopReal._*_
          (Heat.frequencyNormSquared xi)
          (complex3NormSquared u))
    regroup =
      solve 7
        (λ q xr xi' yr yi zr zi →
          (q ⊗ ((xr ⊗ xr) ⊕ ((yr ⊗ yr) ⊕ (zr ⊗ zr))))
          ⊕
          (q ⊗ ((xi' ⊗ xi') ⊕ ((yi ⊗ yi) ⊕ (zi ⊗ zi))))
          ⊜
          q ⊗
          (((xr ⊗ xr) ⊕ (xi' ⊗ xi'))
           ⊕
           (((yr ⊗ yr) ⊕ (yi ⊗ yi))
            ⊕
            ((zr ⊗ zr) ⊕ (zi ⊗ zi)))))
        BishopP.≃-refl
        (Heat.frequencyNormSquared xi)
        (Physical.realPart (Physical.cx u))
        (Physical.imaginaryPart (Physical.cx u))
        (Physical.realPart (Physical.cy u))
        (Physical.imaginaryPart (Physical.cy u))
        (Physical.realPart (Physical.cz u))
        (Physical.imaginaryPart (Physical.cz u))
  in
  BishopP.≤-respʳ-≃ regroup summed

realHermitianYoung :
  (a b : Physical.BishopComplex3) →
  BishopReal._≤_
    (BishopReal._*_ Gram.two (Gram.realHermitianCross a b))
    (BishopReal._+_
      (complex3NormSquared a)
      (complex3NormSquared b))
realHermitianYoung
    (Physical.bishop-complex3
      (Physical.bishop-complex axr axi)
      (Physical.bishop-complex ayr ayi)
      (Physical.bishop-complex azr azi))
    (Physical.bishop-complex3
      (Physical.bishop-complex bxr bxi)
      (Physical.bishop-complex byr byi)
      (Physical.bishop-complex bzr bzi)) =
  let
    remainder =
      BishopReal._+_
        (square (BishopReal._-_ axr bxr))
        (BishopReal._+_
          (square (BishopReal._-_ axi bxi))
          (BishopReal._+_
            (square (BishopReal._-_ ayr byr))
            (BishopReal._+_
              (square (BishopReal._-_ ayi byi))
              (BishopReal._+_
                (square (BishopReal._-_ azr bzr))
                (square (BishopReal._-_ azi bzi))))))

    remainderNN : BishopReal.NonNegative remainder
    remainderNN =
      BishopP.+-nonNeg (directSquareNonnegative (BishopReal._-_ axr bxr))
      (BishopP.+-nonNeg (directSquareNonnegative (BishopReal._-_ axi bxi))
      (BishopP.+-nonNeg (directSquareNonnegative (BishopReal._-_ ayr byr))
      (BishopP.+-nonNeg (directSquareNonnegative (BishopReal._-_ ayi byi))
      (BishopP.+-nonNeg (directSquareNonnegative (BishopReal._-_ azr bzr))
                        (directSquareNonnegative (BishopReal._-_ azi bzi))))))

    open BishopP.ℝ-Solver
    differenceIdentity :
      BishopReal._≃_
        (BishopReal._-_
          (BishopReal._+_
            (complex3NormSquared
              (Physical.bishop-complex3
                (Physical.bishop-complex axr axi)
                (Physical.bishop-complex ayr ayi)
                (Physical.bishop-complex azr azi)))
            (complex3NormSquared
              (Physical.bishop-complex3
                (Physical.bishop-complex bxr bxi)
                (Physical.bishop-complex byr byi)
                (Physical.bishop-complex bzr bzi))))
          (BishopReal._*_
            Gram.two
            (Gram.realHermitianCross
              (Physical.bishop-complex3
                (Physical.bishop-complex axr axi)
                (Physical.bishop-complex ayr ayi)
                (Physical.bishop-complex azr azi))
              (Physical.bishop-complex3
                (Physical.bishop-complex bxr bxi)
                (Physical.bishop-complex byr byi)
                (Physical.bishop-complex bzr bzi)))))
        remainder
    differenceIdentity =
      solve 12
        (λ ar ai br bi cr ci dr di er ei fr fi →
          (((ar⊗ar ⊕ ai⊗ai)
            ⊕ ((br⊗br ⊕ bi⊗bi) ⊕ (cr⊗cr ⊕ ci⊗ci)))
           ⊕
           ((dr⊗dr ⊕ di⊗di)
            ⊕ ((er⊗er ⊕ ei⊗ei) ⊕ (fr⊗fr ⊕ fi⊗fi))))
          ⊖
          ((BishopReal.1ℝ ⊕ BishopReal.1ℝ)
           ⊗
           ((ar⊗dr ⊕ ai⊗di)
            ⊕ ((br⊗er ⊕ bi⊗ei) ⊕ (cr⊗fr ⊕ ci⊗fi))))
          ⊜
          ((ar⊖dr)⊗(ar⊖dr)
           ⊕
           ((ai⊖di)⊗(ai⊖di)
            ⊕
            ((br⊖er)⊗(br⊖er)
             ⊕
             ((bi⊖ei)⊗(bi⊖ei)
              ⊕
              ((cr⊖fr)⊗(cr⊖fr)
               ⊕ (ci⊖fi)⊗(ci⊖fi)))))))
        BishopP.≃-refl
        axr axi ayr ayi azr azi bxr bxi byr byi bzr bzi

    zeroBelowDiff =
      BishopP.≤-respʳ-≃
        (BishopP.≃-symm differenceIdentity)
        (BishopP.nonNegx⇒0≤x remainderNN)
  in
  BishopP.0≤y-x⇒x≤y zeroBelowDiff

bishopComplex3CauchySquaredClosed : Bool
bishopComplex3CauchySquaredClosed = true

bishopRealHermitianYoungClosed : Bool
bishopRealHermitianYoungClosed = true

squareRootsUsed : Bool
squareRootsUsed = false

clayPromotion : Bool
clayPromotion = false

bishopComplex3CauchySquaredClosedIsTrue :
  bishopComplex3CauchySquaredClosed ≡ true
bishopComplex3CauchySquaredClosedIsTrue = refl

squareRootsUsedIsFalse : squareRootsUsed ≡ false
squareRootsUsedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
