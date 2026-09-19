module DASHI.Physics.Closure.NSTriadKNEuclideanRawGramQuadraticMajorantExact where

------------------------------------------------------------------------
-- A / RAW DIVERGENCE-FORM GRAM <= |xi|^2 * STATE MAJORANT
--
-- This composes the concrete Bishop-real Cauchy/Young algebra:
--
--   |xi dot u|^2 <= |xi|^2 |u|^2,
--   |i (xi dot u) v|^2 = |xi dot u|^2 |v|^2,
--   2 Re <A,B> <= |A|^2 + |B|^2.
--
-- Hence the literal raw R290-style Gram formed from two continuous convection
-- cells satisfies
--
--   Gram_raw(xi)
--     <= |xi|^2
--        ( |u_a(eta)|^2 |u_a(zeta)|^2
--        + |u_b(eta)|^2 |u_b(zeta)|^2 ).
--
-- This is exactly the quadratic output-frequency estimate required by the
-- low-frequency saturation consumer.  It uses no square roots and no absolute
-- value before the signed Gram estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanRawGramOutputQuadraticExact as Gram
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopCauchyGramExact as Cauchy
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat

complexMultiplyModulusSquared :
  (a b : Physical.BishopComplex) →
  BishopReal._≃_
    (Cauchy.complexModulusSquared
      (Output.complexMultiply a b))
    (BishopReal._*_
      (Cauchy.complexModulusSquared a)
      (Cauchy.complexModulusSquared b))
complexMultiplyModulusSquared
    (Physical.bishop-complex ar ai)
    (Physical.bishop-complex br bi) =
  let open BishopP.ℝ-Solver
  in
  solve 4
    (λ ar' ai' br' bi' →
      (((ar' ⊗ br') ⊖ (ai' ⊗ bi'))
       ⊗
       ((ar' ⊗ br') ⊖ (ai' ⊗ bi')))
      ⊕
      (((ar' ⊗ bi') ⊕ (ai' ⊗ br'))
       ⊗
       ((ar' ⊗ bi') ⊕ (ai' ⊗ br')))
      ⊜
      ((ar' ⊗ ar') ⊕ (ai' ⊗ ai'))
      ⊗
      ((br' ⊗ br') ⊕ (bi' ⊗ bi')))
    BishopP.≃-refl
    ar ai br bi

complexIModulusSquaredIsOne :
  BishopReal._≃_
    (Cauchy.complexModulusSquared Output.complexI)
    BishopReal.1ℝ
complexIModulusSquaredIsOne =
  let open BishopP.ℝ-Solver
  in
  solve 0
    (((Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1))
      ⊕ (Κ (+ 1 / 1) ⊗ Κ (+ 1 / 1)))
      ⊜ Κ (+ 1 / 1))
    BishopP.≃-refl

iTimesDotModulusSquared :
  (xi : Euclidean.R3Frequency) →
  (u : Physical.BishopComplex3) →
  BishopReal._≃_
    (Cauchy.complexModulusSquared
      (Output.complexMultiply
        Output.complexI
        (Output.frequencyDot xi u)))
    (Cauchy.complexModulusSquared
      (Output.frequencyDot xi u))
iTimesDotModulusSquared xi u =
  BishopP.≃-trans
    (complexMultiplyModulusSquared
      Output.complexI
      (Output.frequencyDot xi u))
    (BishopP.≃-trans
      (BishopP.*-congʳ complexIModulusSquaredIsOne)
      (BishopP.*-identityˡ
        (Cauchy.complexModulusSquared
          (Output.frequencyDot xi u))))

complexScale3NormSquared :
  (scalar : Physical.BishopComplex) →
  (v : Physical.BishopComplex3) →
  BishopReal._≃_
    (Cauchy.complex3NormSquared
      (Output.complexScale3 scalar v))
    (BishopReal._*_
      (Cauchy.complexModulusSquared scalar)
      (Cauchy.complex3NormSquared v))
complexScale3NormSquared scalar
    (Physical.bishop-complex3 vx vy vz) =
  let
    xExact = complexMultiplyModulusSquared scalar vx
    yExact = complexMultiplyModulusSquared scalar vy
    zExact = complexMultiplyModulusSquared scalar vz
    s = Cauchy.complexModulusSquared scalar
    nx = Cauchy.complexModulusSquared vx
    ny = Cauchy.complexModulusSquared vy
    nz = Cauchy.complexModulusSquared vz
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      xExact
      (BishopP.+-cong yExact zExact))
    (solve 4
      (λ s' x y z →
        (s' ⊗ x) ⊕ ((s' ⊗ y) ⊕ (s' ⊗ z))
        ⊜ s' ⊗ (x ⊕ (y ⊕ z)))
      BishopP.≃-refl
      s nx ny nz)

rawCellNormSquaredExact :
  (xi : Euclidean.R3Frequency) →
  (uEta uZeta : Physical.BishopComplex3) →
  BishopReal._≃_
    (Cauchy.complex3NormSquared
      (Output.divergenceFormRawCell xi uEta uZeta))
    (BishopReal._*_
      (Cauchy.complexModulusSquared
        (Output.frequencyDot xi uEta))
      (Cauchy.complex3NormSquared uZeta))
rawCellNormSquaredExact xi uEta uZeta =
  BishopP.≃-trans
    (complexScale3NormSquared
      (Output.complexMultiply
        Output.complexI
        (Output.frequencyDot xi uEta))
      uZeta)
    (BishopP.*-congʳ
      (iTimesDotModulusSquared xi uEta))

statePairMass :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
statePairMass u v =
  BishopReal._*_
    (Cauchy.complex3NormSquared u)
    (Cauchy.complex3NormSquared v)

statePairMassNonnegative :
  (u v : Physical.BishopComplex3) →
  BishopReal.NonNegative (statePairMass u v)
statePairMassNonnegative u v =
  BishopP.nonNegx,y⇒nonNegx*y
    (Cauchy.complex3NormSquaredNonnegative u)
    (Cauchy.complex3NormSquaredNonnegative v)

rawCellQuadraticBound :
  (xi : Euclidean.R3Frequency) →
  (uEta uZeta : Physical.BishopComplex3) →
  BishopReal._≤_
    (Cauchy.complex3NormSquared
      (Output.divergenceFormRawCell xi uEta uZeta))
    (BishopReal._*_
      (Heat.frequencyNormSquared xi)
      (statePairMass uEta uZeta))
rawCellQuadraticBound xi uEta uZeta =
  let
    dotBound = Cauchy.frequencyDotCauchySquared xi uEta
    zetaNN = Cauchy.complex3NormSquaredNonnegative uZeta

    scaled :
      BishopReal._≤_
        (BishopReal._*_
          (Cauchy.complexModulusSquared
            (Output.frequencyDot xi uEta))
          (Cauchy.complex3NormSquared uZeta))
        (BishopReal._*_
          (BishopReal._*_
            (Heat.frequencyNormSquared xi)
            (Cauchy.complex3NormSquared uEta))
          (Cauchy.complex3NormSquared uZeta))
    scaled =
      BishopP.*-monoʳ-≤-nonNeg dotBound zetaNN

    open BishopP.ℝ-Solver
    regroup :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_
            (Heat.frequencyNormSquared xi)
            (Cauchy.complex3NormSquared uEta))
          (Cauchy.complex3NormSquared uZeta))
        (BishopReal._*_
          (Heat.frequencyNormSquared xi)
          (statePairMass uEta uZeta))
    regroup =
      solve 3
        (λ q a b →
          (q ⊗ a) ⊗ b
          ⊜ q ⊗ (a ⊗ b))
        BishopP.≃-refl
        (Heat.frequencyNormSquared xi)
        (Cauchy.complex3NormSquared uEta)
        (Cauchy.complex3NormSquared uZeta)
  in
  BishopP.≤-respˡ-≃
    (rawCellNormSquaredExact xi uEta uZeta)
    (BishopP.≤-respʳ-≃ regroup scaled)

rawGramStateMajorant :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
rawGramStateMajorant aEta aZeta bEta bZeta =
  BishopReal._+_
    (statePairMass aEta aZeta)
    (statePairMass bEta bZeta)

rawGramStateMajorantNonnegative :
  (aEta aZeta bEta bZeta : Physical.BishopComplex3) →
  BishopReal.NonNegative
    (rawGramStateMajorant aEta aZeta bEta bZeta)
rawGramStateMajorantNonnegative aEta aZeta bEta bZeta =
  BishopP.nonNegx,y⇒nonNegx+y
    (statePairMassNonnegative aEta aZeta)
    (statePairMassNonnegative bEta bZeta)

rawGramQuadraticMajorant :
  (xi : Euclidean.R3Frequency) →
  (aEta aZeta bEta bZeta : Physical.BishopComplex3) →
  BishopReal._≤_
    (Gram.rawGram xi aEta aZeta bEta bZeta)
    (BishopReal._*_
      (Heat.frequencyNormSquared xi)
      (rawGramStateMajorant aEta aZeta bEta bZeta))
rawGramQuadraticMajorant
    xi aEta aZeta bEta bZeta =
  let
    A = Output.divergenceFormRawCell xi aEta aZeta
    B = Output.divergenceFormRawCell xi bEta bZeta

    young :
      BishopReal._≤_
        (Gram.rawGram xi aEta aZeta bEta bZeta)
        (BishopReal._+_
          (Cauchy.complex3NormSquared A)
          (Cauchy.complex3NormSquared B))
    young = Cauchy.realHermitianYoung A B

    aBound = rawCellQuadraticBound xi aEta aZeta
    bBound = rawCellQuadraticBound xi bEta bZeta

    sumBound = BishopP.+-mono-≤ aBound bBound

    open BishopP.ℝ-Solver
    regroup :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (Heat.frequencyNormSquared xi)
            (statePairMass aEta aZeta))
          (BishopReal._*_
            (Heat.frequencyNormSquared xi)
            (statePairMass bEta bZeta)))
        (BishopReal._*_
          (Heat.frequencyNormSquared xi)
          (rawGramStateMajorant
            aEta aZeta bEta bZeta))
    regroup =
      solve 3
        (λ q a b →
          (q ⊗ a) ⊕ (q ⊗ b)
          ⊜ q ⊗ (a ⊕ b))
        BishopP.≃-refl
        (Heat.frequencyNormSquared xi)
        (statePairMass aEta aZeta)
        (statePairMass bEta bZeta)
  in
  BishopP.≤-trans
    young
    (BishopP.≤-respʳ-≃ regroup sumBound)

rawGramQuadraticMajorantClosed : Bool
rawGramQuadraticMajorantClosed = true

rawGramMajorantUsesAbsoluteValue : Bool
rawGramMajorantUsesAbsoluteValue = false

rawGramMajorantUsesSquareRoot : Bool
rawGramMajorantUsesSquareRoot = false

projectedGramQuadraticMajorantClosedHere : Bool
projectedGramQuadraticMajorantClosedHere = false

clayPromotion : Bool
clayPromotion = false

rawGramQuadraticMajorantClosedIsTrue :
  rawGramQuadraticMajorantClosed ≡ true
rawGramQuadraticMajorantClosedIsTrue = refl

rawGramMajorantUsesAbsoluteValueIsFalse :
  rawGramMajorantUsesAbsoluteValue ≡ false
rawGramMajorantUsesAbsoluteValueIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
