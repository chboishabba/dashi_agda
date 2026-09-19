module DASHI.Physics.Closure.NSTriadKNEuclideanRawGramOutputQuadraticExact where

------------------------------------------------------------------------
-- A / WHOLE-SPACE RAW GRAM HAS TWO OUTPUT-FREQUENCY POWERS
--
-- The continuous divergence-form convection cell is linear in the output
-- frequency xi.  R290's physical Gram observable is bilinear in TWO cells.
-- Therefore, before Leray projection and before any absolute value,
--
--   Gram_raw(s xi ; A,B) ~= s^2 Gram_raw(xi ; A,B)
--
-- when the two velocity inputs are held fixed.
--
-- This is the exact continuous analogue of the finite R291 real-Hermitian
-- Gram algebra.  It proves two low-frequency powers supplied by the raw
-- nonlinear Gram itself.  It deliberately does NOT upgrade those two powers
-- to the six powers required by a pointwise a^3 compensation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output

------------------------------------------------------------------------
-- Scalar and vector setoid helpers.
------------------------------------------------------------------------

realScaleComplex3 :
  BishopReal.ℝ →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
realScaleComplex3 scalar value =
  Physical.bishop-complex3
    (Output.realScaleComplex scalar (Physical.cx value))
    (Output.realScaleComplex scalar (Physical.cy value))
    (Output.realScaleComplex scalar (Physical.cz value))

complexRealScaleMeaning :
  (scalar : BishopReal.ℝ) →
  (value : Physical.BishopComplex) →
  Output.ComplexEquivalent
    (Output.realScaleComplex scalar value)
    (Output.complexMultiply
      (Physical.bishop-complex scalar BishopReal.0ℝ)
      value)
complexRealScaleMeaning scalar value =
  let open BishopP.ℝ-Solver
  in
  Output.complex-equivalent
    (solve 3
      (λ s r i →
        s ⊗ r
        ⊜ (s ⊗ r) ⊖ (BishopReal.0ℝ ⊗ i))
      BishopP.≃-refl
      scalar
      (Physical.realPart value)
      (Physical.imaginaryPart value))
    (solve 3
      (λ s r i →
        s ⊗ i
        ⊜ (s ⊗ i) ⊕ (BishopReal.0ℝ ⊗ r))
      BishopP.≃-refl
      scalar
      (Physical.realPart value)
      (Physical.imaginaryPart value))

complexMultiplyRealScaleLeft :
  (scalar : BishopReal.ℝ) →
  (a b : Physical.BishopComplex) →
  Output.ComplexEquivalent
    (Output.complexMultiply
      (Output.realScaleComplex scalar a)
      b)
    (Output.realScaleComplex scalar
      (Output.complexMultiply a b))
complexMultiplyRealScaleLeft scalar a b =
  let
    open BishopP.ℝ-Solver
    ar = Physical.realPart a
    ai = Physical.imaginaryPart a
    br = Physical.realPart b
    bi = Physical.imaginaryPart b
  in
  Output.complex-equivalent
    (solve 5
      (λ s ar' ai' br' bi' →
        ((s ⊗ ar') ⊗ br') ⊖ ((s ⊗ ai') ⊗ bi')
        ⊜
        s ⊗ ((ar' ⊗ br') ⊖ (ai' ⊗ bi')))
      BishopP.≃-refl scalar ar ai br bi)
    (solve 5
      (λ s ar' ai' br' bi' →
        ((s ⊗ ar') ⊗ bi') ⊕ ((s ⊗ ai') ⊗ br')
        ⊜
        s ⊗ ((ar' ⊗ bi') ⊕ (ai' ⊗ br')))
      BishopP.≃-refl scalar ar ai br bi)

rawCellScalesWithOutput :
  (scalar : BishopReal.ℝ) →
  (output : Euclidean.R3Frequency) →
  (uEta uZeta : Physical.BishopComplex3) →
  Output.Complex3Equivalent
    (Output.divergenceFormRawCell
      (Output.scaleFrequency scalar output)
      uEta uZeta)
    (realScaleComplex3 scalar
      (Output.divergenceFormRawCell output uEta uZeta))
rawCellScalesWithOutput scalar output uEta uZeta =
  let
    dotScale = Output.frequencyDotScale scalar output uEta

    iDotScale :
      Output.ComplexEquivalent
        (Output.complexMultiply
          Output.complexI
          (Output.frequencyDot
            (Output.scaleFrequency scalar output)
            uEta))
        (Output.realScaleComplex scalar
          (Output.complexMultiply
            Output.complexI
            (Output.frequencyDot output uEta)))
    iDotScale =
      let
        first =
          Output.complexMultiplyRespects
            (Output.complex-equivalent
              (BishopP.≃-refl BishopReal.0ℝ)
              (BishopP.≃-refl BishopReal.1ℝ))
            dotScale

        commuteScale :
          Output.ComplexEquivalent
            (Output.complexMultiply
              Output.complexI
              (Output.realScaleComplex scalar
                (Output.frequencyDot output uEta)))
            (Output.realScaleComplex scalar
              (Output.complexMultiply
                Output.complexI
                (Output.frequencyDot output uEta)))
        commuteScale =
          complexMultiplyRealScaleLeft
            scalar Output.complexI (Output.frequencyDot output uEta)
      in
      Output.complex-equivalent
        (BishopP.≃-trans
          (Output.realEquivalent first)
          (Output.realEquivalent commuteScale))
        (BishopP.≃-trans
          (Output.imaginaryEquivalent first)
          (Output.imaginaryEquivalent commuteScale))

    scaleComponent :
      (z : Physical.BishopComplex) →
      Output.ComplexEquivalent
        (Output.complexMultiply
          (Output.complexMultiply
            Output.complexI
            (Output.frequencyDot
              (Output.scaleFrequency scalar output)
              uEta))
          z)
        (Output.realScaleComplex scalar
          (Output.complexMultiply
            (Output.complexMultiply
              Output.complexI
              (Output.frequencyDot output uEta))
            z))
    scaleComponent z =
      let
        first =
          Output.complexMultiplyRespects
            iDotScale
            (Output.complex-equivalent
              (BishopP.≃-refl (Physical.realPart z))
              (BishopP.≃-refl (Physical.imaginaryPart z)))
        second =
          complexMultiplyRealScaleLeft
            scalar
            (Output.complexMultiply
              Output.complexI
              (Output.frequencyDot output uEta))
            z
      in
      Output.complex-equivalent
        (BishopP.≃-trans
          (Output.realEquivalent first)
          (Output.realEquivalent second))
        (BishopP.≃-trans
          (Output.imaginaryEquivalent first)
          (Output.imaginaryEquivalent second))
  in
  Output.complex3-equivalent
    (scaleComponent (Physical.cx uZeta))
    (scaleComponent (Physical.cy uZeta))
    (scaleComponent (Physical.cz uZeta))

------------------------------------------------------------------------
-- Bishop-real Hermitian Gram scalar, matching R291's 2 Re <A,B>.
------------------------------------------------------------------------

complexRealHermitian :
  Physical.BishopComplex →
  Physical.BishopComplex →
  BishopReal.ℝ
complexRealHermitian a b =
  BishopReal._+_
    (BishopReal._*_
      (Physical.realPart a)
      (Physical.realPart b))
    (BishopReal._*_
      (Physical.imaginaryPart a)
      (Physical.imaginaryPart b))

realHermitianCross :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
realHermitianCross a b =
  BishopReal._+_
    (complexRealHermitian (Physical.cx a) (Physical.cx b))
    (BishopReal._+_
      (complexRealHermitian (Physical.cy a) (Physical.cy b))
      (complexRealHermitian (Physical.cz a) (Physical.cz b)))

two : BishopReal.ℝ
two = BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ

rawGram :
  Euclidean.R3Frequency →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
rawGram output aEta aZeta bEta bZeta =
  BishopReal._*_
    two
    (realHermitianCross
      (Output.divergenceFormRawCell output aEta aZeta)
      (Output.divergenceFormRawCell output bEta bZeta))

realHermitianScaleBoth :
  (scalar : BishopReal.ℝ) →
  (a b : Physical.BishopComplex3) →
  BishopReal._≃_
    (realHermitianCross
      (realScaleComplex3 scalar a)
      (realScaleComplex3 scalar b))
    (BishopReal._*_
      (BishopReal._*_ scalar scalar)
      (realHermitianCross a b))
realHermitianScaleBoth scalar
    (Physical.bishop-complex3
      (Physical.bishop-complex axr axi)
      (Physical.bishop-complex ayr ayi)
      (Physical.bishop-complex azr azi))
    (Physical.bishop-complex3
      (Physical.bishop-complex bxr bxi)
      (Physical.bishop-complex byr byi)
      (Physical.bishop-complex bzr bzi)) =
  let open BishopP.ℝ-Solver
  in
  solve 13
    (λ s axr' axi' ayr' ayi' azr' azi'
       bxr' bxi' byr' byi' bzr' bzi' →
      ((s ⊗ axr') ⊗ (s ⊗ bxr') ⊕
       (s ⊗ axi') ⊗ (s ⊗ bxi'))
      ⊕
      (((s ⊗ ayr') ⊗ (s ⊗ byr') ⊕
        (s ⊗ ayi') ⊗ (s ⊗ byi'))
       ⊕
       ((s ⊗ azr') ⊗ (s ⊗ bzr') ⊕
        (s ⊗ azi') ⊗ (s ⊗ bzi')))
      ⊜
      (s ⊗ s) ⊗
      ((axr' ⊗ bxr' ⊕ axi' ⊗ bxi')
       ⊕
       ((ayr' ⊗ byr' ⊕ ayi' ⊗ byi')
        ⊕
        (azr' ⊗ bzr' ⊕ azi' ⊗ bzi'))))
    BishopP.≃-refl
    scalar axr axi ayr ayi azr azi bxr bxi byr byi bzr bzi

rawGramScalesQuadratically :
  (scalar : BishopReal.ℝ) →
  (output : Euclidean.R3Frequency) →
  (aEta aZeta bEta bZeta : Physical.BishopComplex3) →
  BishopReal._≃_
    (rawGram
      (Output.scaleFrequency scalar output)
      aEta aZeta bEta bZeta)
    (BishopReal._*_
      (BishopReal._*_ scalar scalar)
      (rawGram output aEta aZeta bEta bZeta))
rawGramScalesQuadratically
    scalar output aEta aZeta bEta bZeta =
  let
    A =
      Output.divergenceFormRawCell output aEta aZeta
    B =
      Output.divergenceFormRawCell output bEta bZeta
    AS =
      Output.divergenceFormRawCell
        (Output.scaleFrequency scalar output) aEta aZeta
    BS =
      Output.divergenceFormRawCell
        (Output.scaleFrequency scalar output) bEta bZeta

    aScale = rawCellScalesWithOutput scalar output aEta aZeta
    bScale = rawCellScalesWithOutput scalar output bEta bZeta

    crossCongruence :
      BishopReal._≃_
        (realHermitianCross AS BS)
        (realHermitianCross
          (realScaleComplex3 scalar A)
          (realScaleComplex3 scalar B))
    crossCongruence =
      let
        componentCongruence :
          ∀ {a a' b b'} →
          Output.ComplexEquivalent a a' →
          Output.ComplexEquivalent b b' →
          BishopReal._≃_
            (complexRealHermitian a b)
            (complexRealHermitian a' b')
        componentCongruence {a} {a'} {b} {b'} ae be =
          BishopP.+-cong
            (BishopP.*-cong
              (Output.realEquivalent ae)
              (Output.realEquivalent be))
            (BishopP.*-cong
              (Output.imaginaryEquivalent ae)
              (Output.imaginaryEquivalent be))
      in
      BishopP.+-cong
        (componentCongruence
          (Output.xEquivalent aScale)
          (Output.xEquivalent bScale))
        (BishopP.+-cong
          (componentCongruence
            (Output.yEquivalent aScale)
            (Output.yEquivalent bScale))
          (componentCongruence
            (Output.zEquivalent aScale)
            (Output.zEquivalent bScale)))

    crossScale =
      realHermitianScaleBoth scalar A B

    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (BishopP.≃-trans crossCongruence crossScale))
    (solve 3
      (λ t s g →
        t ⊗ ((s ⊗ s) ⊗ g)
        ⊜
        (s ⊗ s) ⊗ (t ⊗ g))
      BishopP.≃-refl
      two scalar (realHermitianCross A B))

rawGramAtZeroOutputVanishes :
  (aEta aZeta bEta bZeta : Physical.BishopComplex3) →
  BishopReal._≃_
    (rawGram Output.zeroFrequency aEta aZeta bEta bZeta)
    BishopReal.0ℝ
rawGramAtZeroOutputVanishes aEta aZeta bEta bZeta =
  let
    A0 = Output.rawCellAtZeroOutputVanishes aEta aZeta
    B0 = Output.rawCellAtZeroOutputVanishes bEta bZeta

    zeroVector =
      Physical.bishop-complex3
        Output.complexZero Output.complexZero Output.complexZero

    crossToZero :
      BishopReal._≃_
        (realHermitianCross
          (Output.divergenceFormRawCell
            Output.zeroFrequency aEta aZeta)
          (Output.divergenceFormRawCell
            Output.zeroFrequency bEta bZeta))
        (realHermitianCross zeroVector zeroVector)
    crossToZero =
      let
        comp :
          ∀ {a a' b b'} →
          Output.ComplexEquivalent a a' →
          Output.ComplexEquivalent b b' →
          BishopReal._≃_
            (complexRealHermitian a b)
            (complexRealHermitian a' b')
        comp ae be =
          BishopP.+-cong
            (BishopP.*-cong
              (Output.realEquivalent ae)
              (Output.realEquivalent be))
            (BishopP.*-cong
              (Output.imaginaryEquivalent ae)
              (Output.imaginaryEquivalent be))
      in
      BishopP.+-cong
        (comp (Output.xEquivalent A0) (Output.xEquivalent B0))
        (BishopP.+-cong
          (comp (Output.yEquivalent A0) (Output.yEquivalent B0))
          (comp (Output.zEquivalent A0) (Output.zEquivalent B0)))

    open BishopP.ℝ-Solver
    zeroCross :
      BishopReal._≃_
        (realHermitianCross zeroVector zeroVector)
        BishopReal.0ℝ
    zeroCross =
      solve 0
        (((BishopReal.0ℝ ⊗ BishopReal.0ℝ)
          ⊕ (BishopReal.0ℝ ⊗ BishopReal.0ℝ))
         ⊕
         (((BishopReal.0ℝ ⊗ BishopReal.0ℝ)
          ⊕ (BishopReal.0ℝ ⊗ BishopReal.0ℝ))
          ⊕
          ((BishopReal.0ℝ ⊗ BishopReal.0ℝ)
           ⊕ (BishopReal.0ℝ ⊗ BishopReal.0ℝ)))
         ⊜ BishopReal.0ℝ)
        BishopP.≃-refl
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (BishopP.≃-trans crossToZero zeroCross))
    (BishopP.*-zeroʳ two)

------------------------------------------------------------------------
-- Honest low-frequency accounting.
------------------------------------------------------------------------

rawNonlinearCellOutputOrder : Bool
rawNonlinearCellOutputOrder = true

rawGramOutputQuadraticClosed : Bool
rawGramOutputQuadraticClosed = true

rawGramVanishesAtOrigin : Bool
rawGramVanishesAtOrigin = true

rawGramSuppliesAllSixHeatCubePowers : Bool
rawGramSuppliesAllSixHeatCubePowers = false

remainingPointwiseFrequencyPowersRelativeToXiSix : BishopReal.ℝ
remainingPointwiseFrequencyPowersRelativeToXiSix =
  BishopReal._+_
    (BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ)
    (BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ)

lerayProjectedGramQuadraticClosedHere : Bool
lerayProjectedGramQuadraticClosedHere = false

clayPromotion : Bool
clayPromotion = false

rawGramOutputQuadraticClosedIsTrue :
  rawGramOutputQuadraticClosed ≡ true
rawGramOutputQuadraticClosedIsTrue = refl

rawGramSuppliesAllSixHeatCubePowersIsFalse :
  rawGramSuppliesAllSixHeatCubePowers ≡ false
rawGramSuppliesAllSixHeatCubePowersIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
