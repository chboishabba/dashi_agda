module DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact where

------------------------------------------------------------------------
-- A / WHOLE-SPACE DIVERGENCE-FORM OUTPUT-FREQUENCY FACTOR
--
-- For an incompressible Fourier input at eta,
--
--   (xi-eta) dot uHat(eta) = xi dot uHat(eta),
--
-- because eta dot uHat(eta) = 0.  Thus the convection cell may be written
--
--   i (xi dot uHat(eta)) uHat(xi-eta),
--
-- before Leray projection.  The important low-frequency fact is literal:
-- the cell is linear in the OUTPUT frequency xi and vanishes at xi = 0.
--
-- This owner formalises that exact Bishop-real / complex algebra.  It does not
-- claim the full |xi|^6 compensation: it proves the first output-frequency
-- power supplied by the NS divergence structure, so later Gram/second-moment
-- owners cannot silently credit six powers to incompressibility alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical

------------------------------------------------------------------------
-- Bishop-complex algebra on the already-selected A Fourier value types.
------------------------------------------------------------------------

complexZero : Physical.BishopComplex
complexZero =
  Physical.bishop-complex BishopReal.0ℝ BishopReal.0ℝ

complexI : Physical.BishopComplex
complexI =
  Physical.bishop-complex BishopReal.0ℝ BishopReal.1ℝ

complexAdd :
  Physical.BishopComplex →
  Physical.BishopComplex →
  Physical.BishopComplex
complexAdd a b =
  Physical.bishop-complex
    (BishopReal._+_
      (Physical.realPart a) (Physical.realPart b))
    (BishopReal._+_
      (Physical.imaginaryPart a) (Physical.imaginaryPart b))

complexMultiply :
  Physical.BishopComplex →
  Physical.BishopComplex →
  Physical.BishopComplex
complexMultiply a b =
  Physical.bishop-complex
    (BishopReal._-_
      (BishopReal._*_
        (Physical.realPart a) (Physical.realPart b))
      (BishopReal._*_
        (Physical.imaginaryPart a) (Physical.imaginaryPart b)))
    (BishopReal._+_
      (BishopReal._*_
        (Physical.realPart a) (Physical.imaginaryPart b))
      (BishopReal._*_
        (Physical.imaginaryPart a) (Physical.realPart b)))

realScaleComplex :
  BishopReal.ℝ →
  Physical.BishopComplex →
  Physical.BishopComplex
realScaleComplex scalar value =
  Physical.bishop-complex
    (BishopReal._*_ scalar (Physical.realPart value))
    (BishopReal._*_ scalar (Physical.imaginaryPart value))

complexScale3 :
  Physical.BishopComplex →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
complexScale3 scalar value =
  Physical.bishop-complex3
    (complexMultiply scalar (Physical.cx value))
    (complexMultiply scalar (Physical.cy value))
    (complexMultiply scalar (Physical.cz value))

record ComplexEquivalent
    (left right : Physical.BishopComplex) : Set where
  constructor complex-equivalent
  field
    realEquivalent :
      BishopReal._≃_
        (Physical.realPart left)
        (Physical.realPart right)
    imaginaryEquivalent :
      BishopReal._≃_
        (Physical.imaginaryPart left)
        (Physical.imaginaryPart right)

open ComplexEquivalent public

record Complex3Equivalent
    (left right : Physical.BishopComplex3) : Set where
  constructor complex3-equivalent
  field
    xEquivalent :
      ComplexEquivalent (Physical.cx left) (Physical.cx right)
    yEquivalent :
      ComplexEquivalent (Physical.cy left) (Physical.cy right)
    zEquivalent :
      ComplexEquivalent (Physical.cz left) (Physical.cz right)

open Complex3Equivalent public

------------------------------------------------------------------------
-- Literal real-frequency dot complex-vector.
------------------------------------------------------------------------

frequencyDot :
  Euclidean.R3Frequency →
  Physical.BishopComplex3 →
  Physical.BishopComplex
frequencyDot frequency velocity =
  Physical.bishop-complex
    (BishopReal._+_
      (BishopReal._*_
        (Euclidean.x frequency)
        (Physical.realPart (Physical.cx velocity)))
      (BishopReal._+_
        (BishopReal._*_
          (Euclidean.y frequency)
          (Physical.realPart (Physical.cy velocity)))
        (BishopReal._*_
          (Euclidean.z frequency)
          (Physical.realPart (Physical.cz velocity)))))
    (BishopReal._+_
      (BishopReal._*_
        (Euclidean.x frequency)
        (Physical.imaginaryPart (Physical.cx velocity)))
      (BishopReal._+_
        (BishopReal._*_
          (Euclidean.y frequency)
          (Physical.imaginaryPart (Physical.cy velocity)))
        (BishopReal._*_
          (Euclidean.z frequency)
          (Physical.imaginaryPart (Physical.cz velocity)))))

scaleFrequency :
  BishopReal.ℝ →
  Euclidean.R3Frequency →
  Euclidean.R3Frequency
scaleFrequency scalar frequency =
  Euclidean.r3-frequency
    (BishopReal._*_ scalar (Euclidean.x frequency))
    (BishopReal._*_ scalar (Euclidean.y frequency))
    (BishopReal._*_ scalar (Euclidean.z frequency))

zeroFrequency : Euclidean.R3Frequency
zeroFrequency =
  Euclidean.r3-frequency
    BishopReal.0ℝ BishopReal.0ℝ BishopReal.0ℝ

frequencyDotScale :
  (scalar : BishopReal.ℝ) →
  (frequency : Euclidean.R3Frequency) →
  (velocity : Physical.BishopComplex3) →
  ComplexEquivalent
    (frequencyDot (scaleFrequency scalar frequency) velocity)
    (realScaleComplex scalar (frequencyDot frequency velocity))
frequencyDotScale scalar frequency velocity =
  let
    open BishopP.ℝ-Solver
    xr = Physical.realPart (Physical.cx velocity)
    yr = Physical.realPart (Physical.cy velocity)
    zr = Physical.realPart (Physical.cz velocity)
    xi = Physical.imaginaryPart (Physical.cx velocity)
    yi = Physical.imaginaryPart (Physical.cy velocity)
    zi = Physical.imaginaryPart (Physical.cz velocity)
    fx = Euclidean.x frequency
    fy = Euclidean.y frequency
    fz = Euclidean.z frequency
  in
  complex-equivalent
    (solve 7
      (λ s x y z a b c →
        (s ⊗ x) ⊗ a ⊕ ((s ⊗ y) ⊗ b ⊕ (s ⊗ z) ⊗ c)
        ⊜
        s ⊗ (x ⊗ a ⊕ (y ⊗ b ⊕ z ⊗ c)))
      BishopP.≃-refl scalar fx fy fz xr yr zr)
    (solve 7
      (λ s x y z a b c →
        (s ⊗ x) ⊗ a ⊕ ((s ⊗ y) ⊗ b ⊕ (s ⊗ z) ⊗ c)
        ⊜
        s ⊗ (x ⊗ a ⊕ (y ⊗ b ⊕ z ⊗ c)))
      BishopP.≃-refl scalar fx fy fz xi yi zi)

frequencyDotZero :
  (velocity : Physical.BishopComplex3) →
  ComplexEquivalent
    (frequencyDot zeroFrequency velocity)
    complexZero
frequencyDotZero velocity =
  let open BishopP.ℝ-Solver
  in
  complex-equivalent
    (solve 3
      (λ a b c →
        Κ 0ℚᵘ ⊗ a
        ⊕ (Κ 0ℚᵘ ⊗ b ⊕ Κ 0ℚᵘ ⊗ c)
        ⊜ Κ 0ℚᵘ)
      BishopP.≃-refl
      (Physical.realPart (Physical.cx velocity))
      (Physical.realPart (Physical.cy velocity))
      (Physical.realPart (Physical.cz velocity)))
    (solve 3
      (λ a b c →
        Κ 0ℚᵘ ⊗ a
        ⊕ (Κ 0ℚᵘ ⊗ b ⊕ Κ 0ℚᵘ ⊗ c)
        ⊜ Κ 0ℚᵘ)
      BishopP.≃-refl
      (Physical.imaginaryPart (Physical.cx velocity))
      (Physical.imaginaryPart (Physical.cy velocity))
      (Physical.imaginaryPart (Physical.cz velocity)))

------------------------------------------------------------------------
-- Divergence-form convection cell, before output Leray projection.
------------------------------------------------------------------------

divergenceFormRawCell :
  Euclidean.R3Frequency →
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  Physical.BishopComplex3
divergenceFormRawCell output uEta uZeta =
  complexScale3
    (complexMultiply complexI (frequencyDot output uEta))
    uZeta

complexMultiplyRespects :
  ∀ {a a' b b'} →
  ComplexEquivalent a a' →
  ComplexEquivalent b b' →
  ComplexEquivalent
    (complexMultiply a b)
    (complexMultiply a' b')
complexMultiplyRespects {a} {a'} {b} {b'}
    aEq bEq =
  let
    open BishopP.ℝ-Solver
    ar = Physical.realPart a
    ai = Physical.imaginaryPart a
    br = Physical.realPart b
    bi = Physical.imaginaryPart b
    ar' = Physical.realPart a'
    ai' = Physical.imaginaryPart a'
    br' = Physical.realPart b'
    bi' = Physical.imaginaryPart b'
  in
  complex-equivalent
    (BishopP.≃-trans
      (BishopP.-cong
        (BishopP.*-cong (realEquivalent aEq) (realEquivalent bEq))
        (BishopP.*-cong (imaginaryEquivalent aEq) (imaginaryEquivalent bEq)))
      (BishopP.≃-refl
        (BishopReal._-_
          (BishopReal._*_ ar' br')
          (BishopReal._*_ ai' bi'))))
    (BishopP.≃-trans
      (BishopP.+-cong
        (BishopP.*-cong (realEquivalent aEq) (imaginaryEquivalent bEq))
        (BishopP.*-cong (imaginaryEquivalent aEq) (realEquivalent bEq)))
      (BishopP.≃-refl
        (BishopReal._+_
          (BishopReal._*_ ar' bi')
          (BishopReal._*_ ai' br'))))

complexScale3RespectsScalar :
  ∀ {a a'} →
  ComplexEquivalent a a' →
  (v : Physical.BishopComplex3) →
  Complex3Equivalent
    (complexScale3 a v)
    (complexScale3 a' v)
complexScale3RespectsScalar scalarEq v =
  complex3-equivalent
    (complexMultiplyRespects scalarEq
      (complex-equivalent
        (BishopP.≃-refl (Physical.realPart (Physical.cx v)))
        (BishopP.≃-refl (Physical.imaginaryPart (Physical.cx v)))))
    (complexMultiplyRespects scalarEq
      (complex-equivalent
        (BishopP.≃-refl (Physical.realPart (Physical.cy v)))
        (BishopP.≃-refl (Physical.imaginaryPart (Physical.cy v)))))
    (complexMultiplyRespects scalarEq
      (complex-equivalent
        (BishopP.≃-refl (Physical.realPart (Physical.cz v)))
        (BishopP.≃-refl (Physical.imaginaryPart (Physical.cz v)))))

rawCellAtZeroOutputVanishes :
  (uEta uZeta : Physical.BishopComplex3) →
  Complex3Equivalent
    (divergenceFormRawCell zeroFrequency uEta uZeta)
    (Physical.bishop-complex3 complexZero complexZero complexZero)
rawCellAtZeroOutputVanishes uEta uZeta =
  let
    dotZero = frequencyDotZero uEta

    iDotZero :
      ComplexEquivalent
        (complexMultiply complexI (frequencyDot zeroFrequency uEta))
        complexZero
    iDotZero =
      complexMultiplyRespects
        (complex-equivalent
          (BishopP.≃-refl BishopReal.0ℝ)
          (BishopP.≃-refl BishopReal.1ℝ))
        dotZero

    scaled =
      complexScale3RespectsScalar iDotZero uZeta

    zeroTimes :
      (z : Physical.BishopComplex) →
      ComplexEquivalent
        (complexMultiply complexZero z)
        complexZero
    zeroTimes z =
      let open BishopP.ℝ-Solver
      in complex-equivalent
        (solve 2
          (λ r i →
            Κ 0ℚᵘ ⊗ r ⊖ Κ 0ℚᵘ ⊗ i
            ⊜ Κ 0ℚᵘ)
          BishopP.≃-refl
          (Physical.realPart z) (Physical.imaginaryPart z))
        (solve 2
          (λ r i →
            Κ 0ℚᵘ ⊗ i ⊕ Κ 0ℚᵘ ⊗ r
            ⊜ Κ 0ℚᵘ)
          BishopP.≃-refl
          (Physical.realPart z) (Physical.imaginaryPart z))
  in
  complex3-equivalent
    (let q = xEquivalent scaled
     in complex-equivalent
       (BishopP.≃-trans (realEquivalent q)
         (realEquivalent (zeroTimes (Physical.cx uZeta))))
       (BishopP.≃-trans (imaginaryEquivalent q)
         (imaginaryEquivalent (zeroTimes (Physical.cx uZeta)))))
    (let q = yEquivalent scaled
     in complex-equivalent
       (BishopP.≃-trans (realEquivalent q)
         (realEquivalent (zeroTimes (Physical.cy uZeta))))
       (BishopP.≃-trans (imaginaryEquivalent q)
         (imaginaryEquivalent (zeroTimes (Physical.cy uZeta)))))
    (let q = zEquivalent scaled
     in complex-equivalent
       (BishopP.≃-trans (realEquivalent q)
         (realEquivalent (zeroTimes (Physical.cz uZeta))))
       (BishopP.≃-trans (imaginaryEquivalent q)
         (imaginaryEquivalent (zeroTimes (Physical.cz uZeta)))))

------------------------------------------------------------------------
-- Status: the exact PDE cell supplies one output-frequency zero.  Additional
-- powers required by the heat-cube target must come from the actual
-- Gram/opposite-shift/second-moment geometry, not from transversality alone.
------------------------------------------------------------------------

divergenceFormOutputFrequencyFactorClosed : Bool
divergenceFormOutputFrequencyFactorClosed = true

rawConvectionCellVanishesAtZeroOutput : Bool
rawConvectionCellVanishesAtZeroOutput = true

outputFactorPowersProvedHere : Bool
outputFactorPowersProvedHere = true

sixOutputPowersClaimedHere : Bool
sixOutputPowersClaimedHere = false

lerayProjectionPreservesOutputFactorClosedHere : Bool
lerayProjectionPreservesOutputFactorClosedHere = false

clayPromotion : Bool
clayPromotion = false

divergenceFormOutputFrequencyFactorClosedIsTrue :
  divergenceFormOutputFrequencyFactorClosed ≡ true
divergenceFormOutputFrequencyFactorClosedIsTrue = refl

sixOutputPowersClaimedHereIsFalse :
  sixOutputPowersClaimedHere ≡ false
sixOutputPowersClaimedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
