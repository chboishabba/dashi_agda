module DASHI.Analysis.BishopComplexAlgebraExact where

------------------------------------------------------------------------
-- SETOID-NATIVE COMPLEX ALGEBRA ON THE CONCRETE BISHOP REAL CARRIER
--
-- DASHI CONTRIBUTION
--
-- This owner extends the already-existing BishopComplex pair carrier with the
-- exact finite algebra required by the Eisenstein q-series trajectory:
--
--   0, 1, +, -, *, natural scaling, and natural powers.
--
-- All operations remain on Bishop's setoid real carrier.  No propositional
-- quotient or legacy ConcreteComplex identification is used.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex

zeroC : Complex.BishopComplex
zeroC = Complex.complex BishopReal.0ℝ BishopReal.0ℝ

oneC : Complex.BishopComplex
oneC = Complex.complex BishopReal.1ℝ BishopReal.0ℝ

infixl 20 _+C_ _-C_
infixl 30 _*C_

_+C_ : Complex.BishopComplex → Complex.BishopComplex → Complex.BishopComplex
Complex.complex a b +C Complex.complex c d =
  Complex.complex
    (BishopReal._+_ a c)
    (BishopReal._+_ b d)

_-C_ : Complex.BishopComplex → Complex.BishopComplex → Complex.BishopComplex
Complex.complex a b -C Complex.complex c d =
  Complex.complex
    (BishopReal._-_ a c)
    (BishopReal._-_ b d)

_*C_ : Complex.BishopComplex → Complex.BishopComplex → Complex.BishopComplex
Complex.complex a b *C Complex.complex c d =
  Complex.complex
    (BishopReal._-_
      (BishopReal._*_ a c)
      (BishopReal._*_ b d))
    (BishopReal._+_
      (BishopReal._*_ a d)
      (BishopReal._*_ b c))

addCCongruent :
  ∀ {left left' right right'} →
  Complex._≈C_ left left' →
  Complex._≈C_ right right' →
  Complex._≈C_ (left +C right) (left' +C right')
addCCongruent
  {Complex.complex a b} {Complex.complex a' b'}
  {Complex.complex c d} {Complex.complex c' d'}
  (a≈a' , b≈b') (c≈c' , d≈d') =
  BishopP.+-cong a≈a' c≈c'
  ,
  BishopP.+-cong b≈b' d≈d'

subCCongruent :
  ∀ {left left' right right'} →
  Complex._≈C_ left left' →
  Complex._≈C_ right right' →
  Complex._≈C_ (left -C right) (left' -C right')
subCCongruent
  {Complex.complex a b} {Complex.complex a' b'}
  {Complex.complex c d} {Complex.complex c' d'}
  (a≈a' , b≈b') (c≈c' , d≈d') =
  BishopP.+-cong a≈a' (BishopP.-‿cong c≈c')
  ,
  BishopP.+-cong b≈b' (BishopP.-‿cong d≈d')

mulCCongruent :
  ∀ {left left' right right'} →
  Complex._≈C_ left left' →
  Complex._≈C_ right right' →
  Complex._≈C_ (left *C right) (left' *C right')
mulCCongruent
  {Complex.complex a b} {Complex.complex a' b'}
  {Complex.complex c d} {Complex.complex c' d'}
  (a≈a' , b≈b') (c≈c' , d≈d') =
  BishopP.+-cong
    (BishopP.*-cong a≈a' c≈c')
    (BishopP.-‿cong (BishopP.*-cong b≈b' d≈d'))
  ,
  BishopP.+-cong
    (BishopP.*-cong a≈a' d≈d')
    (BishopP.*-cong b≈b' c≈c')

scaleNatC : Nat → Complex.BishopComplex → Complex.BishopComplex
scaleNatC zero value = zeroC
scaleNatC (suc n) value = value +C scaleNatC n value

scaleNatCCongruent :
  ∀ {left right} →
  Complex._≈C_ left right →
  ∀ n →
  Complex._≈C_ (scaleNatC n left) (scaleNatC n right)
scaleNatCCongruent equivalent zero =
  Complex.≈C-refl zeroC
scaleNatCCongruent equivalent (suc n) =
  addCCongruent equivalent (scaleNatCCongruent equivalent n)

powC : Complex.BishopComplex → Nat → Complex.BishopComplex
powC value zero = oneC
powC value (suc n) = value *C powC value n

powCCongruent :
  ∀ {left right} →
  Complex._≈C_ left right →
  ∀ n →
  Complex._≈C_ (powC left n) (powC right n)
powCCongruent equivalent zero =
  Complex.≈C-refl oneC
powCCongruent equivalent (suc n) =
  mulCCongruent equivalent (powCCongruent equivalent n)
