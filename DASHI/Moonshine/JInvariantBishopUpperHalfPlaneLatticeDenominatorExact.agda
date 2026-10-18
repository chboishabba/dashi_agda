module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact where

------------------------------------------------------------------------
-- UPPER-HALF-PLANE NONVANISHING OF m*tau+n
--
-- For Im(tau)>0 and (m,n) != (0,0):
--
--   * if m != 0, the imaginary component m*Im(tau) is apart from zero;
--   * if m = 0, then n != 0 and the real component n is apart from zero.
--
-- The generic component-apartness theorem then supplies positive norm-square,
-- hence the constructive complex reciprocal used by the literal Eisenstein
-- lattice kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as Component
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as Kernel
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

record BishopUpperHalfPlanePoint : Set where
  constructor bishop-upper-half-plane-point
  field
    tau : Complex.BishopComplex
    imaginaryPositive :
      BishopReal._<_ BishopReal.0ℝ (Complex.im tau)

open BishopUpperHalfPlanePoint public

positiveIntegerTimesPositiveApart :
  ∀ n {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopReal._≄0
    (BishopReal._*_
      (Kernel.embedInteger (+ suc n))
      imag)
positiveIntegerTimesPositiveApart n imagPositive =
  inj₂
    (BishopP.posx⇒0<x
      (BishopP.posx,y⇒posx*y
        (BishopP.0<x⇒posx
          (NatPositive.natRealSuccessorStrictlyPositive n))
        (BishopP.0<x⇒posx imagPositive)))

negativeIntegerTimesPositiveApart :
  ∀ n {imag : BishopReal.ℝ} →
  BishopReal._<_ BishopReal.0ℝ imag →
  BishopReal._≄0
    (BishopReal._*_
      (Kernel.embedInteger (-[1+ n ]))
      imag)
negativeIntegerTimesPositiveApart n imagPositive =
  let
    magnitude = Kernel.embedInteger (+ suc n)

    magnitudeProductPositive :
      BishopReal._<_ BishopReal.0ℝ
        (BishopReal._*_ magnitude imag)
    magnitudeProductPositive =
      BishopP.posx⇒0<x
        (BishopP.posx,y⇒posx*y
          (BishopP.0<x⇒posx
            (NatPositive.natRealSuccessorStrictlyPositive n))
          (BishopP.0<x⇒posx imagPositive))

    negatedProductNegative :
      BishopReal._<_
        (BishopReal.- (BishopReal._*_ magnitude imag))
        BishopReal.0ℝ
    negatedProductNegative =
      Component.positiveNegatesNegative magnitudeProductPositive

    productIsNegatedProduct :
      BishopReal._≃_
        (BishopReal._*_
          (Kernel.embedInteger (-[1+ n ]))
          imag)
        (BishopReal.- (BishopReal._*_ magnitude imag))
    productIsNegatedProduct =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ m y →
          (⊝ m) ⊗ y
          ⊜ ⊝ (m ⊗ y))
        BishopP.≃-refl
        magnitude imag
  in
  inj₁
    (BishopP.<-respˡ-≃
      productIsNegatedProduct
      negatedProductNegative)

positiveIntegerApart :
  ∀ n →
  BishopReal._≄0 (Kernel.embedInteger (+ suc n))
positiveIntegerApart n =
  inj₂ (NatPositive.natRealSuccessorStrictlyPositive n)

negativeIntegerApart :
  ∀ n →
  BishopReal._≄0 (Kernel.embedInteger (-[1+ n ]))
negativeIntegerApart n =
  inj₁
    (Component.positiveNegatesNegative
      (NatPositive.natRealSuccessorStrictlyPositive n))

imaginaryCoordinateApartPositiveM :
  ∀ {point : BishopUpperHalfPlanePoint} m n →
  BishopReal._≄0
    (Complex.im
      (Kernel.latticeDenominator
        (Lattice.lattice-point (+ suc m) n)
        (tau point)))
imaginaryCoordinateApartPositiveM {point} m n =
  let
    raw =
      positiveIntegerTimesPositiveApart
        m (imaginaryPositive point)

    normalize :
      BishopReal._≃_
        (Complex.im
          (Kernel.latticeDenominator
            (Lattice.lattice-point (+ suc m) n)
            (tau point)))
        (BishopReal._*_
          (Kernel.embedInteger (+ suc m))
          (Complex.im (tau point)))
    normalize =
      BishopP.+-identityʳ
        (BishopReal._*_
          (Kernel.embedInteger (+ suc m))
          (Complex.im (tau point)))
  in
  Component.apartCongruent
    (BishopP.≃-symm normalize)
    raw

imaginaryCoordinateApartNegativeM :
  ∀ {point : BishopUpperHalfPlanePoint} m n →
  BishopReal._≄0
    (Complex.im
      (Kernel.latticeDenominator
        (Lattice.lattice-point (-[1+ m ]) n)
        (tau point)))
imaginaryCoordinateApartNegativeM {point} m n =
  let
    raw =
      negativeIntegerTimesPositiveApart
        m (imaginaryPositive point)

    normalize :
      BishopReal._≃_
        (Complex.im
          (Kernel.latticeDenominator
            (Lattice.lattice-point (-[1+ m ]) n)
            (tau point)))
        (BishopReal._*_
          (Kernel.embedInteger (-[1+ m ]))
          (Complex.im (tau point)))
    normalize =
      BishopP.+-identityʳ
        (BishopReal._*_
          (Kernel.embedInteger (-[1+ m ]))
          (Complex.im (tau point)))
  in
  Component.apartCongruent
    (BishopP.≃-symm normalize)
    raw

realCoordinateApartZeroMPositiveN :
  ∀ {point : BishopUpperHalfPlanePoint} n →
  BishopReal._≄0
    (Complex.re
      (Kernel.latticeDenominator
        (Lattice.lattice-point (+ zero) (+ suc n))
        (tau point)))
realCoordinateApartZeroMPositiveN {point} n =
  let
    raw = positiveIntegerApart n
    embedded = Kernel.embedInteger (+ suc n)

    normalize :
      BishopReal._≃_
        (Complex.re
          (Kernel.latticeDenominator
            (Lattice.lattice-point (+ zero) (+ suc n))
            (tau point)))
        embedded
    normalize =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ x n′ →
          (Κ 0ℚᵘ ⊗ x) ⊕ n′
          ⊜ n′)
        BishopP.≃-refl
        (Complex.re (tau point))
        embedded
  in
  Component.apartCongruent
    (BishopP.≃-symm normalize)
    raw

realCoordinateApartZeroMNegativeN :
  ∀ {point : BishopUpperHalfPlanePoint} n →
  BishopReal._≄0
    (Complex.re
      (Kernel.latticeDenominator
        (Lattice.lattice-point (+ zero) (-[1+ n ]))
        (tau point)))
realCoordinateApartZeroMNegativeN {point} n =
  let
    raw = negativeIntegerApart n
    embedded = Kernel.embedInteger (-[1+ n ])

    normalize :
      BishopReal._≃_
        (Complex.re
          (Kernel.latticeDenominator
            (Lattice.lattice-point (+ zero) (-[1+ n ]))
            (tau point)))
        embedded
    normalize =
      let open BishopP.ℝ-Solver in
      solve 2
        (λ x n′ →
          (Κ 0ℚᵘ ⊗ x) ⊕ n′
          ⊜ n′)
        BishopP.≃-refl
        (Complex.re (tau point))
        embedded
  in
  Component.apartCongruent
    (BishopP.≃-symm normalize)
    raw

upperHalfPlaneDenominatorNonzero :
  (parameter : BishopUpperHalfPlanePoint) →
  (index : Kernel.NonzeroLatticePoint) →
  Reciprocal.BishopComplexNonzero
    (Kernel.latticeDenominator
      (Kernel.point index)
      (tau parameter))
upperHalfPlaneDenominatorNonzero parameter
  (Kernel.nonzero-lattice-point
    (Lattice.lattice-point (+ suc m) n)
    notOrigin) =
  Component.complexNonzeroFromImagApart
    (imaginaryCoordinateApartPositiveM {point = parameter} m n)
upperHalfPlaneDenominatorNonzero parameter
  (Kernel.nonzero-lattice-point
    (Lattice.lattice-point (-[1+ m ]) n)
    notOrigin) =
  Component.complexNonzeroFromImagApart
    (imaginaryCoordinateApartNegativeM {point = parameter} m n)
upperHalfPlaneDenominatorNonzero parameter
  (Kernel.nonzero-lattice-point
    (Lattice.lattice-point (+ zero) (+ suc n))
    notOrigin) =
  Component.complexNonzeroFromRealApart
    (realCoordinateApartZeroMPositiveN {point = parameter} n)
upperHalfPlaneDenominatorNonzero parameter
  (Kernel.nonzero-lattice-point
    (Lattice.lattice-point (+ zero) (-[1+ n ]))
    notOrigin) =
  Component.complexNonzeroFromRealApart
    (realCoordinateApartZeroMNegativeN {point = parameter} n)
upperHalfPlaneDenominatorNonzero parameter
  (Kernel.nonzero-lattice-point
    (Lattice.lattice-point (+ zero) (+ zero))
    notOrigin)
  with notOrigin refl
... | ()

upperHalfPlaneDenominatorGeometry :
  Kernel.BishopLatticeDenominatorGeometry
    BishopUpperHalfPlanePoint
    tau
upperHalfPlaneDenominatorGeometry = record
  { Kernel.denominatorNonzero =
      upperHalfPlaneDenominatorNonzero
  }
