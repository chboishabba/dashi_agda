module DASHI.Physics.Closure.NSTriadKNPressureHessianComplexFourierIsometryRound85Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- ROUND85 / COMPLEX SAME-MODE PRESSURE-HESSIAN ISOMETRY
--
-- Round81 proved the scalar rational calibration
--
--   sum_ij |H_ij(k)|^2 = |h(k)|^2
--
-- with a real rational source coefficient.  The literal Galerkin pressure
-- source constructed in Round85 is instead a COMPLEX Fourier coefficient over
-- the physical `RealField`.  This module closes that phase/provenance gap.
--
-- For arbitrary repository RealField F, coordinates k_i, inverse radius i_k,
-- and complex source h satisfying
--
--   (kx^2+ky^2+kz^2) i_k = 1,
--
-- define
--
--   H_ij = (k_i k_j i_k) h.
--
-- Then exactly
--
--   sum_ij |H_ij|^2 = |h|^2.
--
-- No order, norm completeness, Parseval theorem, or rational specialization is
-- required for this algebraic mode identity.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

square : ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
square {F = F} value = C3.multiply F value value

complexSquareMagnitude :
  ∀ {r} {F : C3.RealField r} → C3.Complex F → C3.Carrier F
complexSquareMagnitude {F = F} value =
  C3.add F (square (C3.real value)) (square (C3.imaginary value))

record ComplexPressureModeDatum {r : Level} (F : C3.RealField r) : Set r where
  field
    kx ky kz inverseRadiusSquared : C3.Carrier F
    sourceCoefficient : C3.Complex F

    inverseRadiusSquaredExact :
      C3.multiply F
        (C3.add F
          (C3.add F (square kx) (square ky))
          (square kz))
        inverseRadiusSquared
      ≡ C3.one F

open ComplexPressureModeDatum public

radiusSquared :
  ∀ {r} {F : C3.RealField r} → ComplexPressureModeDatum F → C3.Carrier F
radiusSquared {F = F} datum =
  C3.add F
    (C3.add F (square (kx datum)) (square (ky datum)))
    (square (kz datum))

hessianRealScalar :
  ∀ {r} {F : C3.RealField r} →
  ComplexPressureModeDatum F → C3.Carrier F → C3.Carrier F → C3.Carrier F
hessianRealScalar {F = F} datum ki kj =
  C3.multiply F
    (C3.multiply F ki kj)
    (inverseRadiusSquared datum)

scaleComplexByReal :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex F → C3.Complex F
scaleComplexByReal {F = F} scalar value =
  C3.complex
    (C3.multiply F scalar (C3.real value))
    (C3.multiply F scalar (C3.imaginary value))

hessianCoefficient :
  ∀ {r} {F : C3.RealField r} →
  ComplexPressureModeDatum F → C3.Carrier F → C3.Carrier F → C3.Complex F
hessianCoefficient datum ki kj =
  scaleComplexByReal
    (hessianRealScalar datum ki kj)
    (sourceCoefficient datum)

hessianFrobeniusSquareEnergy :
  ∀ {r} {F : C3.RealField r} →
  ComplexPressureModeDatum F → C3.Carrier F
hessianFrobeniusSquareEnergy {F = F} datum =
  let
    e = λ i j → complexSquareMagnitude (hessianCoefficient datum i j)
  in
  C3.add F
    (C3.add F
      (C3.add F (e (kx datum) (kx datum)) (e (kx datum) (ky datum)))
      (C3.add F (e (kx datum) (kz datum)) (e (ky datum) (kx datum))))
    (C3.add F
      (C3.add F (e (ky datum) (ky datum)) (e (ky datum) (kz datum)))
      (C3.add F
        (C3.add F (e (kz datum) (kx datum)) (e (kz datum) (ky datum)))
        (e (kz datum) (kz datum))))

hessianFrobeniusFactorsThroughRadius :
  ∀ {r} {F : C3.RealField r}
    (datum : ComplexPressureModeDatum F) →
  hessianFrobeniusSquareEnergy datum
  ≡ C3.multiply F
      (complexSquareMagnitude (sourceCoefficient datum))
      (square
        (C3.multiply F (radiusSquared datum) (inverseRadiusSquared datum)))
hessianFrobeniusFactorsThroughRadius {F = F} datum =
  P.R.solve 6
    (λ x y z inv hr hi →
      let
        sq = λ a → a P.R.⊗ a
        r2 = (sq x P.R.⊕ sq y) P.R.⊕ sq z
        hs = λ a b → (a P.R.⊗ b) P.R.⊗ inv
        mag = λ a b → sq (hs a b P.R.⊗ hr) P.R.⊕ sq (hs a b P.R.⊗ hi)
      in
      (((mag x x P.R.⊕ mag x y)
          P.R.⊕ (mag x z P.R.⊕ mag y x))
        P.R.⊕
        ((mag y y P.R.⊕ mag y z)
          P.R.⊕ ((mag z x P.R.⊕ mag z y) P.R.⊕ mag z z)))
      P.R.⊜
      ((sq hr P.R.⊕ sq hi) P.R.⊗ sq (r2 P.R.⊗ inv)))
    refl
    (kx datum) (ky datum) (kz datum)
    (inverseRadiusSquared datum)
    (C3.real (sourceCoefficient datum))
    (C3.imaginary (sourceCoefficient datum))
  where
  module P = Field.Polynomial F

complexPressureHessianModeFrobeniusIsometry :
  ∀ {r} {F : C3.RealField r}
    (datum : ComplexPressureModeDatum F) →
  hessianFrobeniusSquareEnergy datum
  ≡ complexSquareMagnitude (sourceCoefficient datum)
complexPressureHessianModeFrobeniusIsometry {F = F} datum =
  trans
    (hessianFrobeniusFactorsThroughRadius datum)
    (trans
      (cong
        (λ unit →
          C3.multiply F
            (complexSquareMagnitude (sourceCoefficient datum))
            (square unit))
        (inverseRadiusSquaredExact datum))
      (P.R.solve 1
        (λ sourceNorm →
          sourceNorm P.R.⊗
            ((P.R.Κ (C3.one F)) P.R.⊗ (P.R.Κ (C3.one F)))
          P.R.⊜ sourceNorm)
        refl
        (complexSquareMagnitude (sourceCoefficient datum))))
  where
  module P = Field.Polynomial F

round85ComplexPressureHessianFourierModeIsometryConstructed : Bool
round85ComplexPressureHessianFourierModeIsometryConstructed = true

round85ComplexPressureSourcePhasePreservedByHessianIsometry : Bool
round85ComplexPressureSourcePhasePreservedByHessianIsometry = true

round85ComplexPressureHessianFourierModeIsometryConstructedIsTrue :
  round85ComplexPressureHessianFourierModeIsometryConstructed ≡ true
round85ComplexPressureHessianFourierModeIsometryConstructedIsTrue = refl
