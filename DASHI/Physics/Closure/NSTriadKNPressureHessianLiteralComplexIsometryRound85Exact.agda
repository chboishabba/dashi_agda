module DASHI.Physics.Closure.NSTriadKNPressureHessianLiteralComplexIsometryRound85Exact where

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
-- ROUND85 / LITERAL COMPLEX PRESSURE SOURCE INSTANTIATES HESSIAN ISOMETRY
--
-- The generic complex isometry is now instantiated from the SAME
-- `IntegerEmbedding`, `ModeInverseSquare`, Fourier mode and complex Poisson
-- source used by the literal Galerkin pressure potential.
--
-- With h = -Delta p and pHat the Round85 literal pressure potential,
--
--   h = |k|^2 pHat,
--   H_ij = - k_i k_j pHat
--        = - (k_i k_j / |k|^2) h.
--
-- Thus the unsigned multiplier used in the norm isometry differs from the
-- physical Hessian only by an explicit minus sign.  The Frobenius square is
-- exactly the complex source square magnitude with no phase loss.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPressurePotentialGradientHessianSameModeRound85Exact as Potential
import DASHI.Physics.Closure.NSTriadKNPressureTransportPoissonSplitRound85Exact as Transport
import DASHI.Physics.Closure.NSTriadKNPressureHessianComplexFourierIsometryRound85Exact as Iso

literalComplexPressureModeDatum :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode → Iso.ComplexPressureModeDatum F
literalComplexPressureModeDatum {F = F} {E = E} {I = I}
    system mode nonzero = record
  { Iso.ComplexPressureModeDatum.kx = C3.embedInteger E (Z3.kx mode)
  ; Iso.ComplexPressureModeDatum.ky = C3.embedInteger E (Z3.ky mode)
  ; Iso.ComplexPressureModeDatum.kz = C3.embedInteger E (Z3.kz mode)
  ; Iso.ComplexPressureModeDatum.inverseRadiusSquared =
      C3.inverseNormSquared I mode
  ; Iso.ComplexPressureModeDatum.sourceCoefficient =
      Transport.pressurePoissonSourceCoefficient system mode
  ; Iso.ComplexPressureModeDatum.inverseRadiusSquaredExact = inverseExact
  }
  where
  radius =
    C3.add F
      (C3.add F
        (C3.multiply F
          (C3.embedInteger E (Z3.kx mode))
          (C3.embedInteger E (Z3.kx mode)))
        (C3.multiply F
          (C3.embedInteger E (Z3.ky mode))
          (C3.embedInteger E (Z3.ky mode))))
      (C3.multiply F
        (C3.embedInteger E (Z3.kz mode))
        (C3.embedInteger E (Z3.kz mode)))

  inverseExact :
    C3.multiply F radius (C3.inverseNormSquared I mode) ≡ C3.one F
  inverseExact =
    trans
      (cong
        (λ norm → C3.multiply F norm (C3.inverseNormSquared I mode))
        (sym (C3.normSquaredMeaning I mode)))
      (trans
        (C3.multiplyCommutative F
          (C3.normSquared I mode) (C3.inverseNormSquared I mode))
        (C3.inverseLaw I mode nonzero))

literalPressureHessianComplexIsometry :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (mode : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode mode) →
  Iso.hessianFrobeniusSquareEnergy
    (literalComplexPressureModeDatum system mode nonzero)
  ≡ Iso.complexSquareMagnitude
      (Transport.pressurePoissonSourceCoefficient system mode)
literalPressureHessianComplexIsometry system mode nonzero =
  Iso.complexPressureHessianModeFrobeniusIsometry
    (literalComplexPressureModeDatum system mode nonzero)

scaleComplexByRealMeaning :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Carrier F)
    (value : C3.Complex F) →
  Iso.scaleComplexByReal scalar value
  ≡ C3.complexMultiply (C3.realEmbed F scalar) value
scaleComplexByRealMeaning {F = F} scalar (C3.complex real imaginary) =
  Field.complexExt
    (P.R.solve 2
      (λ s x →
        (s P.R.⊗ x)
        P.R.⊜ ((s P.R.⊗ x)
          P.R.⊕ P.R.⊝ ((P.R.Κ (C3.zero F)) P.R.⊗ (P.R.Κ (C3.zero F)))))
      refl scalar real)
    (P.R.solve 2
      (λ s y →
        (s P.R.⊗ y)
        P.R.⊜ ((s P.R.⊗ y)
          P.R.⊕ ((P.R.Κ (C3.zero F)) P.R.⊗ (P.R.Κ y)))
      refl scalar imaginary)
  where module P = Field.Polynomial F

literalSignedHessianCoefficient :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (mode : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode mode)
    (left right : C3.Carrier F) → C3.Complex F
literalSignedHessianCoefficient system mode nonzero left right =
  C3.complexNegate
    (Iso.hessianCoefficient
      (literalComplexPressureModeDatum system mode nonzero) left right)

signedHessianCoefficientMatchesLiteralPotential :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (mode : Z3.FourierMode)
    (nonzero : Z3.NonZeroMode mode)
    (left right : C3.Carrier F) →
  literalSignedHessianCoefficient system mode nonzero left right
  ≡ Potential.pressureHessianComponent
      left right (Potential.pressurePotential system mode)
signedHessianCoefficientMatchesLiteralPotential {F = F} {I = I}
    system mode nonzero left right =
  let
    inv = C3.inverseNormSquared I mode
    norm = C3.normSquared I mode
    pHat = Potential.pressurePotential system mode
    source = Transport.pressurePoissonSourceCoefficient system mode
    scalar = C3.multiply F (C3.multiply F left right) inv

    sourceMeaning :
      source
      ≡ C3.complexMultiply (C3.realEmbed F norm) pHat
    sourceMeaning =
      trans
        (C3.complexMultiplyCommutative
          pHat (C3.realEmbed F norm))
        refl

    unsignedMeaning :
      Iso.hessianCoefficient
        (literalComplexPressureModeDatum system mode nonzero) left right
      ≡ C3.complexMultiply
          (C3.realEmbed F (C3.multiply F left right)) pHat
    unsignedMeaning =
      trans
        (scaleComplexByRealMeaning scalar source)
        (trans
          (cong
            (C3.complexMultiply (C3.realEmbed F scalar))
            sourceMeaning)
          (Field.complexExt
            (P.R.solve 5
              (λ l r inv norm x →
                (((l P.R.⊗ r) P.R.⊗ inv) P.R.⊗ (norm P.R.⊗ x))
                P.R.⊜ ((l P.R.⊗ r) P.R.⊗ x))
              (C3.inverseLaw I mode nonzero)
              left right inv norm (C3.real pHat))
            (P.R.solve 5
              (λ l r inv norm y →
                (((l P.R.⊗ r) P.R.⊗ inv) P.R.⊗ (norm P.R.⊗ y))
                P.R.⊜ ((l P.R.⊗ r) P.R.⊗ y))
              (C3.inverseLaw I mode nonzero)
              left right inv norm (C3.imaginary pHat)))))
  in
  trans
    (cong C3.complexNegate unsignedMeaning)
    (trans
      (cong C3.complexNegate
        (sym
          (scaleComplexByRealMeaning
            (C3.multiply F left right) pHat)))
      (Field.complexExt
        (P.R.solve 3
          (λ l r x →
            (P.R.⊝ ((l P.R.⊗ r) P.R.⊗ x))
            P.R.⊜ (P.R.⊝ (l P.R.⊗ (r P.R.⊗ x))))
          refl left right (C3.real pHat))
        (P.R.solve 3
          (λ l r y →
            (P.R.⊝ ((l P.R.⊗ r) P.R.⊗ y))
            P.R.⊜ (P.R.⊝ (l P.R.⊗ (r P.R.⊗ y))))
          refl left right (C3.imaginary pHat))))
  where module P = Field.Polynomial F

round85LiteralComplexPressureModeIsometryConstructed : Bool
round85LiteralComplexPressureModeIsometryConstructed = true

round85SignedHessianCoefficientSameLiteralPressurePotential : Bool
round85SignedHessianCoefficientSameLiteralPressurePotential = true

round85SignedHessianCoefficientSameLiteralPressurePotentialIsTrue :
  round85SignedHessianCoefficientSameLiteralPressurePotential ≡ true
round85SignedHessianCoefficientSameLiteralPressurePotentialIsTrue = refl
