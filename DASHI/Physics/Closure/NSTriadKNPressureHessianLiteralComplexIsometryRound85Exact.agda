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
-- The generic complex isometry is instantiated from the SAME
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
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
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
          P.R.⊕ ((P.R.Κ (C3.zero F)) P.R.⊗ y))
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
    lr = C3.multiply F left right
    scalar = C3.multiply F lr inv

    sourceMeaning :
      source
      ≡ C3.complexMultiply (C3.realEmbed F norm) pHat
    sourceMeaning =
      Field.complexMultiplyCommutative pHat (C3.realEmbed F norm)

    scalarTimesNorm : C3.multiply F scalar norm ≡ lr
    scalarTimesNorm =
      trans
        (P.R.solve 4
          (λ l r i n →
            (((l P.R.⊗ r) P.R.⊗ i) P.R.⊗ n)
            P.R.⊜ ((l P.R.⊗ r) P.R.⊗ (i P.R.⊗ n)))
          refl left right inv norm)
        (trans
          (cong (C3.multiply F lr) (C3.inverseLaw I mode nonzero))
          (trans
            (C3.multiplyCommutative F lr (C3.one F))
            (C3.multiplyOneLeft F lr)))

    realPrefixCollapse :
      C3.complexMultiply
        (C3.realEmbed F scalar)
        (C3.realEmbed F norm)
      ≡ C3.realEmbed F lr
    realPrefixCollapse =
      trans
        (LerayOut.realEmbedMultiply scalar norm)
        (cong (C3.realEmbed F) scalarTimesNorm)

    unsignedMeaning :
      Iso.hessianCoefficient
        (literalComplexPressureModeDatum system mode nonzero) left right
      ≡ C3.complexMultiply (C3.realEmbed F lr) pHat
    unsignedMeaning =
      trans
        (scaleComplexByRealMeaning scalar source)
        (trans
          (cong
            (C3.complexMultiply (C3.realEmbed F scalar))
            sourceMeaning)
          (trans
            (Field.complexMultiplyAssociative
              (C3.realEmbed F scalar) (C3.realEmbed F norm) pHat)
            (cong
              (λ prefix → C3.complexMultiply prefix pHat)
              realPrefixCollapse)))

    groupedLiteral :
      C3.complexMultiply (C3.realEmbed F lr) pHat
      ≡ C3.complexMultiply
          (C3.realEmbed F left)
          (C3.complexMultiply (C3.realEmbed F right) pHat)
    groupedLiteral =
      sym
        (trans
          (Field.complexMultiplyAssociative
            (C3.realEmbed F left) (C3.realEmbed F right) pHat)
          (cong
            (λ prefix → C3.complexMultiply prefix pHat)
            (LerayOut.realEmbedMultiply left right)))
  in
  trans
    (cong C3.complexNegate unsignedMeaning)
    (cong C3.complexNegate groupedLiteral)
  where module P = Field.Polynomial F

round85LiteralComplexPressureModeIsometryConstructed : Bool
round85LiteralComplexPressureModeIsometryConstructed = true

round85SignedHessianCoefficientSameLiteralPressurePotential : Bool
round85SignedHessianCoefficientSameLiteralPressurePotential = true

round85SignedHessianCoefficientSameLiteralPressurePotentialIsTrue :
  round85SignedHessianCoefficientSameLiteralPressurePotential ≡ true
round85SignedHessianCoefficientSameLiteralPressurePotentialIsTrue = refl
