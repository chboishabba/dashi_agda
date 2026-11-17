module DASHI.Physics.YangMills.BalabanSU2VacuumPolarizationTensor where

open import Agda.Builtin.Equality using (_≡_)

-- A finite polarization tensor is the literal second variation of the finite
-- one-step effective action.  The symmetry and Ward identities are carried as
-- proof terms attached to that constructed derivative, rather than status
-- booleans.  Quantitative uniform beta bounds remain a separate analytic gate.
record FiniteVacuumPolarization
  (Background Direction Scalar Momentum : Set) : Set₁ where
  field
    zeroBackground : Background
    effectiveAction : Background → Scalar
    secondVariation : Direction → Direction → Scalar

    scalarZero : Scalar
    scalarAdd : Scalar → Scalar → Scalar
    scalarNegate : Scalar → Scalar

    translateDirection : Momentum → Direction → Direction
    divergenceDirection : Direction → Direction

    secondVariationSymmetric :
      ∀ X Y → secondVariation X Y ≡ secondVariation Y X

    translationCovariant :
      ∀ momentum X Y →
      secondVariation
        (translateDirection momentum X)
        (translateDirection momentum Y)
      ≡ secondVariation X Y

    wardTransverseLeft :
      ∀ X Y →
      secondVariation (divergenceDirection X) Y ≡ scalarZero

    wardTransverseRight :
      ∀ X Y →
      secondVariation X (divergenceDirection Y) ≡ scalarZero

open FiniteVacuumPolarization public

PolarizationCoefficientExtractor :
  ∀ {Background Direction Scalar Momentum} →
  FiniteVacuumPolarization Background Direction Scalar Momentum → Set₁
PolarizationCoefficientExtractor {Direction = Direction} {Scalar = Scalar} tensor =
  (Direction → Direction → Scalar) → Scalar

extractPolarizationCoefficient :
  ∀ {Background Direction Scalar Momentum}
  (tensor : FiniteVacuumPolarization Background Direction Scalar Momentum) →
  PolarizationCoefficientExtractor tensor → Scalar
extractPolarizationCoefficient tensor extractor =
  extractor (secondVariation tensor)

record PolarizationDecomposition
  {Background Direction Scalar Momentum : Set}
  (tensor : FiniteVacuumPolarization Background Direction Scalar Momentum)
  (extractor : PolarizationCoefficientExtractor tensor) : Set₁ where
  field
    yangMillsQuadraticTensor : Direction → Direction → Scalar
    higherDerivativeRemainder : Direction → Direction → Scalar

    decomposition :
      ∀ X Y →
      secondVariation tensor X Y
      ≡ scalarAdd tensor
          (yangMillsQuadraticTensor X Y)
          (higherDerivativeRemainder X Y)

    betaCoefficient : Scalar
    betaCoefficientIsExtracted :
      betaCoefficient ≡ extractPolarizationCoefficient tensor extractor

open PolarizationDecomposition public

polarizationSymmetry :
  ∀ {Background Direction Scalar Momentum}
  (tensor : FiniteVacuumPolarization Background Direction Scalar Momentum) →
  ∀ X Y → secondVariation tensor X Y ≡ secondVariation tensor Y X
polarizationSymmetry = secondVariationSymmetric

polarizationWardLeft :
  ∀ {Background Direction Scalar Momentum}
  (tensor : FiniteVacuumPolarization Background Direction Scalar Momentum) →
  ∀ X Y →
  secondVariation tensor (divergenceDirection tensor X) Y
    ≡ scalarZero tensor
polarizationWardLeft = wardTransverseLeft

polarizationWardRight :
  ∀ {Background Direction Scalar Momentum}
  (tensor : FiniteVacuumPolarization Background Direction Scalar Momentum) →
  ∀ X Y →
  secondVariation tensor X (divergenceDirection tensor Y)
    ≡ scalarZero tensor
polarizationWardRight = wardTransverseRight
