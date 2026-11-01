module DASHI.Moonshine.PenumbralVectorValuedForm where

-- Distinguished weight-one-half vector-valued modular forms attached to a
-- penumbral lambdency.  Component support, modularity, singular part, theta
-- ambiguity, and integral Fourier coefficients are all explicit witnesses.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.PenumbralLambency

record VectorValuedModularCarrier : Set₁ where
  field
    Scalar : Set
    UpperHalfPlane : Set
    MetaplecticElement : Set
    WeilRepresentation : Set
    FormalExponent : Set

    Vector : Set
    component : Vector → Nat → UpperHalfPlane → Scalar
    coefficient : Vector → Nat → FormalExponent → Scalar

    weightOneHalf : Set
    weaklyHolomorphic : Vector → Set
    transformsFor : Vector → WeilRepresentation → Set

record PenumbralSupport
  (carrier : VectorValuedModularCarrier)
  (arithmetic : LambencyArithmetic)
  {Discriminant : Set}
  (lambda : PenumbralLambdency arithmetic Discriminant) : Set₁ where
  open VectorValuedModularCarrier carrier
  field
    residueModulus : Nat
    ResidueModulusIsTwiceLevel : Nat → Nat → Set
    residueModulusCorrect :
      ResidueModulusIsTwiceLevel residueModulus
        (Lambency.level (PenumbralLambdency.lambency lambda))

    DiscriminantIndex : Set
    residue : DiscriminantIndex → Nat
    discriminant : DiscriminantIndex → Discriminant
    exponent : DiscriminantIndex → FormalExponent

    CongruentSquareModuloFourLevel : DiscriminantIndex → Set
    supportCongruence :
      (index : DiscriminantIndex) →
      CongruentSquareModuloFourLevel index

record PenumbralForm
  (carrier : VectorValuedModularCarrier)
  (arithmetic : LambencyArithmetic)
  {Discriminant : Set}
  (lambda : PenumbralLambdency arithmetic Discriminant)
  (support : PenumbralSupport carrier arithmetic lambda) : Setω where
  open VectorValuedModularCarrier carrier
  field
    weilRepresentation : WeilRepresentation
    form : Vector

    weakHolomorphy : weaklyHolomorphic form
    weightIsOneHalf : weightOneHalf
    weilTransformation : transformsFor form weilRepresentation

    SingularPart : Vector → Set
    distinguishedSingularPart : SingularPart form

    ThetaCorrection : Vector → Set
    thetaCorrectionControlled : ThetaCorrection form

    IntegralCoefficient : Scalar → Set
    integralFourierCoefficients :
      (index : PenumbralSupport.DiscriminantIndex support) →
      IntegralCoefficient
        (coefficient form
          (PenumbralSupport.residue support index)
          (PenumbralSupport.exponent support index))

    AtkinLehnerCompatible : Vector → Set
    atkinLehnerCompatibility : AtkinLehnerCompatible form

record PenumbralFormBoundary : Set where
  field
    weightOneHalfNotWeightZero : ⊤
    vectorValuedWeilLawRequired : ⊤
    singularPartDoesNotDetermineThetaCorrectionAutomatically : ⊤
    integralCoefficientsNeedProof : ⊤
    noModuleRealizationFromCoefficientsAlone : ⊤

penumbralFormBoundary : PenumbralFormBoundary
penumbralFormBoundary = record
  { weightOneHalfNotWeightZero = tt
  ; vectorValuedWeilLawRequired = tt
  ; singularPartDoesNotDetermineThetaCorrectionAutomatically = tt
  ; integralCoefficientsNeedProof = tt
  ; noModuleRealizationFromCoefficientsAlone = tt
  }
