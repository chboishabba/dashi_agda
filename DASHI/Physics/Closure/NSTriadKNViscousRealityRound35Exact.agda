module DASHI.Physics.Closure.NSTriadKNViscousRealityRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Close the linear half of the finite Galerkin Fourier-reality theorem.  The
-- viscosity and |k|^2 multiplier are real and |k|^2 is even, while the stored
-- velocity satisfies u_-k = conjugate u_k.  Hence the literal viscous
-- coefficient obeys
--
--   V(-k) = conjugate(V(k)).
--
-- We then prove that the full literal viscous-plus-quadratic coefficient has
-- Fourier reality from exactly one remaining premise: the summed projected
-- nonlinearity reality theorem.  Thus no additional linear or projection
-- algebra remains hidden behind the F1 compatibility producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact as InverseReality

viscousScalarEven :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : Coefficient.PhysicalFiniteComplex3GalerkinSystem F)
    (mode : Z3.FourierMode) →
  Coefficient.viscousScalar physicalSystem (Z3.negateMode mode)
  ≡ Coefficient.viscousScalar physicalSystem mode
viscousScalarEven {F = F} physicalSystem mode =
  cong
    (λ normValue →
      C3.realEmbed F
        (C3.negate F
          (C3.multiply F
            (Coefficient.viscosity physicalSystem)
            normValue)))
    (InverseReality.normSquaredEven
      (Audit.integerEmbedding system)
      (Audit.inverseSquare system)
      mode)
  where
  system = Coefficient.finiteSystem physicalSystem

viscousScalarConjugate :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : Coefficient.PhysicalFiniteComplex3GalerkinSystem F)
    (mode : Z3.FourierMode) →
  C3.complexConjugate (Coefficient.viscousScalar physicalSystem mode)
  ≡ Coefficient.viscousScalar physicalSystem mode
viscousScalarConjugate {F = F} physicalSystem mode =
  C3.realEmbedConjugate F _

literalViscousCoefficientReality :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : Coefficient.PhysicalFiniteComplex3GalerkinSystem F) →
  Reality.RealityCondition
    (Audit.velocity (Coefficient.finiteSystem physicalSystem)) →
  (mode : Z3.FourierMode) →
  Coefficient.literalViscousCoefficient physicalSystem (Z3.negateMode mode)
  ≡ C3.complex3Conjugate
      (Coefficient.literalViscousCoefficient physicalSystem mode)
literalViscousCoefficientReality physicalSystem velocityReality mode =
  trans
    (cong₂ C3.complex3Scale
      (viscousScalarEven physicalSystem mode)
      (velocityReality mode))
    (sym
      (trans
        (Scaling.complex3ConjugateScale
          (Coefficient.viscousScalar physicalSystem mode)
          (Audit.velocity (Coefficient.finiteSystem physicalSystem) mode))
        (cong
          (λ scalar →
            C3.complex3Scale scalar
              (C3.complex3Conjugate
                (Audit.velocity (Coefficient.finiteSystem physicalSystem) mode)))
          (viscousScalarConjugate physicalSystem mode))))

record SummedProjectedNonlinearityReality
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I) : Set r where
  field
    nonlinearReality :
      Reality.RealityCondition (Audit.projectedNonlinearity system)

open SummedProjectedNonlinearityReality public

literalViscousQuadraticCoefficientReality :
  ∀ {r} {F : C3.RealField r}
    (physicalSystem : Coefficient.PhysicalFiniteComplex3GalerkinSystem F) →
  (velocityReality :
    Reality.RealityCondition
      (Audit.velocity (Coefficient.finiteSystem physicalSystem))) →
  SummedProjectedNonlinearityReality (Coefficient.finiteSystem physicalSystem) →
  Reality.RealityCondition
    (Coefficient.literalViscousQuadraticCoefficient physicalSystem)
literalViscousQuadraticCoefficientReality
    physicalSystem velocityReality nonlinearReality mode =
  trans
    (cong₂ C3.complex3Add
      (literalViscousCoefficientReality physicalSystem velocityReality mode)
      (nonlinearReality nonlinearReality mode))
    (sym
      (Additive.complex3ConjugateAdd
        (Coefficient.literalViscousCoefficient physicalSystem mode)
        (Audit.projectedNonlinearity
          (Coefficient.finiteSystem physicalSystem) mode)))

literalViscousRealityClosed : Bool
literalViscousRealityClosed = true

wholeCoefficientRealityReducedToSummedNonlinearity : Bool
wholeCoefficientRealityReducedToSummedNonlinearity = true

literalViscousRealityClosedIsTrue : literalViscousRealityClosed ≡ true
literalViscousRealityClosedIsTrue = refl

wholeCoefficientRealityReducedToSummedNonlinearityIsTrue :
  wholeCoefficientRealityReducedToSummedNonlinearity ≡ true
wholeCoefficientRealityReducedToSummedNonlinearityIsTrue = refl
