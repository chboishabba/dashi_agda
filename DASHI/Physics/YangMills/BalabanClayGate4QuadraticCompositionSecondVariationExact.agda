module DASHI.Physics.YangMills.BalabanClayGate4QuadraticCompositionSecondVariationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact second variation of a quadratic outer functional.
--
-- Kenneth G. Wilson, "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- For Q(z)=c<z,z> and a nonlinear plaquette map P,
--
--   D²(Q o P)[u,v]
--     = 2c <DP[u],DP[v]> + 2c <P,D²P[u,v]>.
--
-- The first term is the Gauss--Newton curvature sandwich. The second is the
-- exact nonlinear transport/chart remainder. This module fixes that ownership
-- before any norm estimate is introduced.
------------------------------------------------------------------------

record QuadraticSecondVariationAlgebra
    (State Vector Scalar : Set) : Set₁ where
  field
    addScalar multiplyScalar : Scalar → Scalar → Scalar
    inner : Vector → Vector → Scalar

    two : Scalar

    plaquetteMap : State → Vector
    derivative : State → State → Vector
    secondDerivative : State → State → State → Vector

open QuadraticSecondVariationAlgebra public

quadraticOuterValue :
  ∀ {State Vector Scalar} →
  QuadraticSecondVariationAlgebra State Vector Scalar →
  Scalar → State → Scalar
quadraticOuterValue algebra coefficient state =
  multiplyScalar algebra coefficient
    (inner algebra (plaquetteMap algebra state)
      (plaquetteMap algebra state))

curvatureGaussNewtonTerm :
  ∀ {State Vector Scalar} →
  QuadraticSecondVariationAlgebra State Vector Scalar →
  Scalar → State → State → State → Scalar
curvatureGaussNewtonTerm algebra coefficient base left right =
  multiplyScalar algebra
    (multiplyScalar algebra (two algebra) coefficient)
    (inner algebra
      (derivative algebra base left)
      (derivative algebra base right))

nonlinearPlaquetteSecondDerivativeTerm :
  ∀ {State Vector Scalar} →
  QuadraticSecondVariationAlgebra State Vector Scalar →
  Scalar → State → State → State → Scalar
nonlinearPlaquetteSecondDerivativeTerm algebra coefficient base left right =
  multiplyScalar algebra
    (multiplyScalar algebra (two algebra) coefficient)
    (inner algebra
      (plaquetteMap algebra base)
      (secondDerivative algebra base left right))

quadraticCompositeSecondVariation :
  ∀ {State Vector Scalar} →
  QuadraticSecondVariationAlgebra State Vector Scalar →
  Scalar → State → State → State → Scalar
quadraticCompositeSecondVariation algebra coefficient base left right =
  addScalar algebra
    (curvatureGaussNewtonTerm algebra coefficient base left right)
    (nonlinearPlaquetteSecondDerivativeTerm
      algebra coefficient base left right)

quadraticCompositeSecondVariationSplit :
  ∀ {State Vector Scalar}
    (algebra : QuadraticSecondVariationAlgebra State Vector Scalar)
    coefficient base left right →
  quadraticCompositeSecondVariation algebra coefficient base left right
  ≡ addScalar algebra
      (curvatureGaussNewtonTerm algebra coefficient base left right)
      (nonlinearPlaquetteSecondDerivativeTerm
        algebra coefficient base left right)
quadraticCompositeSecondVariationSplit algebra coefficient base left right = refl

record PhysicalQuadraticChainRuleMeaning
    {State Vector Scalar : Set}
    (algebra : QuadraticSecondVariationAlgebra State Vector Scalar)
    (coefficient : Scalar) : Set₁ where
  field
    physicalSecondVariation : State → State → State → Scalar

    physicalSecondVariationMeaning : ∀ base left right →
      physicalSecondVariation base left right
      ≡ quadraticCompositeSecondVariation
          algebra coefficient base left right

open PhysicalQuadraticChainRuleMeaning public

physicalSecondVariationAsCurvaturePlusNonlinear :
  ∀ {State Vector Scalar}
    {algebra : QuadraticSecondVariationAlgebra State Vector Scalar}
    {coefficient : Scalar}
    (meaning : PhysicalQuadraticChainRuleMeaning algebra coefficient)
    base left right →
  physicalSecondVariation meaning base left right
  ≡ addScalar algebra
      (curvatureGaussNewtonTerm algebra coefficient base left right)
      (nonlinearPlaquetteSecondDerivativeTerm
        algebra coefficient base left right)
physicalSecondVariationAsCurvaturePlusNonlinear
    meaning base left right =
  physicalSecondVariationMeaning meaning base left right

quadraticCompositionSecondVariationLevel : ProofLevel
quadraticCompositionSecondVariationLevel = machineChecked

wilsonCurvatureNonlinearOwnershipLevel : ProofLevel
wilsonCurvatureNonlinearOwnershipLevel = machineChecked

physicalWilsonPlaquetteSecondDerivativeInputsLevel : ProofLevel
physicalWilsonPlaquetteSecondDerivativeInputsLevel = conditional
