module DASHI.Physics.YangMills.BalabanSU2AdScalarReduction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; lieAdd; lieScale)
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  (adOperator)
open import DASHI.Physics.YangMills.BalabanSU2AdOperator using
  (cAd; lieNormSquared; adCubic)

record AdQuadraticCoefficients : Set where
  constructor adCoefficients
  field
    identityCoefficient : ℝ
    linearCoefficient : ℝ
    quadraticCoefficient : ℝ

open AdQuadraticCoefficients public

adQuadratic :
  AdQuadraticCoefficients →
  SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
adQuadratic coefficients Y X =
  lieAdd
    (lieScale (identityCoefficient coefficients) X)
    (lieAdd
      (lieScale (linearCoefficient coefficients) (adOperator Y X))
      (lieScale (quadraticCoefficient coefficients)
        (adOperator Y (adOperator Y X))))

-- Any cubic contribution can be folded back into the linear coefficient.
reduceCubicCoefficient :
  ℝ → AdQuadraticCoefficients → SU2LieAlgebra → AdQuadraticCoefficients
reduceCubicCoefficient cubic coefficients Y =
  adCoefficients
    (identityCoefficient coefficients)
    (linearCoefficient coefficients +R
      (cubic *R (-R (cAd *R lieNormSquared Y))))
    (quadraticCoefficient coefficients)

adQuadraticPlusCubicReduced :
  ∀ cubic coefficients Y X →
  lieAdd
    (adQuadratic coefficients Y X)
    (lieScale cubic
      (adOperator Y (adOperator Y (adOperator Y X))))
  ≡ adQuadratic (reduceCubicCoefficient cubic coefficients Y) Y X
adQuadraticPlusCubicReduced cubic coefficients Y X
  rewrite adCubic Y X = refl

record BoundedAdScalarApproximation : Set where
  constructor boundedAdApproximation
  field
    coefficients : AdQuadraticCoefficients
    coefficientBound : Set

open BoundedAdScalarApproximation public

applyAdScalarApproximation :
  BoundedAdScalarApproximation →
  SU2LieAlgebra → SU2LieAlgebra → SU2LieAlgebra
applyAdScalarApproximation approximation =
  adQuadratic (coefficients approximation)
