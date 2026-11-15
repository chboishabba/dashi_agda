module DASHI.Physics.YangMills.BalabanSU2AdScalarReduction where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using ( Polynomial; _:=_; _:+_; _:*_; :-_ )

open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; -R_)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; su2Lie; su2LieExt; lieAdd; lieScale; xComponent; yComponent; zComponent)
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

reduceCubicCoefficient :
  ℝ → AdQuadraticCoefficients → SU2LieAlgebra → AdQuadraticCoefficients
reduceCubicCoefficient cubic coefficients Y =
  adCoefficients
    (identityCoefficient coefficients)
    (linearCoefficient coefficients +R
      (cubic *R (-R (cAd *R lieNormSquared Y))))
    (quadraticCoefficient coefficients)

scalarAdLemma : ∀ i x l w q v c k →
  ((i *R x) +R ((l *R w) +R (q *R v))) +R (c *R (k *R w)) ≡
  (i *R x) +R (((l +R (c *R k)) *R w) +R (q *R v))
scalarAdLemma =
  solveComputed 8
    (λ i x l w q v c k →
      ((i :* x :+ (l :* w :+ q :* v)) :+ (c :* (k :* w))) :=
      ((i :* x) :+ (((l :+ (c :* k)) :* w) :+ (q :* v))))
    computed

adQuadraticPlusCubicReduced :
  ∀ cubic coefficients Y X →
  lieAdd
    (adQuadratic coefficients Y X)
    (lieScale cubic
      (adOperator Y (adOperator Y (adOperator Y X))))
  ≡ adQuadratic (reduceCubicCoefficient cubic coefficients Y) Y X
adQuadraticPlusCubicReduced
  cubic (adCoefficients identity linear quadratic)
  Y X
  rewrite adCubic Y X =
  su2LieExt
    (scalarAdLemma
      identity (xComponent X)
      linear (xComponent (adOperator Y X))
      quadratic (xComponent (adOperator Y (adOperator Y X)))
      cubic (-R (cAd *R lieNormSquared Y)))
    (scalarAdLemma
      identity (yComponent X)
      linear (yComponent (adOperator Y X))
      quadratic (yComponent (adOperator Y (adOperator Y X)))
      cubic (-R (cAd *R lieNormSquared Y)))
    (scalarAdLemma
      identity (zComponent X)
      linear (zComponent (adOperator Y X))
      quadratic (zComponent (adOperator Y (adOperator Y X)))
      cubic (-R (cAd *R lieNormSquared Y)))

record BoundedAdScalarApproximation : Set₁ where
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
