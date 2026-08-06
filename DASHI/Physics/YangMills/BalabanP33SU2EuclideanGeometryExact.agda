module DASHI.Physics.YangMills.BalabanP33SU2EuclideanGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Fix the repository's literal su(2) normalization and Euclidean geometry.
-- The quaternion commutator convention is
--
--   [X,Y] = 2 X cross Y,
--
-- so ad_X has cubic polynomial
--
--   ad_X^3 = -4 <X,X> ad_X.
--
-- This module proves, by computed polynomial normalization, the exact Gram
-- identity, the exact squared norm of ad_X Y, the gamma=2 Cayley--Hamilton
-- normalization, unit-quaternion adjoint isometry, and the coordinate/basis
-- identities needed to turn abstract operator coefficients into concrete
-- su(2) matrix coefficients.  No analytic inequality or norm socket is added.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  ( module RealPolynomialSolver; zeroCoefficient; oneCoefficient )
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  ( solveComputed; computed )
open RealPolynomialSolver using
  ( Polynomial; con; _:=_; _:+_; _:*_; :-_ )
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( _+R_; _*R_; -R_; zeroR; oneR; SU2Quaternion )
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  ( SU2LieAlgebra; su2Lie; xComponent; yComponent; zComponent
  ; lieScale; su2Adjoint )
open import DASHI.Physics.YangMills.BalabanSU2AdjointInnerProduct using
  ( su2Dot; su2DotAdjointInvariant )
open import DASHI.Physics.YangMills.BalabanSU2LieBracket using
  ( adOperator; bracket1P; bracket2P; bracket3P; dotP )
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  ( fourR; fourP; adCubicCoefficient
  ; adSquareVectorIdentity; adCubicReduction )

zeroP : ∀ {n} → Polynomial n
zeroP = con zeroCoefficient

oneP : ∀ {n} → Polynomial n
oneP = con oneCoefficient

su2NormSq : SU2LieAlgebra → ℝ
su2NormSq X = su2Dot X X

minorXY minorXZ minorYZ : SU2LieAlgebra → SU2LieAlgebra → ℝ
minorXY X Y =
  (xComponent X *R yComponent Y)
  +R (-R (yComponent X *R xComponent Y))
minorXZ X Y =
  (xComponent X *R zComponent Y)
  +R (-R (zComponent X *R xComponent Y))
minorYZ X Y =
  (yComponent X *R zComponent Y)
  +R (-R (zComponent X *R yComponent Y))

gramGap : SU2LieAlgebra → SU2LieAlgebra → ℝ
gramGap X Y =
  (su2NormSq X *R su2NormSq Y)
  +R (-R (su2Dot X Y *R su2Dot X Y))

gramMinorSum : SU2LieAlgebra → SU2LieAlgebra → ℝ
gramMinorSum X Y =
  ((minorXY X Y *R minorXY X Y)
    +R (minorXZ X Y *R minorXZ X Y))
  +R (minorYZ X Y *R minorYZ X Y)

gramGapIsThreeSquares : ∀ X Y →
  gramGap X Y ≡ gramMinorSum X Y
gramGapIsThreeSquares
    (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  solveComputed 6
    (λ x₁ y₁ z₁ x₂ y₂ z₂ →
      ((dotP x₁ y₁ z₁ x₁ y₁ z₁ :*
          dotP x₂ y₂ z₂ x₂ y₂ z₂)
        :+ (:- (dotP x₁ y₁ z₁ x₂ y₂ z₂ :*
          dotP x₁ y₁ z₁ x₂ y₂ z₂)))
      :=
      ((((x₁ :* y₂) :+ (:- (y₁ :* x₂))) :*
          ((x₁ :* y₂) :+ (:- (y₁ :* x₂))))
        :+ (((x₁ :* z₂) :+ (:- (z₁ :* x₂))) :*
          ((x₁ :* z₂) :+ (:- (z₁ :* x₂)))))
        :+ (((y₁ :* z₂) :+ (:- (z₁ :* y₂))) :*
          ((y₁ :* z₂) :+ (:- (z₁ :* y₂)))))
    computed x₁ y₁ z₁ x₂ y₂ z₂

adNormSqIsFourGramGap : ∀ X Y →
  su2NormSq (adOperator X Y)
  ≡ fourR *R gramGap X Y
adNormSqIsFourGramGap
    (su2Lie x₁ y₁ z₁) (su2Lie x₂ y₂ z₂) =
  solveComputed 6
    (λ x₁ y₁ z₁ x₂ y₂ z₂ →
      dotP
        (bracket1P y₁ z₁ y₂ z₂)
        (bracket2P z₁ x₁ z₂ x₂)
        (bracket3P x₁ y₁ x₂ y₂)
        (bracket1P y₁ z₁ y₂ z₂)
        (bracket2P z₁ x₁ z₂ x₂)
        (bracket3P x₁ y₁ x₂ y₂)
      :=
      fourP :*
        ((dotP x₁ y₁ z₁ x₁ y₁ z₁ :*
            dotP x₂ y₂ z₂ x₂ y₂ z₂)
          :+ (:- (dotP x₁ y₁ z₁ x₂ y₂ z₂ :*
            dotP x₁ y₁ z₁ x₂ y₂ z₂))))
    computed x₁ y₁ z₁ x₂ y₂ z₂

adNormSqIsFourMinorSquares : ∀ X Y →
  su2NormSq (adOperator X Y)
  ≡ fourR *R gramMinorSum X Y
adNormSqIsFourMinorSquares X Y
  rewrite adNormSqIsFourGramGap X Y
        | gramGapIsThreeSquares X Y =
  refl

adSquareGammaTwoExact : ∀ X Y →
  adOperator X (adOperator X Y)
  ≡ su2Lie
      (fourR *R
        ((su2Dot X Y *R xComponent X)
          +R (-R (su2NormSq X *R xComponent Y))))
      (fourR *R
        ((su2Dot X Y *R yComponent X)
          +R (-R (su2NormSq X *R yComponent Y))))
      (fourR *R
        ((su2Dot X Y *R zComponent X)
          +R (-R (su2NormSq X *R zComponent Y))))
adSquareGammaTwoExact = adSquareVectorIdentity

adCubicCoefficientGammaTwo : ∀ X →
  adCubicCoefficient X ≡ -R (fourR *R su2NormSq X)
adCubicCoefficientGammaTwo X = refl

adCubicGammaTwoExact : ∀ X Y →
  adOperator X (adOperator X (adOperator X Y))
  ≡ lieScale (-R (fourR *R su2NormSq X)) (adOperator X Y)
adCubicGammaTwoExact X Y = adCubicReduction X Y

su2AdjointNormSqInvariant : ∀ u X →
  su2NormSq (su2Adjoint u X) ≡ su2NormSq X
su2AdjointNormSqInvariant u X = su2DotAdjointInvariant u X X

basisX basisY basisZ : SU2LieAlgebra
basisX = su2Lie oneR zeroR zeroR
basisY = su2Lie zeroR oneR zeroR
basisZ = su2Lie zeroR zeroR oneR

basisXCoordinate : ∀ X → su2Dot basisX X ≡ xComponent X
basisXCoordinate (su2Lie x y z) =
  solveComputed 3
    (λ x y z → dotP oneP zeroP zeroP x y z := x)
    computed x y z

basisYCoordinate : ∀ X → su2Dot basisY X ≡ yComponent X
basisYCoordinate (su2Lie x y z) =
  solveComputed 3
    (λ x y z → dotP zeroP oneP zeroP x y z := y)
    computed x y z

basisZCoordinate : ∀ X → su2Dot basisZ X ≡ zComponent X
basisZCoordinate (su2Lie x y z) =
  solveComputed 3
    (λ x y z → dotP zeroP zeroP oneP x y z := z)
    computed x y z

basisXNormSq : su2NormSq basisX ≡ oneR
basisXNormSq =
  solveComputed 0
    (dotP oneP zeroP zeroP oneP zeroP zeroP := oneP)
    computed

basisYNormSq : su2NormSq basisY ≡ oneR
basisYNormSq =
  solveComputed 0
    (dotP zeroP oneP zeroP zeroP oneP zeroP := oneP)
    computed

basisZNormSq : su2NormSq basisZ ≡ oneR
basisZNormSq =
  solveComputed 0
    (dotP zeroP zeroP oneP zeroP zeroP oneP := oneP)
    computed

su2EuclideanGramIdentityLevel : ProofLevel
su2EuclideanGramIdentityLevel = machineChecked

su2AdjointNormIdentityLevel : ProofLevel
su2AdjointNormIdentityLevel = machineChecked

su2AdjointGammaTwoCayleyHamiltonLevel : ProofLevel
su2AdjointGammaTwoCayleyHamiltonLevel = machineChecked

su2ConcreteBasisCoordinateLevel : ProofLevel
su2ConcreteBasisCoordinateLevel = machineChecked
