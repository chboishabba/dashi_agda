module DASHI.Physics.YangMills.BalabanP33InverseDexpReducedOperatorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- On su(2), ad_X^3 = k(X) ad_X, so both dexp and inverse-dexp reduce to
-- I+a ad_X+b ad_X^2.  This module proves the actual left and right operator
-- inverse theorem from the two scalar coefficient equations.  The right
-- inverse is not postulated separately: it follows from the already checked
-- commutativity of the reduced polynomial calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  (_+R_; _*R_; oneR; zeroR; *-identityˡ)
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra)
open import DASHI.Physics.YangMills.BalabanSU2AdjointCubicReduction using
  (adCubicCoefficient)
open import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus using
  ( ReducedAdjointOperator; reducedAd; identityReducedAdjoint
  ; reducedAdjointExt; composeReducedAdjoint; composeReducedCommutative
  ; applyReducedAdjoint )
open import DASHI.Physics.YangMills.BalabanSU2AdjointAnalyticFunctionalCalculus using
  (inverseDexpActsLeft; inverseDexpActsRight)

dexpReducedOperator : ℝ → ℝ → ReducedAdjointOperator
dexpReducedOperator linear quadratic =
  reducedAd oneR linear quadratic

inverseDexpReducedOperator : ℝ → ℝ → ReducedAdjointOperator
inverseDexpReducedOperator linear quadratic =
  reducedAd oneR linear quadratic

record ReducedInverseCoefficientEquations
    (Y : SU2LieAlgebra)
    (dexpLinear dexpQuadratic inverseLinear inverseQuadratic : ℝ) : Set where
  field
    linearCoefficientCancels :
      (((oneR *R dexpLinear) +R (inverseLinear *R oneR))
        +R (adCubicCoefficient Y *R
          ((inverseLinear *R dexpQuadratic)
            +R (inverseQuadratic *R dexpLinear))))
      ≡ zeroR

    quadraticCoefficientCancels :
      ((((oneR *R dexpQuadratic)
          +R (inverseLinear *R dexpLinear))
          +R (inverseQuadratic *R oneR))
        +R (adCubicCoefficient Y *R
          (inverseQuadratic *R dexpQuadratic)))
      ≡ zeroR

open ReducedInverseCoefficientEquations public

inverseDexpCompositionLeftClosed :
  ∀ Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  ReducedInverseCoefficientEquations Y
    dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  composeReducedAdjoint Y
    (inverseDexpReducedOperator inverseLinear inverseQuadratic)
    (dexpReducedOperator dexpLinear dexpQuadratic)
  ≡ identityReducedAdjoint
inverseDexpCompositionLeftClosed
    Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations =
  reducedAdjointExt
    (*-identityˡ oneR)
    (linearCoefficientCancels equations)
    (quadraticCoefficientCancels equations)

inverseDexpCompositionRightClosed :
  ∀ Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  ReducedInverseCoefficientEquations Y
    dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  composeReducedAdjoint Y
    (dexpReducedOperator dexpLinear dexpQuadratic)
    (inverseDexpReducedOperator inverseLinear inverseQuadratic)
  ≡ identityReducedAdjoint
inverseDexpCompositionRightClosed
    Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations =
  trans
    (composeReducedCommutative Y
      (dexpReducedOperator dexpLinear dexpQuadratic)
      (inverseDexpReducedOperator inverseLinear inverseQuadratic))
    (inverseDexpCompositionLeftClosed
      Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations)

inverseDexpActsAsTwoSidedInverse :
  ∀ Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  ReducedInverseCoefficientEquations Y
    dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  ∀ X →
  applyReducedAdjoint Y
    (inverseDexpReducedOperator inverseLinear inverseQuadratic)
    (applyReducedAdjoint Y
      (dexpReducedOperator dexpLinear dexpQuadratic) X)
  ≡ X
inverseDexpActsAsTwoSidedInverse
    Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations X =
  inverseDexpActsLeft Y
    (dexpReducedOperator dexpLinear dexpQuadratic)
    (inverseDexpReducedOperator inverseLinear inverseQuadratic)
    (inverseDexpCompositionLeftClosed
      Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations)
    X

inverseDexpActsAsRightInverse :
  ∀ Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  ReducedInverseCoefficientEquations Y
    dexpLinear dexpQuadratic inverseLinear inverseQuadratic →
  ∀ X →
  applyReducedAdjoint Y
    (dexpReducedOperator dexpLinear dexpQuadratic)
    (applyReducedAdjoint Y
      (inverseDexpReducedOperator inverseLinear inverseQuadratic) X)
  ≡ X
inverseDexpActsAsRightInverse
    Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations X =
  inverseDexpActsRight Y
    (dexpReducedOperator dexpLinear dexpQuadratic)
    (inverseDexpReducedOperator inverseLinear inverseQuadratic)
    (inverseDexpCompositionRightClosed
      Y dexpLinear dexpQuadratic inverseLinear inverseQuadratic equations)
    X

p33ReducedInverseDexpOperatorLevel : ProofLevel
p33ReducedInverseDexpOperatorLevel = machineChecked

p33PhysicalCoefficientEquationInputsLevel : ProofLevel
p33PhysicalCoefficientEquationInputsLevel = conditional
