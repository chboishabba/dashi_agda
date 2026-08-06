module DASHI.Physics.YangMills.BalabanP33SU2QuadraticPrimitiveNormAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Connect the existing Cayley--Hamilton reduction
--
--   f(ad_X)-I = a(X) ad_X + b(X) ad_X^2
--
-- directly to the P33 primitive norm targets.  Once the three scalar
-- coefficient budgets fit inside rho, rho and rho respectively, the operator
-- estimates become
--
--   ||Ad(exp X)-I|| <= rho,
--   ||dexp_X-I|| + ||dexp_X^-1-I|| <= 2 rho.
--
-- The operator composition and triangle estimates are inherited from the
-- already checked quadratic-defect theorem; this file proves the rational
-- order transport and the paired dexp sum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2QuadraticChartDefectExact as Quadratic
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants

adBudget :
  ∀ {Operator} →
  Quadratic.SU2QuadraticChartDefects Operator ℚ → ℚ
adBudget dataSet =
  Quadratic.coefficientBudget (Quadratic.algebra dataSet)
    (Quadratic.adLinearCoefficient dataSet)
    (Quadratic.adQuadraticCoefficient dataSet)
    (Quadratic.adBound dataSet)

dexpBudget :
  ∀ {Operator} →
  Quadratic.SU2QuadraticChartDefects Operator ℚ → ℚ
dexpBudget dataSet =
  Quadratic.coefficientBudget (Quadratic.algebra dataSet)
    (Quadratic.dexpLinearCoefficient dataSet)
    (Quadratic.dexpQuadraticCoefficient dataSet)
    (Quadratic.adBound dataSet)

inverseDexpBudget :
  ∀ {Operator} →
  Quadratic.SU2QuadraticChartDefects Operator ℚ → ℚ
inverseDexpBudget dataSet =
  Quadratic.coefficientBudget (Quadratic.algebra dataSet)
    (Quadratic.dexpInverseLinearCoefficient dataSet)
    (Quadratic.dexpInverseQuadraticCoefficient dataSet)
    (Quadratic.adBound dataSet)

transportQuadraticOrder :
  ∀ {Operator}
    (dataSet : Quadratic.SU2QuadraticChartDefects Operator ℚ)
    left right →
  Quadratic.LessEqual (Quadratic.algebra dataSet) ≡ _≤_ →
  Quadratic.LessEqual (Quadratic.algebra dataSet) left right →
  left ≤ right
transportQuadraticOrder dataSet left right orderMeaning estimate =
  subst
    (λ relation → relation left right)
    orderMeaning
    estimate

adMinusIdentityNormBelowRadius :
  ∀ {Operator}
    (dataSet : Quadratic.SU2QuadraticChartDefects Operator ℚ)
    radius →
  Quadratic.LessEqual (Quadratic.algebra dataSet) ≡ _≤_ →
  adBudget dataSet ≤ radius →
  Quadratic.operatorNorm (Quadratic.algebra dataSet)
    (Quadratic.adMinusIdentity dataSet)
  ≤ radius
adMinusIdentityNormBelowRadius
    dataSet radius orderMeaning budgetBound =
  ℚP.≤-trans
    (transportQuadraticOrder dataSet _ _ orderMeaning
      (Quadratic.adMinusIdentityBoundFromQuadratic dataSet))
    budgetBound

dexpMinusIdentityNormBelowBudget :
  ∀ {Operator}
    (dataSet : Quadratic.SU2QuadraticChartDefects Operator ℚ) →
  Quadratic.LessEqual (Quadratic.algebra dataSet) ≡ _≤_ →
  Quadratic.operatorNorm (Quadratic.algebra dataSet)
    (Quadratic.dexpMinusIdentity dataSet)
  ≤ dexpBudget dataSet
dexpMinusIdentityNormBelowBudget dataSet orderMeaning =
  transportQuadraticOrder dataSet _ _ orderMeaning
    (Quadratic.dexpMinusIdentityBoundFromQuadratic dataSet)

inverseDexpMinusIdentityNormBelowBudget :
  ∀ {Operator}
    (dataSet : Quadratic.SU2QuadraticChartDefects Operator ℚ) →
  Quadratic.LessEqual (Quadratic.algebra dataSet) ≡ _≤_ →
  Quadratic.operatorNorm (Quadratic.algebra dataSet)
    (Quadratic.dexpInverseMinusIdentity dataSet)
  ≤ inverseDexpBudget dataSet
inverseDexpMinusIdentityNormBelowBudget dataSet orderMeaning =
  transportQuadraticOrder dataSet _ _ orderMeaning
    (Quadratic.dexpInverseMinusIdentityBoundFromQuadratic dataSet)

dexpPairNormBelowTwoRadius :
  ∀ {Operator}
    (dataSet : Quadratic.SU2QuadraticChartDefects Operator ℚ)
    radius →
  Quadratic.LessEqual (Quadratic.algebra dataSet) ≡ _≤_ →
  dexpBudget dataSet + inverseDexpBudget dataSet
    ≤ Constants.twoℚ * radius →
  Quadratic.operatorNorm (Quadratic.algebra dataSet)
      (Quadratic.dexpMinusIdentity dataSet)
  + Quadratic.operatorNorm (Quadratic.algebra dataSet)
      (Quadratic.dexpInverseMinusIdentity dataSet)
  ≤ Constants.twoℚ * radius
dexpPairNormBelowTwoRadius
    dataSet radius orderMeaning pairedBudget =
  ℚP.≤-trans
    (ℚP.+-mono-≤
      (dexpMinusIdentityNormBelowBudget dataSet orderMeaning)
      (inverseDexpMinusIdentityNormBelowBudget dataSet orderMeaning))
    pairedBudget

su2QuadraticAdPrimitiveBoundLevel : ProofLevel
su2QuadraticAdPrimitiveBoundLevel = machineChecked

su2QuadraticDexpPairPrimitiveBoundLevel : ProofLevel
su2QuadraticDexpPairPrimitiveBoundLevel = machineChecked
