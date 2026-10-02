{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedStressTensorCovarianceCompilerExact where

------------------------------------------------------------------------
-- SELECTED STRESS-OPERATOR BOOST COVARIANCE -> MAX-CUT EXPECTATION DATA.
--
-- This module removes the explicit -(20/9)(rho+p) formula from the QFT
-- covariance premise.  The physical input now only says:
--
--   expectation of the boosted selected T01 operator
--     =
--   the 01 component of the exact rank-two Lorentz transform
--   computed in CMP119CosmologySelectedBoostTensorActionExact.
--
-- The latter module proves that this component is -(20/9)(rho+p).
-- Therefore all coefficient algebra is repository-owned; only the actual
-- operator-covariance identification remains a physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; -_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologySelectedBoostTensorActionExact as Tensor\nimport DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantVacuumExact as Boost
import DASHI.Physics.Foundations.CMP119CosmologyVacuumExpectationBoostCompilerExact as Expectation

record SelectedStressTensorBoostCovariance
    (Operator : Set) : Set₁ where
  field
    lorentzianIsotropicStress :
      Vacuum.IsotropicLorentzianStress

    selectedT01 :
      Operator

    boostConjugate :
      Operator → Operator

    vacuumExpectation :
      Operator → ℚ

    unboostedT01ExpectationZero :
      vacuumExpectation selectedT01 ≡ 0ℚ

    reconstructedVacuumExpectationInvariant :
      vacuumExpectation (boostConjugate selectedT01)
      ≡
      vacuumExpectation selectedT01

    -- The only genuine operator-covariance seam left here.
    boostedT01ExpectationIsTensorAction :
      vacuumExpectation (boostConjugate selectedT01)
      ≡
      Tensor.t01
        (Tensor.boostBlock01
          (Tensor.isotropicRestBlock lorentzianIsotropicStress))

open SelectedStressTensorBoostCovariance public

boostedT01ExpectationIsClosedFormula :
  ∀ {Operator}
    (dataSet : SelectedStressTensorBoostCovariance Operator) →
  vacuumExpectation dataSet
    (boostConjugate dataSet (selectedT01 dataSet))
  ≡
  Boost.boosted01
    (lorentzianIsotropicStress dataSet)
boostedT01ExpectationIsClosedFormula dataSet =
  trans
    (boostedT01ExpectationIsTensorAction dataSet)
    (Tensor.boostedIsotropic01
      (lorentzianIsotropicStress dataSet))

asSelectedStressBoostExpectationData :
  ∀ {Operator} →
  SelectedStressTensorBoostCovariance Operator →
  Expectation.SelectedStressBoostExpectationData Operator
asSelectedStressBoostExpectationData dataSet = record
  { Expectation.SelectedStressBoostExpectationData.lorentzianIsotropicStress =
      lorentzianIsotropicStress dataSet
  ; Expectation.SelectedStressBoostExpectationData.selectedT01 =
      selectedT01 dataSet
  ; Expectation.SelectedStressBoostExpectationData.boostConjugate =
      boostConjugate dataSet
  ; Expectation.SelectedStressBoostExpectationData.vacuumExpectation =
      vacuumExpectation dataSet
  ; Expectation.SelectedStressBoostExpectationData.unboostedT01ExpectationZero =
      unboostedT01ExpectationZero dataSet
  ; Expectation.SelectedStressBoostExpectationData.reconstructedVacuumExpectationInvariant =
      reconstructedVacuumExpectationInvariant dataSet
  ; Expectation.SelectedStressBoostExpectationData.selectedStressOperatorCovariance =
      boostedT01ExpectationIsClosedFormula dataSet
  }

selectedTensorCovarianceForcesVacuumEquationOfState :
  ∀ {Operator}
    (dataSet : SelectedStressTensorBoostCovariance Operator) →
  Vacuum.pressure (lorentzianIsotropicStress dataSet)
  ≡
  - Vacuum.rho (lorentzianIsotropicStress dataSet)
selectedTensorCovarianceForcesVacuumEquationOfState dataSet =
  Expectation.operatorCovarianceAndVacuumInvarianceForceVacuumEquationOfState
    (asSelectedStressBoostExpectationData dataSet)

selectedTensorActionOwnsCoefficientAlgebra : Bool
selectedTensorActionOwnsCoefficientAlgebra = true

onlyOperatorCovarianceIdentificationRemains : Bool
onlyOperatorCovarianceIdentificationRemains = true
