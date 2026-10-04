{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyVacuumExpectationBoostCompilerExact where

------------------------------------------------------------------------
-- OPERATOR COVARIANCE + VACUUM INVARIANCE -> BOOST-INVARIANT STRESS EXPECTATION.
--
-- This module isolates the standard QFT algebra needed immediately upstream of
-- CMP119CosmologyPoincareVacuumStressMaxCutExact.
--
-- It deliberately keeps Hilbert/operator implementation abstract.  Given the
-- SAME reconstructed vacuum expectation, SAME selected stress operator, and
-- ONE selected Lorentz boost:
--
--   (1) vacuum expectation is invariant under conjugation by the boost;
--   (2) the transformed T01 expectation equals the rank-two tensor transform
--       -(20/9)(rho+p);
--   (3) the unboosted isotropic T01 expectation is zero;
--
-- then the numerical boost weld required by the antigravity max-cut is
-- constructed automatically.
--
-- Thus the genuine open theorem is no longer a free numerical equality.  It is
-- the operator-level covariance/continuation identification for the selected
-- CMP119 renormalized stress on the reconstructed Poincare vacuum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; -_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyBoostInvariantVacuumExact as Boost
import DASHI.Physics.Foundations.CMP119CosmologyPoincareVacuumStressMaxCutExact as MaxCut

record SelectedStressBoostExpectationData
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

    -- Isotropy of the unboosted selected tensor.
    unboostedT01ExpectationZero :
      vacuumExpectation selectedT01 ≡ 0ℚ

    -- U(Lambda) Omega = Omega, used at expectation level.
    reconstructedVacuumExpectationInvariant :
      vacuumExpectation (boostConjugate selectedT01)
      ≡
      vacuumExpectation selectedT01

    -- Rank-two covariance of the SAME selected renormalized stress operator.
    selectedStressOperatorCovariance :
      vacuumExpectation (boostConjugate selectedT01)
      ≡
      Boost.boosted01 lorentzianIsotropicStress

open SelectedStressBoostExpectationData public

boostedStressExpectationZero :
  ∀ {Operator}
    (dataSet : SelectedStressBoostExpectationData Operator) →
  vacuumExpectation dataSet (boostConjugate dataSet (selectedT01 dataSet))
  ≡ 0ℚ
boostedStressExpectationZero dataSet =
  trans
    (reconstructedVacuumExpectationInvariant dataSet)
    (unboostedT01ExpectationZero dataSet)

tensorTransformedBoosted01IsZero :
  ∀ {Operator}
    (dataSet : SelectedStressBoostExpectationData Operator) →
  Boost.boosted01 (lorentzianIsotropicStress dataSet)
  ≡ 0ℚ
tensorTransformedBoosted01IsZero dataSet =
  trans
    (sym (selectedStressOperatorCovariance dataSet))
    (boostedStressExpectationZero dataSet)

asSelectedPoincareVacuumStressBoostWeld :
  ∀ {Operator} →
  SelectedStressBoostExpectationData Operator →
  MaxCut.SelectedPoincareVacuumStressBoostWeld
asSelectedPoincareVacuumStressBoostWeld dataSet = record
  { MaxCut.SelectedPoincareVacuumStressBoostWeld.lorentzianIsotropicStress =
      lorentzianIsotropicStress dataSet
  ; MaxCut.SelectedPoincareVacuumStressBoostWeld.boostedStress01Expectation =
      vacuumExpectation dataSet
        (boostConjugate dataSet (selectedT01 dataSet))
  ; MaxCut.SelectedPoincareVacuumStressBoostWeld.stressCovarianceIdentifiesBoosted01 =
      selectedStressOperatorCovariance dataSet
  ; MaxCut.SelectedPoincareVacuumStressBoostWeld.vacuumInvarianceReturnsUnboosted01 =
      boostedStressExpectationZero dataSet
  }

operatorCovarianceAndVacuumInvarianceForceVacuumEquationOfState :
  ∀ {Operator}
    (dataSet : SelectedStressBoostExpectationData Operator) →
  Vacuum.pressure (lorentzianIsotropicStress dataSet)
  ≡
  - Vacuum.rho (lorentzianIsotropicStress dataSet)
operatorCovarianceAndVacuumInvarianceForceVacuumEquationOfState dataSet =
  MaxCut.selectedPoincareVacuumStressForcesVacuumEquationOfState
    (asSelectedPoincareVacuumStressBoostWeld dataSet)

------------------------------------------------------------------------
-- FRONTIER FLAGS
------------------------------------------------------------------------

numericalBoostInvarianceNoLongerPrimitive : Bool
numericalBoostInvarianceNoLongerPrimitive = true

selectedStressOperatorCovarianceStillRequired : Bool
selectedStressOperatorCovarianceStillRequired = true

selectedVacuumExpectationInvarianceStillRequiresConcreteReconstructionAction : Bool
selectedVacuumExpectationInvarianceStillRequiresConcreteReconstructionAction = true
