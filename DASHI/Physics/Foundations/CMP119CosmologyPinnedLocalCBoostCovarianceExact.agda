{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCBoostCovarianceExact where

------------------------------------------------------------------------
-- PIN THE BOOST-COVARIANCE PRODUCER TO THE ACTUAL CMP119 LOCAL-C STRESS
-- AND THE ACTUAL PINNED OS RECONSTRUCTED VACUUM.
--
-- No arbitrary operator and no arbitrary vacuum remain here:
--
--   selected operator = LocalC.stressTensor localC
--   selected vacuum   = OSR.reconstructedVacuum reconstruction group
--
-- The remaining physical laws are therefore properties of those exact objects:
--
--   * isotropic rest-frame 01 expectation is zero;
--   * the selected reconstructed vacuum is invariant under the chosen boost at
--     the stress-expectation level;
--   * the boosted Local-C stress expectation equals the exact rank-two tensor
--     action already proved in CMP119CosmologySelectedBoostTensorActionExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; -_)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologySelectedBoostTensorActionExact as Tensor
import DASHI.Physics.Foundations.CMP119CosmologySelectedStressTensorCovarianceCompilerExact as Covariance

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record PinnedLocalCBoostCovariance
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₁ where
  field
    lorentzianIsotropicStress :
      Vacuum.IsotropicLorentzianStress

    boostStress :
      Top.StressTensor C → Top.StressTensor C

    stress01Expectation :
      Vector → Top.StressTensor C → ℚ

    localCStress01RestExpectationZero :
      stress01Expectation
        (OSR.reconstructedVacuum reconstruction group)
        (LocalC.stressTensor localC)
      ≡ 0ℚ

    reconstructedVacuumBoostInvariantOnStress01 :
      stress01Expectation
        (OSR.reconstructedVacuum reconstruction group)
        (boostStress (LocalC.stressTensor localC))
      ≡
      stress01Expectation
        (OSR.reconstructedVacuum reconstruction group)
        (LocalC.stressTensor localC)

    localCStressBoostTransformsAsRankTwoTensor :
      stress01Expectation
        (OSR.reconstructedVacuum reconstruction group)
        (boostStress (LocalC.stressTensor localC))
      ≡
      Tensor.t01
        (Tensor.boostBlock01
          (Tensor.isotropicRestBlock lorentzianIsotropicStress))

open PinnedLocalCBoostCovariance public

asSelectedStressTensorBoostCovariance :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  PinnedLocalCBoostCovariance
    {C = C} {S = S} Y group localC →
  Covariance.SelectedStressTensorBoostCovariance (Top.StressTensor C)
asSelectedStressTensorBoostCovariance
    {reconstruction = reconstruction} {group = group} {localC = localC} dataSet =
  record
    { Covariance.SelectedStressTensorBoostCovariance.lorentzianIsotropicStress =
        lorentzianIsotropicStress dataSet
    ; Covariance.SelectedStressTensorBoostCovariance.selectedT01 =
        LocalC.stressTensor localC
    ; Covariance.SelectedStressTensorBoostCovariance.boostConjugate =
        boostStress dataSet
    ; Covariance.SelectedStressTensorBoostCovariance.vacuumExpectation =
        stress01Expectation dataSet
          (OSR.reconstructedVacuum reconstruction group)
    ; Covariance.SelectedStressTensorBoostCovariance.unboostedT01ExpectationZero =
        localCStress01RestExpectationZero dataSet
    ; Covariance.SelectedStressTensorBoostCovariance.reconstructedVacuumExpectationInvariant =
        reconstructedVacuumBoostInvariantOnStress01 dataSet
    ; Covariance.SelectedStressTensorBoostCovariance.boostedT01ExpectationIsTensorAction =
        localCStressBoostTransformsAsRankTwoTensor dataSet
    }

pinnedLocalCBoostCovarianceForcesVacuumEquationOfState :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (dataSet :
      PinnedLocalCBoostCovariance
        {C = C} {S = S} Y group localC) →
  Vacuum.pressure (lorentzianIsotropicStress dataSet)
  ≡
  - Vacuum.rho (lorentzianIsotropicStress dataSet)
pinnedLocalCBoostCovarianceForcesVacuumEquationOfState dataSet =
  Covariance.selectedTensorCovarianceForcesVacuumEquationOfState
    (asSelectedStressTensorBoostCovariance dataSet)

operatorCarrierIsPinnedLocalCStress : Bool
operatorCarrierIsPinnedLocalCStress = true

vacuumCarrierIsPinnedOSReconstructedVacuum : Bool
vacuumCarrierIsPinnedOSReconstructedVacuum = true
