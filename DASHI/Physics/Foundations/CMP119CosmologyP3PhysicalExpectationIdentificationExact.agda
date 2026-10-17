{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3PhysicalExpectationIdentificationExact where

------------------------------------------------------------------------
-- P3 PHYSICAL IDENTIFICATION: ONE CMP119 F^2 OBSERVABLE, TWO APPROXIMATIONS
--
-- Do not postulate a new finite-sequence bridge.  The factorized CMP119 lane
-- already has the exact relation needed:
--
--   sourceExpectation O
--       versus
--   approximateExpectation_n O,
--
-- with an explicit expectationErrorBudget_n -> 0.
--
-- The physical identification is therefore only that the two existing Q3
-- consumers are looking at those two presentations of the SAME selected CMP119
-- observable/state carrier:
--
--   physical-Haar finite readout = sourceExpectation O
--   Local-C finite readout       = approximateExpectation_n O.
--
-- Once those same-object attachments are supplied, the existing factorized
-- density theorem constructs the asymptotic Q3 bridge automatically.  No third
-- bridge/error source is physical data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LocalLimit
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarLimit
import DASHI.Physics.Foundations.CMP119CosmologyP3AsymptoticFiniteF2CommonLimitExact as P3

import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Conv
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing

record FactorizedPhysicalExpectationIdentification
    {SlowField Sequence Component Step : Set}
    {approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (convergence :
      Conv.CMP119FactorizedDensityConvergence
        approximation sequenceLimit)
    (vanishing :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    (states : List SlowField)
    (scale : Nat)
    (observable : SlowField → ℝ)
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC : _}
    {embedding : _}
    {convention : _}
    {readout : _}
    (localTransport :
      LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout)
    (physicalHaar :
      HaarLimit.RealHaarExpectationRepresentation sequenceLimit) : Set₁ where
  field
    localFiniteF2IsFactorizedApproximation :
      ∀ refinement →
      LocalLimit.finiteF2Numerator localTransport refinement
      ≡
      Expect.approximateExpectation
        approximation states refinement scale observable

    haarFiniteF2IsFactorizedSourceExpectation :
      ∀ refinement →
      HaarLimit.finiteCMP119Expectation physicalHaar refinement
      ≡
      Expect.sourceExpectation approximation states scale observable

open FactorizedPhysicalExpectationIdentification public

compileFactorizedPhysicalIdentificationToQ3 :
  ∀ {SlowField Sequence Component Step approximation sequenceLimit}
    {convergence :
      Conv.CMP119FactorizedDensityConvergence
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation sequenceLimit}
    {vanishing : Vanishing.RealVanishingFiniteAlgebra sequenceLimit}
    {states : List SlowField}
    {scale : Nat}
    {observable : SlowField → ℝ}
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC embedding convention readout}
    {localTransport :
      LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout}
    {physicalHaar : HaarLimit.RealHaarExpectationRepresentation sequenceLimit} →
  FactorizedPhysicalExpectationIdentification
    convergence vanishing states scale observable
    localTransport physicalHaar →
  P3.AsymptoticCommonFiniteF2 localTransport physicalHaar
compileFactorizedPhysicalIdentificationToQ3
    {approximation = approximation}
    {convergence = convergence}
    {vanishing = vanishing}
    {states = states}
    {scale = scale}
    {observable = observable}
    {localTransport = localTransport}
    {physicalHaar = physicalHaar}
    identification = record
  { P3.AsymptoticCommonFiniteF2.bridgeError =
      λ refinement →
        Expect.expectationErrorBudget
          approximation states refinement scale observable
  ; P3.AsymptoticCommonFiniteF2.finiteF2BridgeBound =
      λ refinement → bridgeBound refinement
  ; P3.AsymptoticCommonFiniteF2.bridgeErrorVanishes =
      Expect.finiteExpectationBudgetVanishes
        convergence vanishing states scale observable
  }
  where
  bridgeBound :
    ∀ refinement →
    _
  bridgeBound refinement
    rewrite haarFiniteF2IsFactorizedSourceExpectation identification refinement
          | localFiniteF2IsFactorizedApproximation identification refinement =
    Expect.finiteExpectationDifferenceBound
      approximation states refinement scale observable

------------------------------------------------------------------------
-- Frontier accounting.
------------------------------------------------------------------------

factorizedPhysicalIdentificationCompilesQ3Bridge : Bool
factorizedPhysicalIdentificationCompilesQ3Bridge = true

independentAsymptoticQ3BridgeStillRequired : Bool
independentAsymptoticQ3BridgeStillRequired = false

sameFactorizedObservableCarriesBothFiniteLanes : Bool
sameFactorizedObservableCarriesBothFiniteLanes = true

-- What remains is not a free epsilon_n.  It is the physical same-object
-- attachment saying which literal Local-C and Haar finite readouts are the
-- factorized approximate/source expectations of this one F^2 observable.
remainingQ3DebtIsExpectationSameObjectAttachment : Bool
remainingQ3DebtIsExpectationSameObjectAttachment = true
