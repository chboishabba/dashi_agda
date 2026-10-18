{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3PhysicalExpectationIdentificationExact where

------------------------------------------------------------------------
-- P3 PHYSICAL IDENTIFICATION: ONE CMP119 F^2 OBSERVABLE, TWO APPROXIMATIONS
--
-- The factorized CMP119 lane already owns the exact estimate
--
--   |sourceExpectation O - approximateExpectation_n O|
--      <= expectationErrorBudget_n(O),
--
-- and proves that budget vanishes.  Therefore Q3 does not need a separately
-- postulated asymptotic bridge.  It only needs the two existing finite readouts
-- to be identified with the source/approximate expectations of the SAME
-- selected F^2 observable on the SAME finite state carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _-ℝ_; absℝ; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as LocalLimit
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarExpectationRepresentationExact as HaarLimit
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalTrace
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.Foundations.CMP119CosmologyP3AsymptoticFiniteF2CommonLimitExact as P3

import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Conv
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local

record FactorizedPhysicalExpectationIdentification
    {SlowField Sequence Component Step : Set}
    {approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step}
    (states : List SlowField)
    (scale : Nat)
    (observable : SlowField → ℝ)
    (localFinite haarFinite : Nat → ℝ) : Set₁ where
  field
    localFiniteF2IsFactorizedApproximation :
      ∀ refinement →
      localFinite refinement
      ≡
      Expect.approximateExpectation
        approximation states refinement scale observable

    haarFiniteF2IsFactorizedSourceExpectation :
      ∀ refinement →
      haarFinite refinement
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
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    {readout :
      LocalTrace.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention}
    {localTransport :
      LocalLimit.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout}
    {physicalHaar : HaarLimit.RealHaarExpectationRepresentation sequenceLimit} →
  FactorizedPhysicalExpectationIdentification
    {approximation = approximation}
    states scale observable
    (LocalLimit.finiteF2Numerator localTransport)
    (HaarLimit.finiteCMP119Expectation physicalHaar) →
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
  ; P3.AsymptoticCommonFiniteF2.finiteF2BridgeBound = bridgeBound
  ; P3.AsymptoticCommonFiniteF2.bridgeErrorVanishes =
      Expect.finiteExpectationBudgetVanishes
        convergence vanishing states scale observable
  }
  where
  bridgeBound :
    ∀ refinement →
    absℝ
      (HaarLimit.finiteCMP119Expectation physicalHaar refinement
        -ℝ LocalLimit.finiteF2Numerator localTransport refinement)
    ≤ℝ
    Expect.expectationErrorBudget
      approximation states refinement scale observable
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

-- The remaining source statement is now only the same-object attachment of the
-- literal finite readouts to these already-defined source/approximate
-- expectations.  The bridge estimate itself is no longer a physical input.
remainingQ3DebtIsExpectationSameObjectAttachment : Bool
remainingQ3DebtIsExpectationSameObjectAttachment = true
