{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityFiniteObservableToLocalCAnomalyTransportExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; absℝ; _-ℝ_; _≤ℝ_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as Target
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalCBridge
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace

import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityConvergenceExact as Conv
import DASHI.Physics.YangMills.BalabanCMP119FiniteObservableExpectationConvergenceExact as Expect
import DASHI.Physics.YangMills.BalabanRealVanishingFiniteAlgebraExact as Vanishing
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- REUSE THE EXISTING CMP119 FINITE-OBSERVABLE ERROR THEOREM
--
-- One CMP119 factorized-density approximation already proves, for every fixed
-- observable O on the selected finite state list:
--
--   |E_source[O] - E_refinement[O]| <= explicitBudget_O(refinement),
--   explicitBudget_O -> 0.
--
-- Therefore both trace and F^2 anomaly transports are compiler-owned once:
--
--   * the finite selected trace/F^2 numerators are identified with the two
--     approximateExpectation sequences;
--   * the pinned Local-C readouts are identified with the corresponding
--     sourceExpectation values.
--
-- No new convergence inequality is required by the antigravity lane.
------------------------------------------------------------------------

record CMP119AnomalyObservableIdentification
    {SlowField Sequence Component Step
     ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {approximation :
      Approx.CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (readout :
      LocalCBridge.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention)
    (states : List SlowField)
    (scale : Nat) : Set₁ where
  field
    traceObservable : SlowField → ℝ
    f2Observable : SlowField → ℝ

    -- Literal physical selected finite numerators.  These are not replaced by
    -- the factorized finite-state representation without an explicit weld.
    literalFiniteQuantumTraceNumerator : Nat → ℝ
    literalFiniteF2Numerator : Nat → ℝ

    literalFiniteTraceIsApproximateExpectation :
      ∀ refinement →
      literalFiniteQuantumTraceNumerator refinement
      ≡
      Expect.approximateExpectation
        approximation states refinement scale traceObservable

    literalFiniteF2IsApproximateExpectation :
      ∀ refinement →
      literalFiniteF2Numerator refinement
      ≡
      Expect.approximateExpectation
        approximation states refinement scale f2Observable

    localCTraceIsCMP119SourceExpectation :
      LocalCBridge.stressTraceNumerator readout
        (Local.stressTensor localC)
      ≡
      Expect.sourceExpectation
        approximation states scale traceObservable

    localCF2IsCMP119SourceExpectation :
      LocalCBridge.localOperatorNumerator readout
        (Local.localOperator localC
          (LocalCBridge.fieldStrengthSquarePolynomial readout))
      ≡
      Expect.sourceExpectation
        approximation states scale f2Observable

open CMP119AnomalyObservableIdentification public

compileFiniteObservableAnomalyLimitTransport :
  ∀ {SlowField Sequence Component Step
      ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian
      approximation sequenceLimit localC embedding convention}
    (convergence :
      Conv.CMP119FactorizedDensityConvergence
        {SlowField = SlowField}
        {Sequence = Sequence}
        {Component = Component}
        {Step = Step}
        approximation sequenceLimit)
    (vanishing :
      Vanishing.RealVanishingFiniteAlgebra sequenceLimit)
    {readout :
      LocalCBridge.SameFamilyLocalCTraceAnomalyReadout
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        localC embedding convention}
    {states : List SlowField}
    {scale : Nat}
    (identification :
      CMP119AnomalyObservableIdentification
        readout states scale) →
  Target.FiniteCMP119ToLocalCAnomalyLimitTransport
    sequenceLimit readout
compileFiniteObservableAnomalyLimitTransport
    {approximation = approximation}
    {sequenceLimit = sequenceLimit}
    {localC = localC}
    {readout = readout}
    {states = states}
    {scale = scale}
    convergence vanishing identification = record
  { Target.FiniteCMP119ToLocalCAnomalyLimitTransport.finiteQuantumTraceNumerator =
      literalFiniteQuantumTraceNumerator identification
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.finiteF2Numerator =
      literalFiniteF2Numerator identification
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.traceError =
      λ refinement →
        Expect.expectationErrorBudget
          approximation states refinement scale
          (traceObservable identification)
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.f2Error =
      λ refinement →
        Expect.expectationErrorBudget
          approximation states refinement scale
          (f2Observable identification)
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.finiteTraceApproximatesLocalC =
      λ refinement →
        subst
          (λ approximate →
            absℝ
              (LocalCBridge.stressTraceNumerator readout
                (Local.stressTensor localC)
                -ℝ approximate)
            ≤ℝ
            Expect.expectationErrorBudget
              approximation states refinement scale
              (traceObservable identification))
          (sym (literalFiniteTraceIsApproximateExpectation
            identification refinement))
          (subst
            (λ target →
              absℝ
                (target -ℝ
                  Expect.approximateExpectation
                    approximation states refinement scale
                    (traceObservable identification))
              ≤ℝ
              Expect.expectationErrorBudget
                approximation states refinement scale
                (traceObservable identification))
            (sym (localCTraceIsCMP119SourceExpectation identification))
            (Expect.finiteExpectationDifferenceBound
              approximation states refinement scale
              (traceObservable identification)))
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.finiteF2ApproximatesLocalC =
      λ refinement →
        subst
          (λ approximate →
            absℝ
              (LocalCBridge.localOperatorNumerator readout
                (Local.localOperator localC
                  (LocalCBridge.fieldStrengthSquarePolynomial readout))
                -ℝ approximate)
            ≤ℝ
            Expect.expectationErrorBudget
              approximation states refinement scale
              (f2Observable identification))
          (sym (literalFiniteF2IsApproximateExpectation
            identification refinement))
          (subst
            (λ target →
              absℝ
                (target -ℝ
                  Expect.approximateExpectation
                    approximation states refinement scale
                    (f2Observable identification))
              ≤ℝ
              Expect.expectationErrorBudget
                approximation states refinement scale
                (f2Observable identification))
            (sym (localCF2IsCMP119SourceExpectation identification))
            (Expect.finiteExpectationDifferenceBound
              approximation states refinement scale
              (f2Observable identification)))
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.traceErrorVanishes =
      Expect.finiteExpectationBudgetVanishes
        convergence vanishing states scale
        (traceObservable identification)
  ; Target.FiniteCMP119ToLocalCAnomalyLimitTransport.f2ErrorVanishes =
      Expect.finiteExpectationBudgetVanishes
        convergence vanishing states scale
        (f2Observable identification)
  }

cmp119AnomalyObservableErrorCompilerLevel : ProofLevel
cmp119AnomalyObservableErrorCompilerLevel = machineChecked

newAntigravityConvergenceInequalityRequired : Bool
newAntigravityConvergenceInequalityRequired = false

newAntigravityConvergenceInequalityRequiredIsFalse :
  newAntigravityConvergenceInequalityRequired ≡ false
newAntigravityConvergenceInequalityRequiredIsFalse = refl
