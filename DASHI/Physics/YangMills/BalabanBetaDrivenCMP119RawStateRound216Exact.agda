{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119RawStateRound216Exact where

------------------------------------------------------------------------
-- ROUND216 / MAKE THE RAW CMP119 RUNNING COUPLING THE BETA-HISTORY COUPLING
--
-- `CMP119SourceNativeRawState` deliberately keeps source objects separate from
-- the theorem that they satisfy the Sect.-2 inductive class.  Its running
-- coupling was still freely supplied, so the active CMP122 bridge required a
-- post-hoc same-object equality with the finite beta history.
--
-- On the preferred route that equality is unnecessary.  Build the raw source
-- state with
--
--       runningCoupling = History.couplingAt history
--
-- from the outset.  All other rho/U/E/R/B/A objects remain literal source
-- inputs; no source existence or analytic theorem is manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

record BetaDrivenCMP119RawSourceInputs
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    (history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData)
    (Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set) : Set₁ where
  field
    terminalScale : Nat

    effectiveDensity : Nat → Density
    backgroundField : Nat → Background
    fluctuationFields : Nat → Fluctuation

    wilsonActionTerm : Nat → WilsonTerm
    regularSmallFieldTerm : Nat → SmallFieldTerm
    rOperationTerm : Nat → RTerm
    boundaryTerm : Nat → BoundaryTerm
    vacuumEnergy : Nat → Vacuum
    effectiveAction : Nat → Action

    actionAlgebra :
      Raw.CMP119RawActionAlgebra
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum

    wilsonCoefficient : Nat → ℚ

    equation223 : ∀ scale →
      effectiveAction scale
      ≡ Raw.assemble actionAlgebra
          (wilsonCoefficient scale)
          (wilsonActionTerm scale)
          (regularSmallFieldTerm scale)
          (rOperationTerm scale)
          (boundaryTerm scale)
          (vacuumEnergy scale)

open BetaDrivenCMP119RawSourceInputs public

asCMP119RawState :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum} →
  BetaDrivenCMP119RawSourceInputs
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
    history Density Background Fluctuation Action WilsonTerm SmallFieldTerm
    RTerm BoundaryTerm Vacuum →
  Raw.CMP119SourceNativeRawState
    Density Background Fluctuation Action WilsonTerm SmallFieldTerm
    RTerm BoundaryTerm Vacuum
asCMP119RawState {history = history} inputs = record
  { Raw.CMP119SourceNativeRawState.terminalScale = terminalScale inputs
  ; Raw.CMP119SourceNativeRawState.effectiveDensity = effectiveDensity inputs
  ; Raw.CMP119SourceNativeRawState.backgroundField = backgroundField inputs
  ; Raw.CMP119SourceNativeRawState.fluctuationFields = fluctuationFields inputs
  ; Raw.CMP119SourceNativeRawState.runningCoupling = History.couplingAt history
  ; Raw.CMP119SourceNativeRawState.wilsonActionTerm = wilsonActionTerm inputs
  ; Raw.CMP119SourceNativeRawState.regularSmallFieldTerm = regularSmallFieldTerm inputs
  ; Raw.CMP119SourceNativeRawState.rOperationTerm = rOperationTerm inputs
  ; Raw.CMP119SourceNativeRawState.boundaryTerm = boundaryTerm inputs
  ; Raw.CMP119SourceNativeRawState.vacuumEnergy = vacuumEnergy inputs
  ; Raw.CMP119SourceNativeRawState.effectiveAction = effectiveAction inputs
  ; Raw.CMP119SourceNativeRawState.actionAlgebra = actionAlgebra inputs
  ; Raw.CMP119SourceNativeRawState.wilsonCoefficient = wilsonCoefficient inputs
  ; Raw.CMP119SourceNativeRawState.equation223 = equation223 inputs
  }

rawRunningCouplingIsBetaHistoryCoupling :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum}
    (inputs : BetaDrivenCMP119RawSourceInputs
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
      history Density Background Fluctuation Action WilsonTerm SmallFieldTerm
      RTerm BoundaryTerm Vacuum) →
  ∀ scale →
  Raw.runningCoupling (asCMP119RawState inputs) scale
  ≡ History.couplingAt history scale
rawRunningCouplingIsBetaHistoryCoupling inputs scale = refl

betaDrivenCMP119RawStateCompilerLevel : ProofLevel
betaDrivenCMP119RawStateCompilerLevel = machineChecked

betaDrivenCMP119CouplingSameObjectLevel : ProofLevel
betaDrivenCMP119CouplingSameObjectLevel = machineChecked

-- Physical/source leaf: instantiate the literal CMP119 rho/U/E/R/B/A objects
-- and Eq.(2.23) action assembly on this beta-driven carrier.  The running
-- coupling identity itself is no longer an independent source payment.
literalBetaDrivenCMP119RawSourceInputsLevel : ProofLevel
literalBetaDrivenCMP119RawSourceInputsLevel = conditional
