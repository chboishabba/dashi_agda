module DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Remove the last avoidable same-coupling receipt between the literal CMP119
-- raw state and the finite beta history.  The source objects other than the
-- running coupling are supplied as one raw complete-density family, and the
-- resulting CMP119 state is constructed with
--
--       runningCoupling k = History.couplingAt history k
--
-- definitionally.  Consequently the active-scale coupling identity is `refl`,
-- and the existing Round58 specialization of CMP122 Theorem 1 constructs the
-- active Sect.-2 witness without any independent equality hypothesis.
--
-- This does NOT assume Sect.-2 bounds or complete-density preservation: those
-- remain outputs of the published CMP122 theorem witness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP122Theorem1ToRawCMP119ActiveExact as Theorem1Raw

record CMP119RawObjectsOverHistory
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

open CMP119RawObjectsOverHistory public

rawStateFromFiniteBetaHistory :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set} →
  CMP119RawObjectsOverHistory history
    Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum →
  Raw.CMP119SourceNativeRawState
    Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
rawStateFromFiniteBetaHistory {history = history} objects = record
  { Raw.CMP119SourceNativeRawState.terminalScale = terminalScale objects
  ; Raw.CMP119SourceNativeRawState.effectiveDensity = effectiveDensity objects
  ; Raw.CMP119SourceNativeRawState.backgroundField = backgroundField objects
  ; Raw.CMP119SourceNativeRawState.fluctuationFields = fluctuationFields objects
  ; Raw.CMP119SourceNativeRawState.runningCoupling = History.couplingAt history
  ; Raw.CMP119SourceNativeRawState.wilsonActionTerm = wilsonActionTerm objects
  ; Raw.CMP119SourceNativeRawState.regularSmallFieldTerm = regularSmallFieldTerm objects
  ; Raw.CMP119SourceNativeRawState.rOperationTerm = rOperationTerm objects
  ; Raw.CMP119SourceNativeRawState.boundaryTerm = boundaryTerm objects
  ; Raw.CMP119SourceNativeRawState.vacuumEnergy = vacuumEnergy objects
  ; Raw.CMP119SourceNativeRawState.effectiveAction = effectiveAction objects
  ; Raw.CMP119SourceNativeRawState.actionAlgebra = actionAlgebra objects
  ; Raw.CMP119SourceNativeRawState.wilsonCoefficient = wilsonCoefficient objects
  ; Raw.CMP119SourceNativeRawState.equation223 = equation223 objects
  }

runningCouplingIsFiniteHistoryCoupling :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (objects : CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    scale →
  Raw.runningCoupling (rawStateFromFiniteBetaHistory objects) scale
  ≡ History.couplingAt history scale
runningCouplingIsFiniteHistoryCoupling objects scale = refl

activeRunningCouplingIsFiniteHistoryCoupling :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (objects : CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    scale → History.ActiveScale history scale →
  Raw.runningCoupling (rawStateFromFiniteBetaHistory objects) scale
  ≡ History.couplingAt history scale
activeRunningCouplingIsFiniteHistoryCoupling objects scale active = refl

activeRawWitnessFromFiniteHistoryAndTheorem1 :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (objects : CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    {predicates : Raw.CMP119Section2PredicateFamily
      (rawStateFromFiniteBetaHistory objects)} →
  (theorem1 :
    DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact.ActiveBalaban1989Theorem1Witness
      (Theorem1Raw.asActiveEffectiveDensityFlow
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {betaData = betaData} {history = history}
        predicates)) →
  Raw.ActiveCMP119Section2Witness
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {source = rawStateFromFiniteBetaHistory objects}
    predicates
activeRawWitnessFromFiniteHistoryAndTheorem1 objects theorem1 =
  Theorem1Raw.activeRawCMP119WitnessFromTheorem1
    (activeRunningCouplingIsFiniteHistoryCoupling objects)
    theorem1

cmp119RawStateFiniteHistoryCouplingLevel : ProofLevel
cmp119RawStateFiniteHistoryCouplingLevel = machineChecked

cmp119RawStateActiveTheorem1AssemblyLevel : ProofLevel
cmp119RawStateActiveTheorem1AssemblyLevel = machineChecked

-- Remaining L5 source leaf: instantiate `objects` and `predicates` with the
-- literal CMP119/CMP122 complete-density construction and quantitative norms.
-- The running-coupling equality is no longer part of that leaf.
cmp119LiteralRawObjectsAndPredicateInstantiationLevel : ProofLevel
cmp119LiteralRawObjectsAndPredicateInstantiationLevel = conditional
