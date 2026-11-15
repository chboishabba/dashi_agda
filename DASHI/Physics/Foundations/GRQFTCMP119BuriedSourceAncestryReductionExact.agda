{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTCMP119BuriedSourceAncestryReductionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact as Old
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RawStateFromFiniteBetaHistoryExact as Existing
import DASHI.Physics.YangMills.BalabanCMP119Section2StateToFiniteHistoryRawObjectsBidiExact as Bridge

------------------------------------------------------------------------
-- BURIED SOURCE-ANCESTRY REDUCTION
--
-- The older source-native Section-2 state already carries the literal density,
-- background/fluctuation fields, Wilson/E/R/B/vacuum pieces, effective action,
-- action algebra, Wilson coefficient and Eq. (2.23).  The existing bridge
-- packages those exact objects as `CMP119RawObjectsOverHistory`, after which
-- `rawStateFromFiniteBetaHistory` changes only the running-coupling owner.
--
-- Therefore the source-native -> raw ancestry is compiler-owned.  The honest
-- remaining same-object leaf for the repulsive-bubble lane is downstream:
-- the metric response of THIS raw Eq.(2.23) action must be identified with the
-- selected canonical/pinned R136 metric-stress response.
------------------------------------------------------------------------

module _
  {trajectory : Flow.SourceNormalizedCouplingTrajectory}
  {Mode Atom : Set}
  {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
  {history : History.FiniteModeInverseSquareTerminalHistoryData
    trajectory Mode Atom betaData}
  {Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
  (source : Old.CMP119Section2SourceNativeState
    Density Background Fluctuation
    Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
  where

  rawObjects :
    Existing.CMP119RawObjectsOverHistory history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
  rawObjects = Bridge.sourceStateToRawObjectsOverHistory {history = history} source

  rawSource :
    Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum
  rawSource = Existing.rawStateFromFiniteBetaHistory rawObjects

  sourceVacuumPreserved : ∀ scale →
    Old.vacuumEnergy source scale ≡ Raw.vacuumEnergy rawSource scale
  sourceVacuumPreserved scale = refl

  sourceEffectiveActionPreserved : ∀ scale →
    Old.effectiveAction source scale ≡ Raw.effectiveAction rawSource scale
  sourceEffectiveActionPreserved scale = refl

  sourceWilsonTermPreserved : ∀ scale →
    Old.wilsonActionTerm source scale ≡ Raw.wilsonActionTerm rawSource scale
  sourceWilsonTermPreserved scale = refl

  sourceRegularTermPreserved : ∀ scale →
    Old.regularSmallFieldTerm source scale
      ≡ Raw.regularSmallFieldTerm rawSource scale
  sourceRegularTermPreserved scale = refl

  sourceROperationTermPreserved : ∀ scale →
    Old.rOperationTerm source scale ≡ Raw.rOperationTerm rawSource scale
  sourceROperationTermPreserved scale = refl

  sourceBoundaryTermPreserved : ∀ scale →
    Old.boundaryTerm source scale ≡ Raw.boundaryTerm rawSource scale
  sourceBoundaryTermPreserved scale = refl

  sourceEquation223Preserved : ∀ scale →
    Raw.effectiveAction rawSource scale
    ≡ Raw.assemble (Raw.actionAlgebra rawSource)
        (Raw.wilsonCoefficient rawSource scale)
        (Raw.wilsonActionTerm rawSource scale)
        (Raw.regularSmallFieldTerm rawSource scale)
        (Raw.rOperationTerm rawSource scale)
        (Raw.boundaryTerm rawSource scale)
        (Raw.vacuumEnergy rawSource scale)
  sourceEquation223Preserved scale = Raw.equation223 rawSource scale

record BuriedSourceAncestryBoundary : Set where
  constructor buried-source-ancestry-boundary
  field
    sourceObjectsToRawStateAlreadyCompilerOwned : Bool
    sourceVacuumObjectPreservedDefinitionally : Bool
    sourceEffectiveActionPreservedDefinitionally : Bool
    sourceEq223Preserved : Bool
    independentSourceToRawAncestryAuthorityNeeded : Bool
    remainingGapIsRawEq223ResponseToPinnedR136 : Bool

canonicalBuriedSourceAncestryBoundary : BuriedSourceAncestryBoundary
canonicalBuriedSourceAncestryBoundary =
  buried-source-ancestry-boundary
    true true true true false true
