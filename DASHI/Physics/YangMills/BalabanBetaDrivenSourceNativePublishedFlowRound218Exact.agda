{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBetaDrivenSourceNativePublishedFlowRound218Exact where

------------------------------------------------------------------------
-- ROUND218 / BETA-DRIVEN SOURCE-NATIVE PUBLISHED FLOW
--
-- The current source frontier does not need to rebuild a second raw CMP119
-- family if the already-existing `SourceNativePublishedFlow` is instantiated
-- directly on the beta-driven complete-density flow.
--
-- `betaDrivenCompleteDensityFlow inputs` already has
--
--   Coupling = ℚ
--   couplingAt k = History.couplingAt (betaHistory inputs) k
--   densityAt  k = Flow.densityAt inputs k
--
-- definitionally.  This module packages a scale-indexed literal CMP119
-- complete-density family on that SAME flow and compiles it to the older
-- source-native published-flow authority.  No parallel RG trajectory and no
-- post-hoc source-coupling transport are introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Published
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact as Native
import DASHI.Physics.YangMills.BalabanSourceNativePublishedFlowEntryExact as Entry

record BetaDrivenSourceNativePublishedFlowInputs
    {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₂ where
  field
    Operation Action Field : Set
    RegularTerm RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    theorem1 :
      Published.Balaban1989Theorem1Witness
        (Beta.betaDrivenCompleteDensityFlow inputs)

    completeDensityAt : Nat →
      CMP119.CMP119Section2CompleteDensity
        ℚ (Beta.Density inputs) Operation Action Field
        RegularTerm RTerm BoundaryTerm VacuumTerm
        SmallFieldScale BlockRadius AnalyticRadius Decay

    -- These are source-family identity receipts only.  The right-hand sides are
    -- already the beta-driven flow coordinates by definition.
    densityIsBetaDensity : ∀ scale →
      CMP119.rho (completeDensityAt scale)
      ≡ Beta.densityAt inputs scale

    couplingIsBetaHistory : ∀ scale →
      CMP119.g (completeDensityAt scale)
      ≡ History.couplingAt (Beta.betaHistory inputs) scale

    differentiatedAt : Nat → Native.CMP109DifferentiatedCoordinate RegularTerm

open BetaDrivenSourceNativePublishedFlowInputs public

asSourceNativePublishedFlow :
  ∀ {trajectory split inputs} →
  BetaDrivenSourceNativePublishedFlowInputs
    {trajectory = trajectory} {split = split} inputs →
  Entry.SourceNativePublishedFlow
asSourceNativePublishedFlow {inputs = inputs} dataSet = record
  { Entry.SourceNativePublishedFlow.Coupling = ℚ
  ; Entry.SourceNativePublishedFlow.Density = Beta.Density inputs
  ; Entry.SourceNativePublishedFlow.Operation = Operation dataSet
  ; Entry.SourceNativePublishedFlow.Action = Action dataSet
  ; Entry.SourceNativePublishedFlow.Field = Field dataSet
  ; Entry.SourceNativePublishedFlow.RegularTerm = RegularTerm dataSet
  ; Entry.SourceNativePublishedFlow.RTerm = RTerm dataSet
  ; Entry.SourceNativePublishedFlow.BoundaryTerm = BoundaryTerm dataSet
  ; Entry.SourceNativePublishedFlow.VacuumTerm = VacuumTerm dataSet
  ; Entry.SourceNativePublishedFlow.SmallFieldScale = SmallFieldScale dataSet
  ; Entry.SourceNativePublishedFlow.BlockRadius = BlockRadius dataSet
  ; Entry.SourceNativePublishedFlow.AnalyticRadius = AnalyticRadius dataSet
  ; Entry.SourceNativePublishedFlow.Decay = Decay dataSet
  ; Entry.SourceNativePublishedFlow.flow = Beta.betaDrivenCompleteDensityFlow inputs
  ; Entry.SourceNativePublishedFlow.theorem1 = theorem1 dataSet
  ; Entry.SourceNativePublishedFlow.completeDensityAt = completeDensityAt dataSet
  ; Entry.SourceNativePublishedFlow.densityIsFlowDensity = densityIsBetaDensity dataSet
  ; Entry.SourceNativePublishedFlow.couplingIsFlowCoupling = couplingIsBetaHistory dataSet
  ; Entry.SourceNativePublishedFlow.differentiatedAt = differentiatedAt dataSet
  }

sourceNativeFlowCouplingIsBetaHistory :
  ∀ {trajectory split inputs}
    (dataSet : BetaDrivenSourceNativePublishedFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  Published.couplingAt (Entry.flow (asSourceNativePublishedFlow dataSet)) scale
  ≡ History.couplingAt (Beta.betaHistory inputs) scale
sourceNativeFlowCouplingIsBetaHistory {inputs = inputs} dataSet scale =
  Beta.sourceCouplingIsBetaHistoryCoupling inputs scale

sourceNativeFlowDensityIsBetaDensity :
  ∀ {trajectory split inputs}
    (dataSet : BetaDrivenSourceNativePublishedFlowInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  Published.densityAt (Entry.flow (asSourceNativePublishedFlow dataSet)) scale
  ≡ Beta.densityAt inputs scale
sourceNativeFlowDensityIsBetaDensity dataSet scale = Agda.Builtin.Equality.refl

betaDrivenSourceNativePublishedFlowCompilerLevel : ProofLevel
betaDrivenSourceNativePublishedFlowCompilerLevel = machineChecked

betaDrivenPublishedCouplingSameObjectLevel : ProofLevel
betaDrivenPublishedCouplingSameObjectLevel = machineChecked

-- Remaining source realization on this preferred owner: instantiate the literal
-- scale-indexed CMP119 complete-density family, its identity with the beta-driven
-- density sequence, and the CMP109 differentiated regular-E coordinate.  No
-- independent raw-state or running-coupling construction is required.
literalBetaDrivenSourceNativePublishedFlowInputsLevel : ProofLevel
literalBetaDrivenSourceNativePublishedFlowInputsLevel = conditional
