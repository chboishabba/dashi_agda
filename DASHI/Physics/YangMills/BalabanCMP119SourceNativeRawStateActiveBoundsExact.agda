module DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact where

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
-- Keep the literal CMP119 scale-indexed objects separate from the theorem that
-- they satisfy the Sect.-2 inductive class.  The earlier source-native carrier
-- stored E/R/B regularity and complete-density form for every scale as fields
-- of the state itself.  That is convenient for projection, but it obscures the
-- logical role of CMP122 Theorem 1: preservation of those properties is a
-- theorem, conditional on sufficiently small active couplings.
--
-- Here the raw state contains only source objects and equation-(2.23)
-- assembly.  Sect.-2 predicates are a separate vocabulary, and an active-scale
-- witness carries their proofs only where the finite cutoff history is active.
-- This prevents all-scale RG closure from being smuggled into the data model.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History

record CMP119RawActionAlgebra
    (Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set) : Set₁ where
  field
    assemble :
      ℚ → WilsonTerm → SmallFieldTerm → RTerm → BoundaryTerm → Vacuum → Action
open CMP119RawActionAlgebra public

record CMP119SourceNativeRawState
    (Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set) : Set₁ where
  field
    terminalScale : Nat

    effectiveDensity : Nat → Density
    backgroundField : Nat → Background
    fluctuationFields : Nat → Fluctuation
    runningCoupling : Nat → ℚ

    wilsonActionTerm : Nat → WilsonTerm
    regularSmallFieldTerm : Nat → SmallFieldTerm
    rOperationTerm : Nat → RTerm
    boundaryTerm : Nat → BoundaryTerm
    vacuumEnergy : Nat → Vacuum
    effectiveAction : Nat → Action

    actionAlgebra :
      CMP119RawActionAlgebra
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum

    wilsonCoefficient : Nat → ℚ
    equation223 : ∀ scale →
      effectiveAction scale
      ≡ assemble actionAlgebra
          (wilsonCoefficient scale)
          (wilsonActionTerm scale)
          (regularSmallFieldTerm scale)
          (rOperationTerm scale)
          (boundaryTerm scale)
          (vacuumEnergy scale)

open CMP119SourceNativeRawState public

record CMP119Section2PredicateFamily
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (source : CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) : Set₁ where
  field
    ELocalizedAnalytic : Nat → SmallFieldTerm → Set
    RLocalizedAnalytic : Nat → RTerm → Set
    BLocalizedAnalytic : Nat → BoundaryTerm → Set
    RegularBackground : Nat → Background → Set
    CompleteDensityForm : Nat → Density → Set

open CMP119Section2PredicateFamily public

record CMP119Section2AtScale
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source : CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (predicates : CMP119Section2PredicateFamily source)
    (scale : Nat) : Set where
  field
    eSector :
      ELocalizedAnalytic predicates scale (regularSmallFieldTerm source scale)
    rSector :
      RLocalizedAnalytic predicates scale (rOperationTerm source scale)
    bSector :
      BLocalizedAnalytic predicates scale (boundaryTerm source scale)
    regularBackground :
      RegularBackground predicates scale (backgroundField source scale)
    completeDensityForm :
      CompleteDensityForm predicates scale (effectiveDensity source scale)

open CMP119Section2AtScale public

record ActiveCMP119Section2Witness
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source : CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (predicates : CMP119Section2PredicateFamily source) : Set₁ where
  field
    couplingIsHistoryCoupling : ∀ scale →
      History.ActiveScale history scale →
      runningCoupling source scale ≡ History.couplingAt history scale

    section2OnActiveScale : ∀ scale →
      History.ActiveScale history scale →
      CMP119Section2AtScale predicates scale

open ActiveCMP119Section2Witness public

activeSourceCouplingPositive :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum source predicates}
    (witness : ActiveCMP119Section2Witness
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background}
      {Fluctuation = Fluctuation} {Action = Action}
      {WilsonTerm = WilsonTerm} {SmallFieldTerm = SmallFieldTerm}
      {RTerm = RTerm} {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {source = source} predicates)
    scale → History.ActiveScale history scale →
  Data.Rational.Base.Positive (runningCoupling source scale)
activeSourceCouplingPositive {history = history} {source = source}
    witness scale active
  rewrite couplingIsHistoryCoupling witness scale active =
  History.couplingPositive history scale

activeSourceCouplingSmall :
  ∀ {trajectory Mode Atom betaData history
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum source predicates}
    (witness : ActiveCMP119Section2Witness
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      {Density = Density} {Background = Background}
      {Fluctuation = Fluctuation} {Action = Action}
      {WilsonTerm = WilsonTerm} {SmallFieldTerm = SmallFieldTerm}
      {RTerm = RTerm} {BoundaryTerm = BoundaryTerm} {Vacuum = Vacuum}
      {source = source} predicates)
    scale → History.ActiveScale history scale →
  runningCoupling source scale ≤ History.gamma history
activeSourceCouplingSmall {history = history} {source = source}
    witness scale active
  rewrite couplingIsHistoryCoupling witness scale active =
  History.finiteModeSmallCouplingAtActiveScale history scale active

cmp119RawStateDoesNotAssumeSection2Level : ProofLevel
cmp119RawStateDoesNotAssumeSection2Level = machineChecked

cmp119ActiveSection2WitnessLevel : ProofLevel
cmp119ActiveSection2WitnessLevel = machineChecked

cmp119ActiveCouplingTransportLevel : ProofLevel
cmp119ActiveCouplingTransportLevel = machineChecked

-- Physical/source frontier: instantiate the raw CMP119 objects and obtain the
-- `section2OnActiveScale` witness from the published CMP122 Theorem 1 on the
-- same finite history.  The target theorem is no longer stored inside the raw
-- state itself.
cmp122Theorem1ToActiveRawSourceStateLevel : ProofLevel
cmp122Theorem1ToActiveRawSourceStateLevel = conditional
