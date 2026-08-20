module DASHI.Physics.YangMills.BalabanCMP122Theorem1ToRawCMP119ActiveExact where

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
-- Specialize the existing active-scale carrier for CMP122 Theorem 1 directly
-- to the SAME raw CMP119 source state introduced in Round58.  The source
-- theorem's abstract predicates are instantiated as:
--
--   InSection2DensityClass   = literal CompleteDensityForm,
--   Section2Conditions...   = literal E/R/B/background sector bounds.
--
-- Hence a published-Theorem-1 witness constructs `CMP119Section2AtScale` on
-- every active scale.  The only independent same-object datum retained here is
-- that the raw state's running coupling is the coupling in the finite beta
-- history; no Section-2 preservation theorem is stored in the raw state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteBeta
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989ActiveScaleTheorem1BetaBridgeExact as Theorem1
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

record SectorBoundsAtScale
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (predicates : Raw.CMP119Section2PredicateFamily source)
    (scale : Nat) : Set where
  field
    eSector :
      Raw.ELocalizedAnalytic predicates scale
        (Raw.regularSmallFieldTerm source scale)
    rSector :
      Raw.RLocalizedAnalytic predicates scale
        (Raw.rOperationTerm source scale)
    bSector :
      Raw.BLocalizedAnalytic predicates scale
        (Raw.boundaryTerm source scale)
    regularBackground :
      Raw.RegularBackground predicates scale
        (Raw.backgroundField source scale)

open SectorBoundsAtScale public

asActiveEffectiveDensityFlow :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum} →
  Raw.CMP119Section2PredicateFamily source →
  Theorem1.ActiveEffectiveDensityFlow
    trajectory Mode Atom Density betaData history
asActiveEffectiveDensityFlow {source = source} predicates = record
  { Theorem1.ActiveEffectiveDensityFlow.densityAt =
      Raw.effectiveDensity source
  ; Theorem1.ActiveEffectiveDensityFlow.InSection2DensityClass =
      λ scale density → Raw.CompleteDensityForm predicates scale density
  ; Theorem1.ActiveEffectiveDensityFlow.Section2ConditionsAndBounds =
      λ scale density → SectorBoundsAtScale predicates scale
  }

section2AtScaleFromTheorem1 :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily source}
    (theorem1 : Theorem1.ActiveBalaban1989Theorem1Witness
      (asActiveEffectiveDensityFlow
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {betaData = betaData} {history = history}
        predicates))
    scale → History.ActiveScale history scale →
  Raw.CMP119Section2AtScale predicates scale
section2AtScaleFromTheorem1 theorem1 scale active =
  let
    sectorBounds =
      Theorem1.effectiveDensitiesSatisfySection2Bounds theorem1 scale active
    densityForm =
      Theorem1.effectiveDensitiesPreserveSection2Form theorem1 scale active
  in
  record
    { Raw.CMP119Section2AtScale.eSector = eSector sectorBounds
    ; Raw.CMP119Section2AtScale.rSector = rSector sectorBounds
    ; Raw.CMP119Section2AtScale.bSector = bSector sectorBounds
    ; Raw.CMP119Section2AtScale.regularBackground =
        regularBackground sectorBounds
    ; Raw.CMP119Section2AtScale.completeDensityForm = densityForm
    }

activeRawCMP119WitnessFromTheorem1 :
  ∀ {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData : FiniteBeta.FiniteModeBetaTrajectoryData trajectory Mode Atom}
    {history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData}
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    {source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {predicates : Raw.CMP119Section2PredicateFamily source} →
  (couplingIsHistoryCoupling : ∀ scale →
    History.ActiveScale history scale →
    Raw.runningCoupling source scale ≡ History.couplingAt history scale) →
  Theorem1.ActiveBalaban1989Theorem1Witness
    (asActiveEffectiveDensityFlow
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {betaData = betaData} {history = history}
      predicates) →
  Raw.ActiveCMP119Section2Witness
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {betaData = betaData} {history = history}
    {source = source} predicates
activeRawCMP119WitnessFromTheorem1 couplingSame theorem1 = record
  { Raw.ActiveCMP119Section2Witness.couplingIsHistoryCoupling = couplingSame
  ; Raw.ActiveCMP119Section2Witness.section2OnActiveScale =
      section2AtScaleFromTheorem1 theorem1
  }

cmp122Theorem1SpecializedToRawCMP119Level : ProofLevel
cmp122Theorem1SpecializedToRawCMP119Level = machineChecked

cmp122Theorem1ProducesActiveSection2Level : ProofLevel
cmp122Theorem1ProducesActiveSection2Level = machineChecked

-- Remaining same-object/source leaf on this route: instantiate `source` from
-- the literal CMP119 effective-density construction and identify its running
-- coupling with the already-existing finite beta trajectory.  Once that
-- equality is available, the published CMP122 theorem supplies all active
-- Section-2 predicates through the theorem above.
cmp119RawStateCouplingIdentityLevel : ProofLevel
cmp119RawStateCouplingIdentityLevel = conditional
