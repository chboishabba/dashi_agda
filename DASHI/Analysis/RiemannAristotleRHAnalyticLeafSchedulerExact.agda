module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER — MONSTER-XPOLLENATED BIDI CUT
--
-- The direct phase-statistic and explicit-formula routes share an earlier
-- prerequisite than previously represented:
--
--   H_T       target translation <-> dual modulation intertwiner
--   H_W       window/restriction compatibility + cluster/near/far residual
--   H_E       phase-sensitive finite near evaluation
--   H_Gamma   Gamma precision repair
--
-- Dependency shape:
--
--   H_T -> direct phase statistic -> H_E
--   H_T -> H_W -> explicit-formula target window -> H_E
--   H_Gamma ---------------------------------------> final complement consumer
--
-- H_W and H_E may be developed conditionally, but cannot be promoted as closed
-- producers before their prerequisites are inhabited.
------------------------------------------------------------------------

data RHAnalyticLeaf : Set where
  proveTargetTranslationModulationIntertwiner
  proveWindowRestrictionResidualCompatibility
  provePhaseSensitiveFiniteNearEvaluation
  repairGammaPrecision
  sharpenZeroCount
  sharpenAbsoluteEnvelope
  reuseGenericExplicitFormulaWithoutWindow
  reuseNameOnlyHardyDonor
  : RHAnalyticLeaf

data LeafState : Set where
  closed open blocked pruned : LeafState

leafState : RHAnalyticLeaf → LeafState
leafState proveTargetTranslationModulationIntertwiner = open
leafState proveWindowRestrictionResidualCompatibility = blocked
leafState provePhaseSensitiveFiniteNearEvaluation = blocked
leafState repairGammaPrecision = open
leafState sharpenZeroCount = pruned
leafState sharpenAbsoluteEnvelope = pruned
leafState reuseGenericExplicitFormulaWithoutWindow = pruned
leafState reuseNameOnlyHardyDonor = pruned

------------------------------------------------------------------------
-- Proof-relevant dependency relation.
------------------------------------------------------------------------

data Requires : RHAnalyticLeaf → RHAnalyticLeaf → Set where
  windowNeedsTranslationModulation :
    Requires
      proveWindowRestrictionResidualCompatibility
      proveTargetTranslationModulationIntertwiner

  evaluationNeedsTranslationModulation :
    Requires
      provePhaseSensitiveFiniteNearEvaluation
      proveTargetTranslationModulationIntertwiner

  evaluationExplicitFormulaBranchNeedsWindow :
    Requires
      provePhaseSensitiveFiniteNearEvaluation
      proveWindowRestrictionResidualCompatibility

------------------------------------------------------------------------
-- Current genuinely schedulable producer leaves.
--
-- A blocked leaf may have its conditional interface developed, but cannot win
-- the proof-search selector as though its prerequisites were already owned.
------------------------------------------------------------------------

data RHAnalyticLeafSchedulable : RHAnalyticLeaf → Set where
  targetTranslationModulationLeafLive :
    RHAnalyticLeafSchedulable proveTargetTranslationModulationIntertwiner
  gammaPrecisionLeafLive :
    RHAnalyticLeafSchedulable repairGammaPrecision

windowLeafNotYetSchedulable :
  RHAnalyticLeafSchedulable proveWindowRestrictionResidualCompatibility → ⊥
windowLeafNotYetSchedulable ()

evaluationLeafNotYetSchedulable :
  RHAnalyticLeafSchedulable provePhaseSensitiveFiniteNearEvaluation → ⊥
evaluationLeafNotYetSchedulable ()

zeroCountLeafPruned : RHAnalyticLeafSchedulable sharpenZeroCount → ⊥
zeroCountLeafPruned ()

absoluteEnvelopeLeafPruned : RHAnalyticLeafSchedulable sharpenAbsoluteEnvelope → ⊥
absoluteEnvelopeLeafPruned ()

genericFormulaWithoutWindowPruned :
  RHAnalyticLeafSchedulable reuseGenericExplicitFormulaWithoutWindow → ⊥
genericFormulaWithoutWindowPruned ()

nameOnlyHardyLeafPruned :
  RHAnalyticLeafSchedulable reuseNameOnlyHardyDonor → ⊥
nameOnlyHardyLeafPruned ()

------------------------------------------------------------------------
-- Cost/order only among live leaves.
------------------------------------------------------------------------

record RHAnalyticLeafCostSurface : Set₁ where
  constructor rh-analytic-leaf-cost-surface
  field
    cost : RHAnalyticLeaf → Nat
    Declared : RHAnalyticLeaf → Set
    costReference : String

open RHAnalyticLeafCostSurface public

record SelectedRHAnalyticLeaf (surface : RHAnalyticLeafCostSurface) : Set₁ where
  constructor selected-rh-analytic-leaf
  field
    selected : RHAnalyticLeaf
    selectedDeclared : Declared surface selected
    selectedSchedulable : RHAnalyticLeafSchedulable selected
    minimalAmongDeclaredLive :
      (alternative : RHAnalyticLeaf) →
      Declared surface alternative →
      RHAnalyticLeafSchedulable alternative →
      cost surface selected ≤ cost surface alternative
    selectionReference : String

open SelectedRHAnalyticLeaf public

------------------------------------------------------------------------
-- Regression boundary.
------------------------------------------------------------------------

record RHAnalyticLeafSchedulerBoundary : Set where
  constructor rh-analytic-leaf-scheduler-boundary
  field
    translationModulationLeafOpen : Bool
    translationModulationLeafOpenIsTrue : translationModulationLeafOpen ≡ true

    windowRestrictionLeafBlockedOnHT : Bool
    windowRestrictionLeafBlockedOnHTIsTrue : windowRestrictionLeafBlockedOnHT ≡ true

    finiteEvaluationLeafBlockedOnSharedStructure : Bool
    finiteEvaluationLeafBlockedOnSharedStructureIsTrue :
      finiteEvaluationLeafBlockedOnSharedStructure ≡ true

    gammaPrecisionLeafOpen : Bool
    gammaPrecisionLeafOpenIsTrue : gammaPrecisionLeafOpen ≡ true

    directAndExplicitFormulaRoutesMeetBeforeEvaluation : Bool
    directAndExplicitFormulaRoutesMeetBeforeEvaluationIsTrue :
      directAndExplicitFormulaRoutesMeetBeforeEvaluation ≡ true

    countOnlyLeafActive : Bool
    countOnlyLeafActiveIsFalse : countOnlyLeafActive ≡ false

    absoluteEnvelopeLeafActive : Bool
    absoluteEnvelopeLeafActiveIsFalse : absoluteEnvelopeLeafActive ≡ false

    genericExplicitFormulaWithoutWindowActive : Bool
    genericExplicitFormulaWithoutWindowActiveIsFalse :
      genericExplicitFormulaWithoutWindowActive ≡ false

    nameOnlyHardyLeafActive : Bool
    nameOnlyHardyLeafActiveIsFalse : nameOnlyHardyLeafActive ≡ false

    monsterRepresentationAuthorityImportedIntoRH : Bool
    monsterRepresentationAuthorityImportedIntoRHIsFalse :
      monsterRepresentationAuthorityImportedIntoRH ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRHAnalyticLeafSchedulerBoundary : RHAnalyticLeafSchedulerBoundary
canonicalRHAnalyticLeafSchedulerBoundary =
  rh-analytic-leaf-scheduler-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
