module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER — ACTUAL CARRIER CUT
--
-- Forward audit of the canonical Riemann substrate showed that it does not yet
-- expose complex exponential / target modulation / transform-shift structure.
-- Therefore the shared H_T leaf itself has a first unpaid producer H_M:
--
--   H_M       canonical analytic modulation extension on existing carriers
--   H_T       target translation <-> dual modulation intertwiner
--   H_W       window/restriction compatibility + cluster/near/far residual
--   H_E       phase-sensitive finite near evaluation
--   H_Gamma   Gamma precision repair
--
-- Dependency shape:
--
--   H_M -> H_T -> direct phase statistic -> H_E
--             \-> H_W -> explicit-formula target window -> H_E
--   H_Gamma ----------------------------------------------> final consumer
------------------------------------------------------------------------

data RHAnalyticLeaf : Set where
  buildCanonicalAnalyticModulationExtension
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
leafState buildCanonicalAnalyticModulationExtension = open
leafState proveTargetTranslationModulationIntertwiner = blocked
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
  translationModulationNeedsCanonicalExtension :
    Requires
      proveTargetTranslationModulationIntertwiner
      buildCanonicalAnalyticModulationExtension

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
------------------------------------------------------------------------

data RHAnalyticLeafSchedulable : RHAnalyticLeaf → Set where
  canonicalModulationExtensionLeafLive :
    RHAnalyticLeafSchedulable buildCanonicalAnalyticModulationExtension
  gammaPrecisionLeafLive :
    RHAnalyticLeafSchedulable repairGammaPrecision

translationModulationLeafNotYetSchedulable :
  RHAnalyticLeafSchedulable proveTargetTranslationModulationIntertwiner → ⊥
translationModulationLeafNotYetSchedulable ()

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

record RHAnalyticLeafSchedulerBoundary : Set where
  constructor rh-analytic-leaf-scheduler-boundary
  field
    canonicalModulationExtensionOpen : Bool
    canonicalModulationExtensionOpenIsTrue : canonicalModulationExtensionOpen ≡ true

    translationModulationLeafBlockedOnExtension : Bool
    translationModulationLeafBlockedOnExtensionIsTrue :
      translationModulationLeafBlockedOnExtension ≡ true

    windowRestrictionLeafBlockedOnHT : Bool
    windowRestrictionLeafBlockedOnHTIsTrue : windowRestrictionLeafBlockedOnHT ≡ true

    finiteEvaluationLeafBlockedOnSharedStructure : Bool
    finiteEvaluationLeafBlockedOnSharedStructureIsTrue :
      finiteEvaluationLeafBlockedOnSharedStructure ≡ true

    gammaPrecisionLeafOpen : Bool
    gammaPrecisionLeafOpenIsTrue : gammaPrecisionLeafOpen ≡ true

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
