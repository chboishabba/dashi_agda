module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER — CHARACTER/ACTION CUT
--
-- The canonical carrier audit split the old H_M modulation leaf into:
--
--   H_X       canonical complex character algebra
--             exp(-itu) exp(ibu) = exp(i(b-t)u), even part = cosine
--   H_A       action of that character on the canonical Weil/Mellin test
--             carrier + admissibility + spectral shift for the SAME formula
--   H_M       assembled canonical analytic modulation extension
--   H_T       target translation <-> modulation intertwiner
--   H_W       window/restriction + cluster/near/far residual
--   H_E       phase-sensitive finite near evaluation
--   H_Gamma   Gamma precision repair
--
-- Dependency shape:
--
--   H_X -> H_A -> H_M -> H_T -> direct phase statistic -> H_E
--                    \             \-> H_W -> explicit window -> H_E
--   H_Gamma ------------------------------------------------> final consumer
------------------------------------------------------------------------

data RHAnalyticLeaf : Set where
  buildCanonicalComplexCharacter
  proveCanonicalTestModulationShift
  assembleCanonicalAnalyticModulationExtension
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
leafState buildCanonicalComplexCharacter = open
leafState proveCanonicalTestModulationShift = blocked
leafState assembleCanonicalAnalyticModulationExtension = blocked
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
  testActionNeedsComplexCharacter :
    Requires proveCanonicalTestModulationShift buildCanonicalComplexCharacter

  modulationAssemblyNeedsComplexCharacter :
    Requires assembleCanonicalAnalyticModulationExtension buildCanonicalComplexCharacter

  modulationAssemblyNeedsTestAction :
    Requires assembleCanonicalAnalyticModulationExtension proveCanonicalTestModulationShift

  translationModulationNeedsCanonicalExtension :
    Requires
      proveTargetTranslationModulationIntertwiner
      assembleCanonicalAnalyticModulationExtension

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
  complexCharacterLeafLive :
    RHAnalyticLeafSchedulable buildCanonicalComplexCharacter
  gammaPrecisionLeafLive :
    RHAnalyticLeafSchedulable repairGammaPrecision

testActionLeafNotYetSchedulable :
  RHAnalyticLeafSchedulable proveCanonicalTestModulationShift → ⊥
testActionLeafNotYetSchedulable ()

modulationAssemblyLeafNotYetSchedulable :
  RHAnalyticLeafSchedulable assembleCanonicalAnalyticModulationExtension → ⊥
modulationAssemblyLeafNotYetSchedulable ()

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
    complexCharacterLeafOpen : Bool
    complexCharacterLeafOpenIsTrue : complexCharacterLeafOpen ≡ true

    testModulationActionBlockedOnHX : Bool
    testModulationActionBlockedOnHXIsTrue :
      testModulationActionBlockedOnHX ≡ true

    modulationAssemblyBlockedOnHXAndHA : Bool
    modulationAssemblyBlockedOnHXAndHAIsTrue :
      modulationAssemblyBlockedOnHXAndHA ≡ true

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

    characterLawExcludesPoleCoshTaperFactor : Bool
    characterLawExcludesPoleCoshTaperFactorIsTrue :
      characterLawExcludesPoleCoshTaperFactor ≡ true

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
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
