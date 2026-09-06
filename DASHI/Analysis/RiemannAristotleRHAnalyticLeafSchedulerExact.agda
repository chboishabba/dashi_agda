module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER — CHARACTER/ACTION + GAP-SPLIT CUT
--
-- The canonical carrier audit split the old H_M modulation leaf into H_X/H_A/
-- H_M/H_T/H_W/H_E, with H_Gamma independent.  The later 8894->8896 gap-split
-- return adds one independent zero-side leaf: actual-zeta low-gap clustering.
--
-- §37 closes the adaptive J*Lambda constant comparison and §38 closes zeta's
-- upper local count, so neither is scheduled here.  The clustering theorem is
-- not implied by those closures and is therefore a genuine schedulable leaf.
------------------------------------------------------------------------

data RHAnalyticLeaf : Set where
  buildCanonicalComplexCharacter
  proveCanonicalTestModulationShift
  assembleCanonicalAnalyticModulationExtension
  proveTargetTranslationModulationIntertwiner
  proveWindowRestrictionResidualCompatibility
  provePhaseSensitiveFiniteNearEvaluation
  proveActualZetaLowGapClustering
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
leafState proveActualZetaLowGapClustering = open
leafState repairGammaPrecision = open
leafState sharpenZeroCount = pruned
leafState sharpenAbsoluteEnvelope = pruned
leafState reuseGenericExplicitFormulaWithoutWindow = pruned
leafState reuseNameOnlyHardyDonor = pruned

------------------------------------------------------------------------
-- Proof-relevant dependency relation for the modulation/evaluation route.
-- Actual-zeta clustering is an independent producer for the optimized gap-split
-- route, so it has no fabricated H_X/H_A prerequisite here.
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
  zetaLowGapClusteringLeafLive :
    RHAnalyticLeafSchedulable proveActualZetaLowGapClustering
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

quarterDensityComparisonPrunedUpstream :
  Gap.GapSplitRelevant Gap.compareQuarterPeriodLowerConstantWithDensityUpperConstant
  → ⊥
quarterDensityComparisonPrunedUpstream = Gap.quarterDensityConstantComparisonPruned

zetaUpperCountAlreadyOwned :
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn
  ≡ true
zetaUpperCountAlreadyOwned = refl

actualZetaClusteringStillOpenUpstream :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringStillOpenUpstream = refl

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

    actualZetaLowGapClusteringLeafOpen : Bool
    actualZetaLowGapClusteringLeafOpenIsTrue :
      actualZetaLowGapClusteringLeafOpen ≡ true

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
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
