module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER
--
-- The explicit-formula modulation route and the direct finite exponential-sum
-- route are distinct internal proof routes that meet at the same H_off consumer.
-- The old scheduler incorrectly blocked ALL finite-near evaluation behind the
-- H_X -> H_A -> H_M -> H_T modulation chain. The existing direct route does not
-- have that prerequisite.
--
-- Current direct-route dependency:
--
--   DirectFinitePoleNearProducer
--      -> SelectedDirectFiniteWeld
--          -> selected delta^2 moment -> zeta clustering
--          -> selected finite-near consumer attachment
--
-- The direct producer itself already owns targetRelativeGap and a signed
-- approximant/error receipt. PoleNearPhaseStatistic is now compiler output from
-- that producer, so constructing another phase carrier is pruned.
--
-- The explicit-formula branch remains blocked on the character/modulation/window
-- chain. Gamma remains independent. Direct proof of the clustering inequality is
-- retained as an alternative to the moment refinement.
------------------------------------------------------------------------

data RHAnalyticLeaf : Set where
  buildCanonicalComplexCharacter
  proveCanonicalTestModulationShift
  assembleCanonicalAnalyticModulationExtension
  proveTargetTranslationModulationIntertwiner
  proveWindowRestrictionResidualCompatibility
  proveExplicitFormulaFiniteNearEvaluation
  recoverDirectFinitePoleNearProducer
  weldSelectedDirectZeroCarrier
  proveSelectedTargetLocalSecondMoment
  attachDirectEvaluationToSelectedConsumer
  proveActualZetaLowGapClustering
  repairGammaPrecision
  constructSecondPhaseStatisticCarrier
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
leafState proveExplicitFormulaFiniteNearEvaluation = blocked
leafState recoverDirectFinitePoleNearProducer = open
leafState weldSelectedDirectZeroCarrier = blocked
leafState proveSelectedTargetLocalSecondMoment = blocked
leafState attachDirectEvaluationToSelectedConsumer = blocked
leafState proveActualZetaLowGapClustering = open
leafState repairGammaPrecision = open
leafState constructSecondPhaseStatisticCarrier = pruned
leafState sharpenZeroCount = pruned
leafState sharpenAbsoluteEnvelope = pruned
leafState reuseGenericExplicitFormulaWithoutWindow = pruned
leafState reuseNameOnlyHardyDonor = pruned

------------------------------------------------------------------------
-- Proof-relevant dependencies.
------------------------------------------------------------------------

data Requires : RHAnalyticLeaf → RHAnalyticLeaf → Set where
  testActionNeedsComplexCharacter :
    Requires proveCanonicalTestModulationShift buildCanonicalComplexCharacter

  modulationAssemblyNeedsComplexCharacter :
    Requires assembleCanonicalAnalyticModulationExtension buildCanonicalComplexCharacter

  modulationAssemblyNeedsTestAction :
    Requires assembleCanonicalAnalyticModulationExtension proveCanonicalTestModulationShift

  translationModulationNeedsCanonicalExtension :
    Requires proveTargetTranslationModulationIntertwiner assembleCanonicalAnalyticModulationExtension

  windowNeedsTranslationModulation :
    Requires proveWindowRestrictionResidualCompatibility proveTargetTranslationModulationIntertwiner

  explicitFiniteEvaluationNeedsWindow :
    Requires proveExplicitFormulaFiniteNearEvaluation proveWindowRestrictionResidualCompatibility

  selectedDirectWeldNeedsDirectProducer :
    Requires weldSelectedDirectZeroCarrier recoverDirectFinitePoleNearProducer

  selectedMomentNeedsSelectedDirectWeld :
    Requires proveSelectedTargetLocalSecondMoment weldSelectedDirectZeroCarrier

  selectedFiniteConsumerNeedsSelectedDirectWeld :
    Requires attachDirectEvaluationToSelectedConsumer weldSelectedDirectZeroCarrier

------------------------------------------------------------------------
-- Refinements are sufficient routes, not mandatory dependencies: direct proof of
-- the parent theorem is still allowed.
------------------------------------------------------------------------

data Refines : RHAnalyticLeaf → RHAnalyticLeaf → Set where
  selectedMomentRefinesClustering :
    Refines proveSelectedTargetLocalSecondMoment proveActualZetaLowGapClustering

------------------------------------------------------------------------
-- Currently schedulable leaves are precisely the leaves whose own prerequisites
-- are not represented as open predecessors here.
------------------------------------------------------------------------

data RHAnalyticLeafSchedulable : RHAnalyticLeaf → Set where
  complexCharacterLeafLive : RHAnalyticLeafSchedulable buildCanonicalComplexCharacter
  directFiniteProducerLeafLive : RHAnalyticLeafSchedulable recoverDirectFinitePoleNearProducer
  zetaLowGapClusteringLeafLive : RHAnalyticLeafSchedulable proveActualZetaLowGapClustering
  gammaPrecisionLeafLive : RHAnalyticLeafSchedulable repairGammaPrecision

testActionLeafNotYetSchedulable : RHAnalyticLeafSchedulable proveCanonicalTestModulationShift → ⊥
testActionLeafNotYetSchedulable ()

modulationAssemblyLeafNotYetSchedulable : RHAnalyticLeafSchedulable assembleCanonicalAnalyticModulationExtension → ⊥
modulationAssemblyLeafNotYetSchedulable ()

translationModulationLeafNotYetSchedulable : RHAnalyticLeafSchedulable proveTargetTranslationModulationIntertwiner → ⊥
translationModulationLeafNotYetSchedulable ()

windowLeafNotYetSchedulable : RHAnalyticLeafSchedulable proveWindowRestrictionResidualCompatibility → ⊥
windowLeafNotYetSchedulable ()

explicitFiniteEvaluationNotYetSchedulable : RHAnalyticLeafSchedulable proveExplicitFormulaFiniteNearEvaluation → ⊥
explicitFiniteEvaluationNotYetSchedulable ()

selectedDirectWeldNotYetSchedulable : RHAnalyticLeafSchedulable weldSelectedDirectZeroCarrier → ⊥
selectedDirectWeldNotYetSchedulable ()

selectedMomentNotYetSchedulable : RHAnalyticLeafSchedulable proveSelectedTargetLocalSecondMoment → ⊥
selectedMomentNotYetSchedulable ()

selectedFiniteConsumerNotYetSchedulable : RHAnalyticLeafSchedulable attachDirectEvaluationToSelectedConsumer → ⊥
selectedFiniteConsumerNotYetSchedulable ()

secondPhaseCarrierPruned : RHAnalyticLeafSchedulable constructSecondPhaseStatisticCarrier → ⊥
secondPhaseCarrierPruned ()

zeroCountLeafPruned : RHAnalyticLeafSchedulable sharpenZeroCount → ⊥
zeroCountLeafPruned ()

absoluteEnvelopeLeafPruned : RHAnalyticLeafSchedulable sharpenAbsoluteEnvelope → ⊥
absoluteEnvelopeLeafPruned ()

genericFormulaWithoutWindowPruned : RHAnalyticLeafSchedulable reuseGenericExplicitFormulaWithoutWindow → ⊥
genericFormulaWithoutWindowPruned ()

nameOnlyHardyLeafPruned : RHAnalyticLeafSchedulable reuseNameOnlyHardyDonor → ⊥
nameOnlyHardyLeafPruned ()

------------------------------------------------------------------------
-- Upstream receipts.
------------------------------------------------------------------------

quarterDensityComparisonPrunedUpstream :
  Gap.GapSplitRelevant Gap.compareQuarterPeriodLowerConstantWithDensityUpperConstant → ⊥
quarterDensityComparisonPrunedUpstream = Gap.quarterDensityConstantComparisonPruned

zetaUpperCountAlreadyOwned :
  Z38.zetaShortWindowUpperCountOwnedInLean Z38.canonicalZetaLocalCountLeanReturn ≡ true
zetaUpperCountAlreadyOwned = refl

actualZetaClusteringStillOpenUpstream :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringStillOpenUpstream = refl

phaseStatisticCompilerAlreadyClosed :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ true
phaseStatisticCompilerAlreadyClosed = refl

selectedDirectWeldStillOpen :
  Shared.SelectedDirectFiniteMomentBoundary.selectedDirectWeldInhabitedHere
    Shared.canonicalSelectedDirectFiniteMomentBoundary ≡ false
selectedDirectWeldStillOpen = refl

------------------------------------------------------------------------
-- Highest-alpha selection surface.
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

record RHAnalyticLeafSchedulerBoundary : Set where
  constructor rh-analytic-leaf-scheduler-boundary
  field
    complexCharacterLeafOpen : Bool
    complexCharacterLeafOpenIsTrue : complexCharacterLeafOpen ≡ true

    explicitFormulaModulationChainStillBlocked : Bool
    explicitFormulaModulationChainStillBlockedIsTrue :
      explicitFormulaModulationChainStillBlocked ≡ true

    directFiniteProducerLeafOpen : Bool
    directFiniteProducerLeafOpenIsTrue : directFiniteProducerLeafOpen ≡ true

    directFiniteProducerBlockedOnHX : Bool
    directFiniteProducerBlockedOnHXIsFalse : directFiniteProducerBlockedOnHX ≡ false

    phaseStatisticCarrierStillNeedsIndependentConstruction : Bool
    phaseStatisticCarrierStillNeedsIndependentConstructionIsFalse :
      phaseStatisticCarrierStillNeedsIndependentConstruction ≡ false

    selectedDirectWeldBlockedOnDirectProducer : Bool
    selectedDirectWeldBlockedOnDirectProducerIsTrue :
      selectedDirectWeldBlockedOnDirectProducer ≡ true

    selectedTargetMomentBlockedOnWeld : Bool
    selectedTargetMomentBlockedOnWeldIsTrue : selectedTargetMomentBlockedOnWeld ≡ true

    selectedFiniteConsumerAttachmentBlockedOnWeld : Bool
    selectedFiniteConsumerAttachmentBlockedOnWeldIsTrue :
      selectedFiniteConsumerAttachmentBlockedOnWeld ≡ true

    actualZetaLowGapClusteringLeafOpen : Bool
    actualZetaLowGapClusteringLeafOpenIsTrue : actualZetaLowGapClusteringLeafOpen ≡ true

    gammaPrecisionLeafOpen : Bool
    gammaPrecisionLeafOpenIsTrue : gammaPrecisionLeafOpen ≡ true

    countOnlyLeafActive : Bool
    countOnlyLeafActiveIsFalse : countOnlyLeafActive ≡ false

    absoluteEnvelopeLeafActive : Bool
    absoluteEnvelopeLeafActiveIsFalse : absoluteEnvelopeLeafActive ≡ false

    genericExplicitFormulaWithoutWindowActive : Bool
    genericExplicitFormulaWithoutWindowActiveIsFalse : genericExplicitFormulaWithoutWindowActive ≡ false

    nameOnlyHardyLeafActive : Bool
    nameOnlyHardyLeafActiveIsFalse : nameOnlyHardyLeafActive ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRHAnalyticLeafSchedulerBoundary : RHAnalyticLeafSchedulerBoundary
canonicalRHAnalyticLeafSchedulerBoundary =
  rh-analytic-leaf-scheduler-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
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
