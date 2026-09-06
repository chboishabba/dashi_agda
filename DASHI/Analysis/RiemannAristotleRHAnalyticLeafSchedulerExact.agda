module DASHI.Analysis.RiemannAristotleRHAnalyticLeafSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2GapSplitClusteringLeanReturn8894Exact as Gap
import DASHI.Analysis.RiemannAristotleZetaLocalCountLeanReturnExact as Z38
import DASHI.Analysis.RiemannAristotlePoleNearPhaseStatisticExact as Phase
import DASHI.Analysis.RiemannAristotlePoleQuotientDirectFiniteNearAttackExact as Direct
import DASHI.Analysis.RiemannG2SelectedDirectFiniteMomentBidiExact as Shared

------------------------------------------------------------------------
-- RECURSIVE RH ANALYTIC LEAF SCHEDULER
--
-- The explicit-formula modulation route and the direct finite signed route are
-- distinct proof routes meeting the same H_off/G2d consumer.
--
-- CORRECTION: §35 clustering is not a forward RH producer. It is necessary for
-- positivity of a gap-split lower bound used in a NO-GO against the desired
-- small signed scalar estimate. The optional M2_delta refinement is therefore
-- also diagnostic, not a schedulable RH leaf.
--
-- The direct route now starts at a consumer-sufficient DirectFinitePoleNearProducer.
-- That producer must carry DirectSignedConsumerPayment on the canonical literal
-- G2 scalar problem. PoleNearPhaseStatistic and the canonical evaluation surface
-- are compiler output from it. Selected-window weld/budget transport is downstream.
--
-- The explicit-formula route remains independently blocked on its H_X/H_A/H_M/H_T
-- chain. Gamma remains independent.
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
leafState proveSelectedTargetLocalSecondMoment = pruned
leafState attachDirectEvaluationToSelectedConsumer = blocked
leafState proveActualZetaLowGapClustering = pruned
leafState repairGammaPrecision = open
leafState constructSecondPhaseStatisticCarrier = pruned
leafState sharpenZeroCount = pruned
leafState sharpenAbsoluteEnvelope = pruned
leafState reuseGenericExplicitFormulaWithoutWindow = pruned
leafState reuseNameOnlyHardyDonor = pruned

------------------------------------------------------------------------
-- Proof-relevant forward dependencies.
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

  selectedFiniteConsumerNeedsSelectedDirectWeld :
    Requires attachDirectEvaluationToSelectedConsumer weldSelectedDirectZeroCarrier

------------------------------------------------------------------------
-- Diagnostic relation outside the forward RH dependency chain.
------------------------------------------------------------------------

data GapSplitDiagnosticRefines : RHAnalyticLeaf → RHAnalyticLeaf → Set where
  selectedMomentRefinesClusteringDiagnostic :
    GapSplitDiagnosticRefines
      proveSelectedTargetLocalSecondMoment
      proveActualZetaLowGapClustering

------------------------------------------------------------------------
-- Currently schedulable forward leaves.
------------------------------------------------------------------------

data RHAnalyticLeafSchedulable : RHAnalyticLeaf → Set where
  complexCharacterLeafLive : RHAnalyticLeafSchedulable buildCanonicalComplexCharacter
  directFiniteProducerLeafLive : RHAnalyticLeafSchedulable recoverDirectFinitePoleNearProducer
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

selectedMomentDiagnosticNotRHSchedulable :
  RHAnalyticLeafSchedulable proveSelectedTargetLocalSecondMoment → ⊥
selectedMomentDiagnosticNotRHSchedulable ()

selectedFiniteConsumerNotYetSchedulable : RHAnalyticLeafSchedulable attachDirectEvaluationToSelectedConsumer → ⊥
selectedFiniteConsumerNotYetSchedulable ()

zetaClusteringDiagnosticNotRHSchedulable :
  RHAnalyticLeafSchedulable proveActualZetaLowGapClustering → ⊥
zetaClusteringDiagnosticNotRHSchedulable ()

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

actualZetaClusteringStillUnprovedButDiagnostic :
  Z38.actualZetaClusteringClosed Z38.canonicalZetaLocalCountLeanReturn ≡ false
actualZetaClusteringStillUnprovedButDiagnostic = refl

clusteringDoesNotDirectlyPayRH :
  Gap.clusteringDirectlyPaysRHScalarConsumer
    Gap.canonicalGapSplitClusteringLeanReturn8894 ≡ false
clusteringDoesNotDirectlyPayRH = Gap.clusteringDoesNotDirectlyPayRH

phaseStatisticCompilerAlreadyClosed :
  Phase.PoleNearPhaseStatisticBoundary.repositoryAlreadyOwnsConcretePoleNearPhaseStatistic
    Phase.canonicalPoleNearPhaseStatisticBoundary ≡ true
phaseStatisticCompilerAlreadyClosed = refl

directProducerCarriesExactConsumerPayment :
  Direct.DirectFiniteNearAttackBoundary.directProducerCarriesCanonicalConsumerPayment
    Direct.canonicalDirectFiniteNearAttackBoundary ≡ true
directProducerCarriesExactConsumerPayment = refl

selectedDirectWeldStillDownstream :
  Shared.paymentState Shared.weldExistingDirectProducerToSelectedWindow ≡ Shared.downstream
selectedDirectWeldStillDownstream = refl

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

    directProducerCarriesCanonicalConsumerPayment : Bool
    directProducerCarriesCanonicalConsumerPaymentIsTrue :
      directProducerCarriesCanonicalConsumerPayment ≡ true

    phaseStatisticCarrierStillNeedsIndependentConstruction : Bool
    phaseStatisticCarrierStillNeedsIndependentConstructionIsFalse :
      phaseStatisticCarrierStillNeedsIndependentConstruction ≡ false

    selectedDirectWeldBlockedOnDirectProducer : Bool
    selectedDirectWeldBlockedOnDirectProducerIsTrue :
      selectedDirectWeldBlockedOnDirectProducer ≡ true

    selectedFiniteConsumerAttachmentBlockedOnWeld : Bool
    selectedFiniteConsumerAttachmentBlockedOnWeldIsTrue :
      selectedFiniteConsumerAttachmentBlockedOnWeld ≡ true

    actualZetaLowGapClusteringLeafOpen : Bool
    actualZetaLowGapClusteringLeafOpenIsFalse :
      actualZetaLowGapClusteringLeafOpen ≡ false

    clusteringRetainedAsGapSplitDiagnostic : Bool
    clusteringRetainedAsGapSplitDiagnosticIsTrue :
      clusteringRetainedAsGapSplitDiagnostic ≡ true

    targetLocalMomentIsForwardRHLeaf : Bool
    targetLocalMomentIsForwardRHLeafIsFalse :
      targetLocalMomentIsForwardRHLeaf ≡ false

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

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

canonicalRHAnalyticLeafSchedulerBoundary : RHAnalyticLeafSchedulerBoundary
canonicalRHAnalyticLeafSchedulerBoundary =
  rh-analytic-leaf-scheduler-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
