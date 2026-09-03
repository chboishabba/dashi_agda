module DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2FkOrbitExplicitFormulaWeldExact as Weld
import DASHI.Analysis.RiemannG2FkSelectedTestSameObjectBidiExact as Same

------------------------------------------------------------------------
-- SELECTED POLE-NEAR SINGLE-PRODUCER BIDI CUT
--
-- Cross-pollination from PR #691 (single dependent H_A source producer) and
-- PR #684 (same-object premises compile an apparently separate leaf): the RH
-- target-window lane should not search independently for
--
--   * a selected source-orbit attachment,
--   * a PoleNearTargetWindow decomposition,
--   * a second same-test weld,
--   * a second selected near/far explicit-formula object.
--
-- The scientifically meaningful object is one dependent producer containing
-- the selected source attachment and one theorem-bearing PoleNearTargetWindow,
-- indexed by the SAME space/formula, together with equality of their selected
-- test.  Once that object exists, the downstream same-object and near/far welds
-- are compiler output.
------------------------------------------------------------------------

record ActualSelectedPoleNearProducer
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit) : Set₁ where
  field
    attachment : Orbit.FkOrbitConsumerAttachment space formula orbit
    targetWindow : Window.PoleNearTargetWindow space formula

    sameSelectedTest :
      Window.PoleNearTargetWindow.targetWindowTest targetWindow
      ≡ Orbit.FkOrbitConsumerAttachment.selectedPoleTest attachment

    poleTaperPreservedWitness :
      Window.PoleNearTargetWindow.poleTaperPreserved targetWindow
    targetRelativePhasePreservedWitness :
      Window.PoleNearTargetWindow.targetRelativePhasePreserved targetWindow
    multiplicitiesPreservedWitness :
      Window.PoleNearTargetWindow.multiplicitiesPreserved targetWindow
    nearOffFinsetPreservedWitness :
      Window.PoleNearTargetWindow.nearOffFinsetPreserved targetWindow

    FarComplementPreserved : Set
    farComplementPreservedWitness : FarComplementPreserved

    producerReference : String

open ActualSelectedPoleNearProducer public

------------------------------------------------------------------------
-- 1. The selected-test same-object weld is generated from the attachment.
------------------------------------------------------------------------

producerToSameObjectWeld :
  ∀ {space formula orbit} →
  (producer : ActualSelectedPoleNearProducer space formula orbit) →
  Same.SelectedFkSameObjectWeld
    space formula orbit (attachment producer)
producerToSameObjectWeld producer =
  Same.fromConsumerAttachment (attachment producer)

------------------------------------------------------------------------
-- 2. The selected near/far explicit-formula weld is generated from the
--    theorem-bearing target window once both selected tests are identified.
------------------------------------------------------------------------

producerToSelectedFkExplicitFormulaWeld :
  ∀ {space formula orbit} →
  (producer : ActualSelectedPoleNearProducer space formula orbit) →
  Weld.SelectedFkExplicitFormulaWeld
    space formula orbit (attachment producer)
producerToSelectedFkExplicitFormulaWeld producer
  with sameSelectedTest producer
... | refl = record
  { Weld.SelectedFkExplicitFormulaWeld.sameOrdinateCluster =
      Window.PoleNearTargetWindow.sameOrdinateCluster (targetWindow producer)
  ; Weld.SelectedFkExplicitFormulaWeld.finitePoleNearSigned =
      Window.PoleNearTargetWindow.finitePoleNearSigned (targetWindow producer)
  ; Weld.SelectedFkExplicitFormulaWeld.farZeroRemainder =
      Window.PoleNearTargetWindow.farZeroRemainder (targetWindow producer)
  ; Weld.SelectedFkExplicitFormulaWeld.spectralIsClusterNearFar =
      Window.PoleNearTargetWindow.spectralWindowDecomposition
        (targetWindow producer)
  ; Weld.SelectedFkExplicitFormulaWeld.finiteNearUsesSelectedSourceOrbit =
      Window.PoleNearTargetWindow.nearOffFinsetPreserved (targetWindow producer)
  ; Weld.SelectedFkExplicitFormulaWeld.finiteNearUsesSelectedSourceOrbitWitness =
      nearOffFinsetPreservedWitness producer
  ; Weld.SelectedFkExplicitFormulaWeld.sameOrdinateClusterUsesSelectedTarget =
      Window.PoleNearTargetWindow.targetRelativePhasePreserved
        (targetWindow producer)
  ; Weld.SelectedFkExplicitFormulaWeld.sameOrdinateClusterUsesSelectedTargetWitness =
      targetRelativePhasePreservedWitness producer
  ; Weld.SelectedFkExplicitFormulaWeld.farRemainderUsesSameCutoffComplement =
      FarComplementPreserved producer
  ; Weld.SelectedFkExplicitFormulaWeld.farRemainderUsesSameCutoffComplementWitness =
      farComplementPreservedWitness producer
  ; Weld.SelectedFkExplicitFormulaWeld.weldReference = producerReference producer
  }

------------------------------------------------------------------------
-- 3. The near/far weld is automatically attached to the same literal selected
--    test; no second equality payment remains.
------------------------------------------------------------------------

producerToSameObjectNearFarAttachment :
  ∀ {space formula orbit} →
  (producer : ActualSelectedPoleNearProducer space formula orbit) →
  Same.SameObjectNearFarAttachment
    (producerToSameObjectWeld producer)
    (producerToSelectedFkExplicitFormulaWeld producer)
producerToSameObjectNearFarAttachment producer =
  Same.nearFarFromConsumerAttachment
    (attachment producer)
    (producerToSelectedFkExplicitFormulaWeld producer)

------------------------------------------------------------------------
-- Search compression.
------------------------------------------------------------------------

data SelectedPoleNearSearchAction : Set where
  separatelyRecoverOrbitAttachment
  separatelyRecoverNearFarWeld
  separatelyRecoverSameTestWeld
  recoverActualSelectedPoleNearProducer
  compileSelectedSameObjectWeld
  compileSelectedNearFarWeld
  compileSameObjectNearFarAttachment
  : SelectedPoleNearSearchAction

data SearchStatus : Set where
  live pruned downstream : SearchStatus

searchStatus : SelectedPoleNearSearchAction → SearchStatus
searchStatus separatelyRecoverOrbitAttachment = pruned
searchStatus separatelyRecoverNearFarWeld = pruned
searchStatus separatelyRecoverSameTestWeld = pruned
searchStatus recoverActualSelectedPoleNearProducer = live
searchStatus compileSelectedSameObjectWeld = downstream
searchStatus compileSelectedNearFarWeld = downstream
searchStatus compileSameObjectNearFarAttachment = downstream

separateNearFarSearchPruned :
  searchStatus separatelyRecoverNearFarWeld ≡ pruned
separateNearFarSearchPruned = refl

separateSameTestSearchPruned :
  searchStatus separatelyRecoverSameTestWeld ≡ pruned
separateSameTestSearchPruned = refl

record SelectedPoleNearSingleProducerBoundary : Set where
  constructor selected-pole-near-single-producer-boundary
  field
    orbitAttachmentAndWindowAreIndependentScientificLeaves : Bool
    orbitAttachmentAndWindowAreIndependentScientificLeavesIsFalse :
      orbitAttachmentAndWindowAreIndependentScientificLeaves ≡ false

    oneDependentSelectedProducerIsHighestAlphaTarget : Bool
    oneDependentSelectedProducerIsHighestAlphaTargetIsTrue :
      oneDependentSelectedProducerIsHighestAlphaTarget ≡ true

    sameObjectWeldGeneratedFromProducer : Bool
    sameObjectWeldGeneratedFromProducerIsTrue :
      sameObjectWeldGeneratedFromProducer ≡ true

    selectedNearFarWeldGeneratedFromProducer : Bool
    selectedNearFarWeldGeneratedFromProducerIsTrue :
      selectedNearFarWeldGeneratedFromProducer ≡ true

    actualProducerRecoveredHere : Bool
    actualProducerRecoveredHereIsFalse : actualProducerRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalSelectedPoleNearSingleProducerBoundary :
  SelectedPoleNearSingleProducerBoundary
canonicalSelectedPoleNearSingleProducerBoundary =
  selected-pole-near-single-producer-boundary
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "PR #691's single-source-producer pattern and PR #684's compiler-output pattern both apply here. Search for one dependent selected pole-near producer: the already-chosen source-orbit attachment, one theorem-bearing PoleNearTargetWindow on the same space/formula, and equality of their selected Test. Once recovered, the selected-test same-object weld, the same-formula cluster/finite-near/far weld and their same-object attachment are compiler outputs. Do not search for those projections independently. The actual producer is not recovered here and RH remains open."
