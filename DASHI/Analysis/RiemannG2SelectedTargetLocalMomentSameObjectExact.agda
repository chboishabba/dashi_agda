module DASHI.Analysis.RiemannG2SelectedTargetLocalMomentSameObjectExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannG2FkOrbitConsumerAttachmentExact as Orbit
import DASHI.Analysis.RiemannG2SelectedPoleNearSingleProducerBidiExact as Selected
import DASHI.Analysis.RiemannG2LowGapClusteringMomentReductionExact as Moment

------------------------------------------------------------------------
-- SAME-OBJECT TARGET-LOCAL MOMENT ATTACHMENT
--
-- The clustering moment is not allowed to float as a second notion of target,
-- zero family, multiplicity or cutoff.  It is indexed by the already-existing
-- `ActualSelectedPoleNearProducer`, which itself owns one theorem-bearing
-- `PoleNearTargetWindow` on the SAME Weil space / explicit formula / selected
-- test and preserves target-relative phase, multiplicities and nearOffFinset.
--
-- This module therefore adds only the unpaid analytic value/normalization data.
-- Once a moment ledger is attached to the selected producer, the previously
-- proved Nat moment->ratio compiler is immediate compiler output.
------------------------------------------------------------------------

record SelectedTargetLocalMomentAttachment
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (orbit : Orbit.SourceFkOrbit)
    (selected : Selected.ActualSelectedPoleNearProducer space formula orbit)
    : Set₁ where
  field
    localMomentLedger : Moment.NormalizedLocalSecondMomentLedger

    -- Proof-bearing same-object receipts.  These are deliberately indexed by
    -- `selected`; no unrelated target/window carrier can inhabit this attachment
    -- without an explicit identification.
    momentUsesSelectedTarget :
      Window.PoleNearTargetWindow.targetRelativePhasePreserved
        (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

    momentUsesSelectedMultiplicities :
      Window.PoleNearTargetWindow.multiplicitiesPreserved
        (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

    momentUsesSelectedNearOffFinset :
      Window.PoleNearTargetWindow.nearOffFinsetPreserved
        (Selected.ActualSelectedPoleNearProducer.targetWindow selected)

    radiusIsGapSplitD_piOver3Lambda : Set
    normalizedMomentCountsEveryHighGapAtLeastOne : Set

    attachmentReference : String

open SelectedTargetLocalMomentAttachment public

selectedMomentGivesStrictTwoToOneRatio :
  ∀ {space formula orbit selected} →
  (attachment :
    SelectedTargetLocalMomentAttachment space formula orbit selected) →
  Moment.HighMassStrictlyBelowTwiceLow
    (SelectedTargetLocalMomentAttachment.localMomentLedger attachment)
selectedMomentGivesStrictTwoToOneRatio attachment =
  Moment.localSecondMomentForcesTwoToOneMassRatio
    (SelectedTargetLocalMomentAttachment.localMomentLedger attachment)

------------------------------------------------------------------------
-- Existing selected-window receipts are directly reusable; no second target
-- or near-family proof should be searched for.
------------------------------------------------------------------------

selectedProducerSuppliesTargetReceipt :
  ∀ {space formula orbit} →
  (selected : Selected.ActualSelectedPoleNearProducer space formula orbit) →
  Window.PoleNearTargetWindow.targetRelativePhasePreserved
    (Selected.ActualSelectedPoleNearProducer.targetWindow selected)
selectedProducerSuppliesTargetReceipt =
  Selected.ActualSelectedPoleNearProducer.targetRelativePhasePreservedWitness

selectedProducerSuppliesMultiplicityReceipt :
  ∀ {space formula orbit} →
  (selected : Selected.ActualSelectedPoleNearProducer space formula orbit) →
  Window.PoleNearTargetWindow.multiplicitiesPreserved
    (Selected.ActualSelectedPoleNearProducer.targetWindow selected)
selectedProducerSuppliesMultiplicityReceipt =
  Selected.ActualSelectedPoleNearProducer.multiplicitiesPreservedWitness

selectedProducerSuppliesNearFamilyReceipt :
  ∀ {space formula orbit} →
  (selected : Selected.ActualSelectedPoleNearProducer space formula orbit) →
  Window.PoleNearTargetWindow.nearOffFinsetPreserved
    (Selected.ActualSelectedPoleNearProducer.targetWindow selected)
selectedProducerSuppliesNearFamilyReceipt =
  Selected.ActualSelectedPoleNearProducer.nearOffFinsetPreservedWitness

------------------------------------------------------------------------
-- Search compression.
------------------------------------------------------------------------

data SelectedMomentPayment : Set where
  recoverSecondSelectedTarget : SelectedMomentPayment
  recoverSecondNearZeroFamily : SelectedMomentPayment
  recoverSecondMultiplicityCarrier : SelectedMomentPayment
  proveSelectedWindowLocalMoment : SelectedMomentPayment
  transportMomentRatioToExactPiCoefficient : SelectedMomentPayment


data PaymentState : Set where
  pruned : PaymentState
  live : PaymentState
  downstream : PaymentState

paymentState : SelectedMomentPayment → PaymentState
paymentState recoverSecondSelectedTarget = pruned
paymentState recoverSecondNearZeroFamily = pruned
paymentState recoverSecondMultiplicityCarrier = pruned
paymentState proveSelectedWindowLocalMoment = live
paymentState transportMomentRatioToExactPiCoefficient = downstream

secondTargetSearchPruned :
  paymentState recoverSecondSelectedTarget ≡ pruned
secondTargetSearchPruned = refl

secondNearFamilySearchPruned :
  paymentState recoverSecondNearZeroFamily ≡ pruned
secondNearFamilySearchPruned = refl

secondMultiplicitySearchPruned :
  paymentState recoverSecondMultiplicityCarrier ≡ pruned
secondMultiplicitySearchPruned = refl

record SelectedTargetLocalMomentBoundary : Set where
  constructor selected-target-local-moment-boundary
  field
    secondTargetCarrierRequired : Bool
    secondTargetCarrierRequiredIsFalse : secondTargetCarrierRequired ≡ false

    secondNearZeroFamilyRequired : Bool
    secondNearZeroFamilyRequiredIsFalse : secondNearZeroFamilyRequired ≡ false

    secondMultiplicityCarrierRequired : Bool
    secondMultiplicityCarrierRequiredIsFalse :
      secondMultiplicityCarrierRequired ≡ false

    selectedWindowMomentAttachmentIsExactConsumerShape : Bool
    selectedWindowMomentAttachmentIsExactConsumerShapeIsTrue :
      selectedWindowMomentAttachmentIsExactConsumerShape ≡ true

    selectedWindowMomentProducerInhabitedHere : Bool
    selectedWindowMomentProducerInhabitedHereIsFalse :
      selectedWindowMomentProducerInhabitedHere ≡ false

    momentToTwoToOneRatioIsCompilerOutputAfterAttachment : Bool
    momentToTwoToOneRatioIsCompilerOutputAfterAttachmentIsTrue :
      momentToTwoToOneRatioIsCompilerOutputAfterAttachment ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

open SelectedTargetLocalMomentBoundary public

canonicalSelectedTargetLocalMomentBoundary : SelectedTargetLocalMomentBoundary
canonicalSelectedTargetLocalMomentBoundary =
  selected-target-local-moment-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    true refl
    false refl
    "Do not create another target/window/zero-family ontology for the clustering moment. Index the moment producer by the existing ActualSelectedPoleNearProducer, reuse its target-relative-phase, multiplicity and nearOffFinset witnesses, and prove only the missing SAME-window normalized second-moment estimate. Once attached, the strict highGapMass < 2*lowGapMass receipt is compiler output; the elementary real 4/pi^2 coefficient transport is downstream."
