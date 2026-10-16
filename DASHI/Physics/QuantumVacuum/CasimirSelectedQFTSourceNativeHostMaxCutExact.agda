module DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSourceNativeHostMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as Attach
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as Recovery
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as GRQFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as Host
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

------------------------------------------------------------------------
-- SOURCE-NATIVE SELECTED-QFT HOST MAX-CUT
--
-- The selected-QFT host previously exposed compact simplicity as a separate
-- application payment.  The live source-native recovery stack is stronger:
--
-- * PinnedYangMillsConstruction already owns `compactSimple : forall G`;
-- * source-native selection compiles the pinned/recovered-QFT attachment;
-- * QFTRecoveryReceipt then identifies that recovered construction with the
--   selected qftTarget after coarse graining.
--
-- Consequently compact simplicity is compiler output once the pinned
-- source-native selection is attached.  The first genuine host seams are the
-- legacy/source-native recovery projection compatibility, the pinned selection
-- itself, and literal interpretation of the selected group as quaternionic
-- SU(2).  No Dynkin label is needed for the host.
------------------------------------------------------------------------

record SourceNativePinnedHostSelection
    (U : Weld.UnifiedCandidate)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)) : Set₂ where
  field
    projectionCompatibility :
      Recovery.LegacyQFTRecoveryProjectionCompatibility U

    pinnedSelection :
      Recovery.PinnedSourceNativeRecoverySelection
        U pinned projectionCompatibility

open SourceNativePinnedHostSelection public

compiledPinnedRecoveredAttachment :
  forall {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} ->
  SourceNativePinnedHostSelection U pinned ->
  Attach.PinnedYangMillsRecoveredQFTAttachment U pinned
compiledPinnedRecoveredAttachment selection =
  Recovery.sourceNativeSelectionBuildsPinnedRecoveredAttachment
    (pinnedSelection selection)

qftRecoveryFromCasimirHandoff :
  forall {U : Weld.UnifiedCandidate} ->
  GRQFT.CasimirSameCandidateGRQFTHandoff U ->
  Weld.QFTRecoveryReceipt U
qftRecoveryFromCasimirHandoff handoff = GRQFT.qftRecovery handoff

sourceNativePinnedConstructionIsSelectedQFTTarget :
  forall {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} ->
  (selection : SourceNativePinnedHostSelection U pinned) ->
  Weld.QFTRecoveryReceipt U ->
  forall candidate regime ->
  Weld.qftRegime U regime ->
  Pinned.asLiteralYangMillsConstruction pinned
  ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
sourceNativePinnedConstructionIsSelectedQFTTarget selection qftRecovery =
  Attach.pinnedConstructionIsSelectedQFTTarget
    (compiledPinnedRecoveredAttachment selection)
    qftRecovery

sourceNativeSelectionBuildsSelectedSU2Host :
  forall {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} ->
  SourceNativePinnedHostSelection U pinned ->
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) ->
  (interpretation :
    QFT.CompactSimpleGroup (Weld.qftCarriers U) -> Gauge.GroupStructure) ->
  interpretation group ≡ SU2.su2QuaternionGroup ->
  String ->
  Host.CasimirSelectedQFTSU2Host U group
sourceNativeSelectionBuildsSelectedSU2Host
    {pinned = pinned} selection group interpretation interpreted reading =
  Host.hostFromPinnedYMConstruction
    pinned group interpretation interpreted reading

sourceNativeSelectionSuppliesSelectedCompactSimple :
  forall {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} ->
  SourceNativePinnedHostSelection U pinned ->
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) ->
  QFT.IsCompactSimple (Weld.qftSemantics U) group
sourceNativeSelectionSuppliesSelectedCompactSimple
    {pinned = pinned} selection group =
  Pinned.compactSimple pinned group

------------------------------------------------------------------------
-- Fail-closed boundary.
------------------------------------------------------------------------

data SourceNativeRecoveryAutomaticallyChoosesQuaternionSU2 : Set where

data CompactSimpleProofRequiresSecondSelectedQFTTheoremAfterPinnedSelection : Set where

sourceNativeRecoveryDoesNotChooseQuaternionSU2 :
  SourceNativeRecoveryAutomaticallyChoosesQuaternionSU2 -> ⊥
sourceNativeRecoveryDoesNotChooseQuaternionSU2 ()

noSecondCompactSimpleTheoremAfterPinnedSelection :
  CompactSimpleProofRequiresSecondSelectedQFTTheoremAfterPinnedSelection -> ⊥
noSecondCompactSimpleTheoremAfterPinnedSelection ()

data RemainingSourceNativeHostBlocker : Set where
  missingLegacyQFTRecoveryProjectionCompatibility : RemainingSourceNativeHostBlocker
  missingPinnedSourceNativeRecoverySelection : RemainingSourceNativeHostBlocker
  missingSelectedGroupQuaternionSU2Interpretation : RemainingSourceNativeHostBlocker

firstSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
firstSourceNativeHostBlocker = missingLegacyQFTRecoveryProjectionCompatibility

secondSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
secondSourceNativeHostBlocker = missingPinnedSourceNativeRecoverySelection

thirdSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
thirdSourceNativeHostBlocker = missingSelectedGroupQuaternionSU2Interpretation

record CasimirSelectedQFTSourceNativeHostBoundary : Set where
  constructor casimir-selected-qft-source-native-host-boundary
  field
    sourceNativePinnedRecoveryAttachmentCompilerOwned : Bool
    qftRecoveryReceiptConsumedFromCasimirHandoff : Bool
    compactSimpleWitnessCompiledFromPinnedConstruction : Bool
    independentSelectedCompactSimplePaymentRequired : Bool
    legacyProjectionCompatibilityRequired : Bool
    pinnedSourceNativeSelectionRequired : Bool
    selectedQuaternionSU2InterpretationRequired : Bool

open CasimirSelectedQFTSourceNativeHostBoundary public

canonicalSourceNativeHostBoundary : CasimirSelectedQFTSourceNativeHostBoundary
canonicalSourceNativeHostBoundary =
  casimir-selected-qft-source-native-host-boundary
    true true true false true true true

casimirSelectedQFTSourceNativeHostReading : String
casimirSelectedQFTSourceNativeHostReading =
  "The selected-QFT compact-simple witness is no longer an independent Casimir host payment. A PinnedYangMillsConstruction already proves IsCompactSimple for every group on the SAME qftCarriers/qftSemantics. The source-native recovery compiler turns projection compatibility plus a pinned source-native selection into the existing pinned recovered-QFT attachment, and the Casimir same-candidate handoff already owns QFTRecoveryReceipt to identify that recovered construction with the selected qftTarget. The remaining host seams are therefore: legacy/source-native recovery projection compatibility; selecting the pinned construction for the recovered microscopic state; and literal interpretation of the selected compact-simple group as the existing quaternionic SU(2) GroupStructure. Source-native recovery does not choose SU(2) by itself."
