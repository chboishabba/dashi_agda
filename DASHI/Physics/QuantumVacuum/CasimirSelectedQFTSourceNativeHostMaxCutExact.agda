module DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSourceNativeHostMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as Attach
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as Recovery
import DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingExact as R457Binding
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as GRQFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as Host
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

------------------------------------------------------------------------
-- SOURCE-NATIVE SELECTED-QFT HOST MAX-CUT
--
-- Formal legacy/source-native projection compatibility is now compiler-owned:
-- enrich a legacy state by retaining recoverQFT itself.  That formal adapter is
-- deliberately provenance-neutral.  The real physical/source seam is the R457
-- same-object attachment proving that legacy recoverQFT returns the literal
-- construction carried by the actual SourceNativeContinuumAndOS certificate.
--
-- Once that selected construction is pinned, compact simplicity is already a
-- field of PinnedYangMillsConstruction, and QFTRecoveryReceipt identifies the
-- recovered construction with the selected qftTarget.  No second compact-
-- simplicity theorem or Dynkin label is required.
------------------------------------------------------------------------

record SourceNativePinnedHostSelection
    (U : Weld.UnifiedCandidate)
    (pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)) : Set₂ where
  field
    pinnedSelection :
      Recovery.PinnedSourceNativeRecoverySelection
        U pinned Recovery.canonicalFormalLegacyProjectionCompatibility

open SourceNativePinnedHostSelection public

compiledPinnedRecoveredAttachment :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  SourceNativePinnedHostSelection U pinned →
  Attach.PinnedYangMillsRecoveredQFTAttachment U pinned
compiledPinnedRecoveredAttachment selection =
  Recovery.sourceNativeSelectionBuildsPinnedRecoveredAttachment
    (pinnedSelection selection)

qftRecoveryFromCasimirHandoff :
  ∀ {U : Weld.UnifiedCandidate} →
  GRQFT.CasimirSameCandidateGRQFTHandoff U →
  Weld.QFTRecoveryReceipt U
qftRecoveryFromCasimirHandoff handoff = GRQFT.qftRecovery handoff

sourceNativePinnedConstructionIsSelectedQFTTarget :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  (selection : SourceNativePinnedHostSelection U pinned) →
  Weld.QFTRecoveryReceipt U →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  Pinned.asLiteralYangMillsConstruction pinned
  ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
sourceNativePinnedConstructionIsSelectedQFTTarget selection qftRecovery =
  Attach.pinnedConstructionIsSelectedQFTTarget
    (compiledPinnedRecoveredAttachment selection)
    qftRecovery

sourceNativeSelectionBuildsSelectedSU2Host :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  SourceNativePinnedHostSelection U pinned →
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  (interpretation :
    QFT.CompactSimpleGroup (Weld.qftCarriers U) → Gauge.GroupStructure) →
  interpretation group ≡ SU2.su2QuaternionGroup →
  String →
  Host.CasimirSelectedQFTSU2Host U group
sourceNativeSelectionBuildsSelectedSU2Host
    {pinned = pinned} selection group interpretation interpreted reading =
  Host.hostFromPinnedYMConstruction
    pinned group interpretation interpreted reading

sourceNativeSelectionSuppliesSelectedCompactSimple :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  SourceNativePinnedHostSelection U pinned →
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  QFT.IsCompactSimple (Weld.qftSemantics U) group
sourceNativeSelectionSuppliesSelectedCompactSimple
    {pinned = pinned} selection group =
  Pinned.compactSimple pinned group

formalProjectionCompatibility :
  ∀ {U : Weld.UnifiedCandidate} →
  Recovery.LegacyQFTRecoveryProjectionCompatibility U
formalProjectionCompatibility =
  Recovery.canonicalFormalLegacyProjectionCompatibility

------------------------------------------------------------------------
-- Fail-closed boundary.
------------------------------------------------------------------------

data SourceNativeRecoveryAutomaticallyChoosesQuaternionSU2 : Set where

data CompactSimpleProofRequiresSecondSelectedQFTTheoremAfterPinnedSelection : Set where

data FormalProjectionCompatibilityAutomaticallySuppliesR457Provenance : Set where

sourceNativeRecoveryDoesNotChooseQuaternionSU2 :
  SourceNativeRecoveryAutomaticallyChoosesQuaternionSU2 → ⊥
sourceNativeRecoveryDoesNotChooseQuaternionSU2 ()

noSecondCompactSimpleTheoremAfterPinnedSelection :
  CompactSimpleProofRequiresSecondSelectedQFTTheoremAfterPinnedSelection → ⊥
noSecondCompactSimpleTheoremAfterPinnedSelection ()

formalProjectionDoesNotSupplyR457Provenance :
  FormalProjectionCompatibilityAutomaticallySuppliesR457Provenance → ⊥
formalProjectionDoesNotSupplyR457Provenance ()

data RemainingSourceNativeHostBlocker : Set where
  missingR457LegacyRecoverySameObjectAttachment : RemainingSourceNativeHostBlocker
  missingPinnedSourceNativeRecoverySelection : RemainingSourceNativeHostBlocker
  missingSelectedGroupQuaternionSU2Interpretation : RemainingSourceNativeHostBlocker

firstSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
firstSourceNativeHostBlocker = missingR457LegacyRecoverySameObjectAttachment

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
    formalProjectionCompatibilityCompilerPaid : Bool
    independentProjectionCompatibilityPaymentRequired : Bool
    r457LegacyRecoverySameObjectAttachmentRequired : Bool
    pinnedSourceNativeSelectionRequired : Bool
    selectedQuaternionSU2InterpretationRequired : Bool

open CasimirSelectedQFTSourceNativeHostBoundary public

canonicalSourceNativeHostBoundary : CasimirSelectedQFTSourceNativeHostBoundary
canonicalSourceNativeHostBoundary =
  casimir-selected-qft-source-native-host-boundary
    true true true false true false true true true

casimirSelectedQFTSourceNativeHostReading : String
casimirSelectedQFTSourceNativeHostReading =
  "The selected-QFT host is now recut around actual source provenance. Formal legacy projection compatibility is compiler-owned and is not physical payment. The live R457 SourceNativeContinuumAndOS certificate supplies the rich provenance object; the first real seam is same-object equality between legacy recoverQFT and the literal R457 construction. A pinned source-native selection then compiles the recovered-QFT attachment, and the Casimir handoff already supplies QFTRecoveryReceipt. Compact simplicity is a field of the pinned construction, so no independent compact-simple theorem remains. The final host seam is same-object identification of the selected compact-simple group with the existing quaternionic SU(2) group; source-native recovery does not choose that group by itself."
