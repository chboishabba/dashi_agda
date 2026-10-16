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
-- Formal legacy/source-native projection compatibility is compiler-owned and
-- intentionally provenance-neutral.  R457's apparent extra recovery equality
-- is also compiler output once the canonical Round131RecoveredQFTAttachment is
-- paid on the SAME R457 literal construction: R457 merely needs the reverse
-- direction of Y = recoverQFT(...).
--
-- Thus the first live recovery seam is the existing Round131 same-object
-- recovered-QFT attachment instantiated for the R457 construction.  A pinned
-- source-native selection then compiles the pinned recovered attachment.
-- Compact simplicity is a field of that pinned construction; no second proof
-- or Dynkin label is required.
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
formalProjectionCompatibility = Recovery.canonicalFormalLegacyProjectionCompatibility

------------------------------------------------------------------------
-- Fail-closed boundary.
------------------------------------------------------------------------

data SourceNativeRecoveryAutomaticallyChoosesQuaternionSU2 : Set where

data CompactSimpleProofRequiresSecondSelectedQFTTheoremAfterPinnedSelection : Set where

data FormalProjectionCompatibilityAutomaticallySuppliesR457Provenance : Set where

data R457ProvenanceAutomaticallySuppliesRound131RecoveredAttachment : Set where

sourceNativeRecoveryDoesNotChooseQuaternionSU2 :
  SourceNativeRecoveryAutomaticallyChoosesQuaternionSU2 → ⊥
sourceNativeRecoveryDoesNotChooseQuaternionSU2 ()

noSecondCompactSimpleTheoremAfterPinnedSelection :
  CompactSimpleProofRequiresSecondSelectedQFTTheoremAfterPinnedSelection → ⊥
noSecondCompactSimpleTheoremAfterPinnedSelection ()

formalProjectionDoesNotSupplyR457Provenance :
  FormalProjectionCompatibilityAutomaticallySuppliesR457Provenance → ⊥
formalProjectionDoesNotSupplyR457Provenance ()

r457ProvenanceDoesNotSupplyRecoveredAttachment :
  R457ProvenanceAutomaticallySuppliesRound131RecoveredAttachment → ⊥
r457ProvenanceDoesNotSupplyRecoveredAttachment ()

data RemainingSourceNativeHostBlocker : Set where
  missingRound131RecoveredQFTAttachmentForR457 : RemainingSourceNativeHostBlocker
  missingPinnedSourceNativeRecoverySelection : RemainingSourceNativeHostBlocker
  missingSelectedGroupQuaternionSU2Interpretation : RemainingSourceNativeHostBlocker

firstSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
firstSourceNativeHostBlocker = missingRound131RecoveredQFTAttachmentForR457

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
    r457RecoveryEqualityCompiledFromRound131Attachment : Bool
    round131RecoveredQFTAttachmentForR457Required : Bool
    pinnedSourceNativeSelectionRequired : Bool
    selectedQuaternionSU2InterpretationRequired : Bool

open CasimirSelectedQFTSourceNativeHostBoundary public

canonicalSourceNativeHostBoundary : CasimirSelectedQFTSourceNativeHostBoundary
canonicalSourceNativeHostBoundary =
  casimir-selected-qft-source-native-host-boundary
    true true true false true false true true true true

casimirSelectedQFTSourceNativeHostReading : String
casimirSelectedQFTSourceNativeHostReading =
  "The selected-QFT host is recut around canonical shared recovery machinery. Formal projection compatibility is compiler-owned and supplies no rich provenance. R457 SourceNativeContinuumAndOS supplies the real provenance object, but its legacy-recovery equality is not a new theorem: a Round131RecoveredQFTAttachment for the SAME R457 construction compiles it by symmetry. That Round131 attachment is now the first live recovery seam. A pinned source-native selection then compiles the pinned recovered-QFT attachment; the Casimir handoff already supplies QFTRecoveryReceipt; and compact simplicity is a field of the pinned construction. The final host seam remains same-object identification of the selected compact-simple group with the existing quaternionic SU(2) group."
