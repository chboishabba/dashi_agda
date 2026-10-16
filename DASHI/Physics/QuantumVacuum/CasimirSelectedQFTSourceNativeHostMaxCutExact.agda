module DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSourceNativeHostMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PinnedYangMillsRecoveredQFTAttachmentExact as Attach
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as Recovery
import DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingExact as R457Binding
import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTAttachmentExact as Round131
import DASHI.Physics.QuantumVacuum.CasimirGRQFTUnificationCrossPollinationExact as GRQFT
import DASHI.Physics.QuantumVacuum.CasimirSelectedQFTSU2HostExact as Host
import DASHI.Physics.QuantumVacuum.CasimirRound131PinnedRecoveryCompilerExact as PinnedCompiler
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Gauge
import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier as SU2

------------------------------------------------------------------------
-- SOURCE-NATIVE SELECTED-QFT HOST MAX-CUT
--
-- Recovery is reduced to two genuine same-object inputs:
--
--   1. Round131RecoveredQFTAttachment U Y_R457
--   2. Y_R457 = asLiteralYangMillsConstruction pinned
--
-- Those compile the former pinned-selection receipt, pinned recovered-QFT
-- attachment and selected-target equality.  Compact simplicity is already a
-- field of the pinned construction.
--
-- The next group payment is also sharpened: the physical input is not an
-- arbitrary function interpreting every compact-simple index.  It is an
-- indexed SelectedGroupStructureRealization proving that one concrete group
-- structure realizes THIS selected group and is quaternionic SU(2).
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

compiledSourceNativePinnedHostSelection :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : QFT.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  Round131.Round131RecoveredQFTAttachment U Y →
  PinnedCompiler.R457LiteralPinnedConstructionIdentity U Y pinned →
  SourceNativePinnedHostSelection U pinned
compiledSourceNativePinnedHostSelection attachment identity = record
  { SourceNativePinnedHostSelection.pinnedSelection =
      PinnedCompiler.round131AndPinnedIdentityBuildSourceNativeSelection
        attachment identity
  }

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

round131PinnedInputsBuildSelectedQFTTarget :
  ∀ {U : Weld.UnifiedCandidate}
    {Y : QFT.LiteralYangMillsConstruction
      (Weld.qftCarriers U) (Weld.qftSemantics U)}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  Round131.Round131RecoveredQFTAttachment U Y →
  PinnedCompiler.R457LiteralPinnedConstructionIdentity U Y pinned →
  Weld.QFTRecoveryReceipt U →
  ∀ candidate regime →
  Weld.qftRegime U regime →
  Pinned.asLiteralYangMillsConstruction pinned
  ≡ Weld.qftTarget U (Weld.coarseGrain U candidate regime)
round131PinnedInputsBuildSelectedQFTTarget =
  PinnedCompiler.round131AndPinnedIdentityBuildSelectedTargetEquality

sourceNativeSelectionBuildsSelectedSU2HostFromRealization :
  ∀ {U : Weld.UnifiedCandidate}
    {pinned :
      Pinned.PinnedYangMillsConstruction
        {C = Weld.qftCarriers U}
        (Weld.qftSemantics U)} →
  SourceNativePinnedHostSelection U pinned →
  (group : QFT.CompactSimpleGroup (Weld.qftCarriers U)) →
  Host.SelectedGroupStructureRealization U group →
  String →
  Host.CasimirSelectedQFTSU2Host U group
sourceNativeSelectionBuildsSelectedSU2HostFromRealization
    {pinned = pinned} selection group realization reading =
  Host.hostFromPinnedSelectedStructure
    pinned group realization reading

-- Compatibility route retained for older callers.  It is not the current
-- physical payment surface because the all-groups interpretation is too weak to
-- establish selected-index same-object semantics by itself.
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
data Round131RecoveryAutomaticallyIdentifiesPinnedConstruction : Set where
data AllGroupsInterpretationAutomaticallyPaysSelectedGroupRealization : Set where

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

round131RecoveryDoesNotIdentifyPinnedConstruction :
  Round131RecoveryAutomaticallyIdentifiesPinnedConstruction → ⊥
round131RecoveryDoesNotIdentifyPinnedConstruction ()

allGroupsInterpretationDoesNotPaySelectedRealization :
  AllGroupsInterpretationAutomaticallyPaysSelectedGroupRealization → ⊥
allGroupsInterpretationDoesNotPaySelectedRealization ()

data RemainingSourceNativeHostBlocker : Set where
  missingRound131RecoveredQFTAttachmentForR457 : RemainingSourceNativeHostBlocker
  missingR457LiteralPinnedConstructionIdentity : RemainingSourceNativeHostBlocker
  missingSelectedGroupQuaternionSU2Realization : RemainingSourceNativeHostBlocker

firstSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
firstSourceNativeHostBlocker = missingRound131RecoveredQFTAttachmentForR457

secondSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
secondSourceNativeHostBlocker = missingR457LiteralPinnedConstructionIdentity

thirdSourceNativeHostBlocker : RemainingSourceNativeHostBlocker
thirdSourceNativeHostBlocker = missingSelectedGroupQuaternionSU2Realization

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
    pinnedSourceNativeSelectionCompiledFromRound131AndPinnedIdentity : Bool
    independentPinnedSourceNativeSelectionRequired : Bool
    r457LiteralPinnedConstructionIdentityRequired : Bool
    selectedGroupStructureRealizationBuildsHostCompilerOwned : Bool
    selectedGroupQuaternionSU2RealizationRequired : Bool
    independentAllGroupsStructureInterpretationRequired : Bool

open CasimirSelectedQFTSourceNativeHostBoundary public

canonicalSourceNativeHostBoundary : CasimirSelectedQFTSourceNativeHostBoundary
canonicalSourceNativeHostBoundary =
  casimir-selected-qft-source-native-host-boundary
    true true true false true false true true true false true true true false

casimirSelectedQFTSourceNativeHostReading : String
casimirSelectedQFTSourceNativeHostReading =
  "The selected-QFT host is reduced to genuine same-object inputs. First: Round131RecoveredQFTAttachment on the literal R457 construction. Second: equality of that same construction with the pinned physical Yang-Mills construction; these compile the old pinned-selection receipt and selected-target equality. Compact simplicity is already pinned. Third: an indexed SelectedGroupStructureRealization proving a concrete GroupStructure realizes the chosen compact-simple token and is the existing quaternionic SU(2). The old arbitrary all-groups interpretation remains compatibility-only and is not independent physical payment."
