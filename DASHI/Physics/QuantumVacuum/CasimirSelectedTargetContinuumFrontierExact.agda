module DASHI.Physics.QuantumVacuum.CasimirSelectedTargetContinuumFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.QuantumVacuum.CasimirMinimalR457SourceNativeCompilerExact as Minimal
import DASHI.Physics.QuantumVacuum.CasimirSelectedTargetR457CompilerExact as Selected
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- PRIMITIVE CONTINUUM LEAVES ON THE SELECTED qftTarget
------------------------------------------------------------------------

record SelectedTargetContinuumLimitAttachment
    (U : Weld.UnifiedCandidate)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U)
    (group : Top.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    selectedFiniteMeasuresConverge :
      Top.IsContinuumLimitOf (Weld.qftSemantics U) group
        (Top.finiteMeasure (Selected.selectedTarget U candidate regime) group)
        (Top.continuumMeasure (Selected.selectedTarget U candidate regime) group)

open SelectedTargetContinuumLimitAttachment public

record SelectedTargetSchwingerMembershipAttachment
    (U : Weld.UnifiedCandidate)
    (candidate : Weld.Candidate U)
    (regime : Weld.Regime U)
    (group : Top.CompactSimpleGroup (Weld.qftCarriers U)) : Set₁ where
  field
    selectedSchwingerBelongsToContinuumMeasure :
      Top.SchwingerBelongsToMeasure (Weld.qftSemantics U)
        (Top.continuumMeasure (Selected.selectedTarget U candidate regime) group)
        (Top.schwinger (Selected.selectedTarget U candidate regime) group)

open SelectedTargetSchwingerMembershipAttachment public

splitContinuumAndSchwingerBuildMinimalAttachment :
  ∀ {U : Weld.UnifiedCandidate}
    {candidate : Weld.Candidate U}
    {regime : Weld.Regime U}
    {group : Top.CompactSimpleGroup (Weld.qftCarriers U)} →
  SelectedTargetContinuumLimitAttachment U candidate regime group →
  SelectedTargetSchwingerMembershipAttachment U candidate regime group →
  Minimal.MinimalContinuumSchwingerAttachment
    (Weld.qftSemantics U)
    (Selected.selectedTarget U candidate regime)
    group
splitContinuumAndSchwingerBuildMinimalAttachment continuum schwinger = record
  { Minimal.MinimalContinuumSchwingerAttachment.literalFiniteMeasuresConverge =
      selectedFiniteMeasuresConverge continuum
  ; Minimal.MinimalContinuumSchwingerAttachment.literalSchwingerBelongsToContinuumMeasure =
      selectedSchwingerBelongsToContinuumMeasure schwinger
  }

data SelectedTargetContinuumLeaf : Set where
  missingSelectedTargetContinuumLimit : SelectedTargetContinuumLeaf
  missingSelectedTargetSchwingerMembership : SelectedTargetContinuumLeaf

firstSelectedTargetContinuumLeaf : SelectedTargetContinuumLeaf
firstSelectedTargetContinuumLeaf = missingSelectedTargetContinuumLimit

secondSelectedTargetContinuumLeaf : SelectedTargetContinuumLeaf
secondSelectedTargetContinuumLeaf = missingSelectedTargetSchwingerMembership

record CasimirSelectedTargetContinuumBoundary : Set where
  constructor casimir-selected-target-continuum-boundary
  field
    splitContinuumAndSchwingerBuildMinimalAttachmentCompilerOwned : Bool
    selectedTargetContinuumLimitStillRequired : Bool
    selectedTargetSchwingerMembershipStillRequired : Bool
    combinedMinimalAttachmentRequiredAfterTwoLeaves : Bool

open CasimirSelectedTargetContinuumBoundary public

canonicalSelectedTargetContinuumBoundary : CasimirSelectedTargetContinuumBoundary
canonicalSelectedTargetContinuumBoundary =
  casimir-selected-target-continuum-boundary true true true false

casimirSelectedTargetContinuumReading : String
casimirSelectedTargetContinuumReading =
  "The first selected-Casimir source payment is two exact predicates on the already-selected qftTarget: finiteMeasure -> continuumMeasure for the chosen compact-simple sector, and schwinger(qftTarget) belongs to that exact continuum measure. Their conjunction compiles the older MinimalContinuumSchwingerAttachment; no independent combined receipt is required. Generic QFTRecoveryReceipt adapter booleans do not by themselves establish these same-object predicates."
