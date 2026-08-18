module DASHI.Ontology.WikidataRepairReopeningExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (proj₁)

import DASHI.Core.MinimalSufficientResidual as Minimal
import DASHI.Core.ReopenableProjectionComposition as Reopenable

------------------------------------------------------------------------
-- Exact provenance/reopening chain for ontology diagnostics.
--
-- Cross-domain calibration: DASHI.Biology.SoTLEpistemicQuotientPipeline
-- demonstrates the same theorem shape for lived state -> expression -> coding
-- -> aggregate -> recommendation.  This module instantiates the generic owner
-- directly for source ontology -> transcription -> alignment -> diagnostic ->
-- repair candidate.  No Biology dependency is introduced here.
------------------------------------------------------------------------

data TranscribedGraph : Set where
  transcribedZero transcribedOne : TranscribedGraph

data AlignedGraph : Set where
  alignedZero alignedOne : AlignedGraph

data DiagnosticSurface : Set where
  diagnosticZero diagnosticOne : DiagnosticSurface

data RepairCandidate : Set where
  repairZero repairOne : RepairCandidate

transcribedBit : TranscribedGraph → Bool
transcribedBit transcribedZero = false
transcribedBit transcribedOne = true

transcribeFromBit : Bool → TranscribedGraph
transcribeFromBit false = transcribedZero
transcribeFromBit true = transcribedOne

alignFromTranscription : TranscribedGraph → AlignedGraph
alignFromTranscription transcribedZero = alignedZero
alignFromTranscription transcribedOne = alignedOne

transcriptionFromAlignment : AlignedGraph → TranscribedGraph
transcriptionFromAlignment alignedZero = transcribedZero
transcriptionFromAlignment alignedOne = transcribedOne

diagnoseFromAlignment : AlignedGraph → DiagnosticSurface
diagnoseFromAlignment alignedZero = diagnosticZero
diagnoseFromAlignment alignedOne = diagnosticOne

alignmentFromDiagnostic : DiagnosticSurface → AlignedGraph
alignmentFromDiagnostic diagnosticZero = alignedZero
alignmentFromDiagnostic diagnosticOne = alignedOne

repairFromDiagnostic : DiagnosticSurface → RepairCandidate
repairFromDiagnostic diagnosticZero = repairZero
repairFromDiagnostic diagnosticOne = repairOne

diagnosticFromRepair : RepairCandidate → DiagnosticSurface
diagnosticFromRepair repairZero = diagnosticZero
diagnosticFromRepair repairOne = diagnosticOne

transcriptionProjection : Minimal.FineBitState → TranscribedGraph
transcriptionProjection state = transcribeFromBit (Minimal.coarseFirstBit state)

transcriptionReopen : TranscribedGraph → Bool → Minimal.FineBitState
transcriptionReopen graph hidden =
  Minimal.reopenFromHiddenBit (transcribedBit graph) hidden

transcriptionReopensExactly :
  (state : Minimal.FineBitState) →
  transcriptionReopen
    (transcriptionProjection state)
    (Minimal.hiddenSecondBit state) ≡ state
transcriptionReopensExactly Minimal.fine00 = refl
transcriptionReopensExactly Minimal.fine01 = refl
transcriptionReopensExactly Minimal.fine10 = refl
transcriptionReopensExactly Minimal.fine11 = refl

transcriptionMap :
  Reopenable.ExactReopenableProjection Minimal.FineBitState TranscribedGraph
transcriptionMap =
  Reopenable.exactReopenableProjection Bool transcriptionProjection
    Minimal.hiddenSecondBit transcriptionReopen transcriptionReopensExactly

alignmentMap : Reopenable.ExactReopenableProjection TranscribedGraph AlignedGraph
alignmentMap =
  Reopenable.exactReopenableProjection ⊤ alignFromTranscription
    (λ graph → tt) (λ aligned receipt → transcriptionFromAlignment aligned)
    alignmentExact
  where
    alignmentExact : (graph : TranscribedGraph) →
      transcriptionFromAlignment (alignFromTranscription graph) ≡ graph
    alignmentExact transcribedZero = refl
    alignmentExact transcribedOne = refl

diagnosticMap : Reopenable.ExactReopenableProjection AlignedGraph DiagnosticSurface
diagnosticMap =
  Reopenable.exactReopenableProjection ⊤ diagnoseFromAlignment
    (λ aligned → tt) (λ diagnostic receipt → alignmentFromDiagnostic diagnostic)
    diagnosticExact
  where
    diagnosticExact : (aligned : AlignedGraph) →
      alignmentFromDiagnostic (diagnoseFromAlignment aligned) ≡ aligned
    diagnosticExact alignedZero = refl
    diagnosticExact alignedOne = refl

repairMap : Reopenable.ExactReopenableProjection DiagnosticSurface RepairCandidate
repairMap =
  Reopenable.exactReopenableProjection ⊤ repairFromDiagnostic
    (λ diagnostic → tt) (λ repair receipt → diagnosticFromRepair repair)
    repairExact
  where
    repairExact : (diagnostic : DiagnosticSurface) →
      diagnosticFromRepair (repairFromDiagnostic diagnostic) ≡ diagnostic
    repairExact diagnosticZero = refl
    repairExact diagnosticOne = refl

transcriptionAlignmentMap :
  Reopenable.ExactReopenableProjection Minimal.FineBitState AlignedGraph
transcriptionAlignmentMap =
  Reopenable.composeExactReopenableProjection transcriptionMap alignmentMap

transcriptionAlignmentDiagnosticMap :
  Reopenable.ExactReopenableProjection Minimal.FineBitState DiagnosticSurface
transcriptionAlignmentDiagnosticMap =
  Reopenable.composeExactReopenableProjection transcriptionAlignmentMap diagnosticMap

fullOntologyDiagnosticRepairPipeline :
  Reopenable.ExactReopenableProjection Minimal.FineBitState RepairCandidate
fullOntologyDiagnosticRepairPipeline =
  Reopenable.composeExactReopenableProjection transcriptionAlignmentDiagnosticMap repairMap

fullRepairPipelineReopensExactly :
  (state : Minimal.FineBitState) →
  Reopenable.reopen fullOntologyDiagnosticRepairPipeline
    (Reopenable.project fullOntologyDiagnosticRepairPipeline state)
    (Reopenable.receipt fullOntologyDiagnosticRepairPipeline state) ≡ state
fullRepairPipelineReopensExactly =
  Reopenable.reopenExact fullOntologyDiagnosticRepairPipeline

sourceResidualSurvivesRepairPipeline :
  (state : Minimal.FineBitState) →
  proj₁ (proj₁ (proj₁ (Reopenable.receipt fullOntologyDiagnosticRepairPipeline state)))
  ≡ Minimal.hiddenSecondBit state
sourceResidualSurvivesRepairPipeline state = refl

record RepairReopeningBoundary : Set where
  constructor repairReopeningBoundary
  field
    repairCandidateRetainsExactSourceReceipt : Bool
    repairCandidateIsSourceOntologyIdentity : Bool

canonicalRepairReopeningBoundary : RepairReopeningBoundary
canonicalRepairReopeningBoundary = repairReopeningBoundary true false
