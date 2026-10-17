{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCanonicalClayResidualExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.BalabanCMP109CanonicalSourceSemanticsObligationsExact as CMP109
open import DASHI.Physics.YangMills.BalabanCanonicalPhysicalTransferGapObligationExact as TransferGap
open import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedTermReplayExact as R409
open import DASHI.Physics.YangMills.BalabanCMP116CanonicalTraceEntropyBudgetExact as R429
open import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
open import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- Preferred non-Round research scheduler after historical Round contraction.
-- Every field is typed through one of the canonical package owners; no Round
-- scheduler is imported and no residual inhabitant is manufactured here.
--
-- CMP109 is no longer represented by three opaque Set-valued placeholders.
-- Its field is now typed through the selected shooting-map attachment, the
-- existing Ward/quartic response producer, and the minimal D1 transport
-- equality exposed by the canonical CMP109 owner.
------------------------------------------------------------------------

record YangMillsCanonicalClayResidual
    {TubePoint Component Background Tangent Scalar : Set}
    {cutoff : Nat}
    {Measure Schwinger Observable Energy Bound : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger)
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    {SourceTranscriptionReceipt
     ExecutionReplayReceipt
     SelectedTermIdentity
     ProofBearingEquality
     ExactCompilerStructure
     QuantitativeTraceEntropyBound
     SameObjectTraceAttachment : Set} : Set₁ where
  field
    cmp109SourceSemantics :
      CMP109.CMP109CanonicalSourceSemanticsObligations
        TubePoint cutoff Component Background Tangent Scalar

    physicalTransferGap :
      TransferGap.SelectedPhysicalTransferGapObligation closure spectrum

    cmp116SelectedTermReplay :
      R409.CMP116CanonicalSelectedTermReplay
        SourceTranscriptionReceipt
        ExecutionReplayReceipt
        SelectedTermIdentity
        ProofBearingEquality

    cmp116TraceEntropyBudget :
      R429.CMP116CanonicalTraceEntropyBudget
        ExactCompilerStructure
        QuantitativeTraceEntropyBound
        SameObjectTraceAttachment

------------------------------------------------------------------------

open YangMillsCanonicalClayResidual public

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

clayPromotion : Bool
clayPromotion = false
