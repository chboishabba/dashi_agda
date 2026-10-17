{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCanonicalClayResidualExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.BalabanCMP109CanonicalSourceSemanticsObligationsExact as CMP109 using ()
open import DASHI.Physics.YangMills.BalabanCanonicalPhysicalTransferGapObligationExact as TransferGap using ()
open import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedTermReplayExact as R409 using ()
open import DASHI.Physics.YangMills.BalabanCMP116CanonicalTraceEntropyBudgetExact as R429 using ()
open import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap using ()
open import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit using ()

------------------------------------------------------------------------
-- Preferred non-Round research scheduler after historical Round contraction.
-- Qualified-only imports prevent per-owner authority/status names from leaking
-- into this scheduler's scope.
--
-- CMP109 carrier relations and reference D1 functions are fixed externally and
-- threaded into the canonical owner.  Likewise CMP116 now takes one fixed
-- selected source/term/proof relation for R409 and one fixed trace/compiler/
-- quantitative/attachment surface for R429.  Residual records cannot invent
-- the relations they are asked to inhabit.
------------------------------------------------------------------------

record YangMillsCanonicalClayResidual
    (SelectedSource : Set)
    (selectedSource : SelectedSource)
    (Producer : Set)
    (ProducerBelongsToSelectedSource : SelectedSource → Producer → Set)
    (TubePoint ShootingMap BetaScalar : Set)
    (ShootingMapBelongsToSelectedSource : SelectedSource → ShootingMap → Set)
    (initialInverseSquare : ShootingMap → TubePoint → BetaScalar)
    (renormalisationMap : ShootingMap → TubePoint → TubePoint)
    (cumulativeBeta : ShootingMap → TubePoint → BetaScalar)
    (minus : BetaScalar → BetaScalar → BetaScalar)
    (betaDifferenceAlgebra :
      ∀ shootingMap left right →
      minus
        (initialInverseSquare shootingMap (renormalisationMap shootingMap left))
        (initialInverseSquare shootingMap (renormalisationMap shootingMap right))
      ≡
      minus
        (cumulativeBeta shootingMap left)
        (cumulativeBeta shootingMap right))
    (Component Background Tangent D1Scalar : Set)
    (physicalCompositeD1 substitutedD1 :
      Component → Background → Tangent → D1Scalar)
    (D1BelongsToSelectedSource :
      SelectedSource → (Component → Background → Tangent → D1Scalar) → Set)
    (physicalCompositeD1BelongsToSelectedSource :
      D1BelongsToSelectedSource selectedSource physicalCompositeD1)
    (substitutedD1BelongsToSelectedSource :
      D1BelongsToSelectedSource selectedSource substitutedD1)
    (cutoff : Nat)

    (SelectedCMP116Source : Set)
    (selectedCMP116Source : SelectedCMP116Source)
    (SelectedCMP116Term : Set)
    (selectedCMP116Term : SelectedCMP116Term)
    (SelectedCMP116TermBelongsToSource :
      SelectedCMP116Source → SelectedCMP116Term → Set)
    (selectedCMP116TermSourceAttachment :
      SelectedCMP116TermBelongsToSource
        selectedCMP116Source selectedCMP116Term)
    (CMP116ProofBearingEquality :
      SelectedCMP116Source → SelectedCMP116Term → Set)
    (SourceTranscriptionReceipt ExecutionReplayReceipt : Set)

    (R429TraceCarrier : Set)
    (selectedR429Trace : R429TraceCarrier)
    (R429ExactCompilerStructure : Set)
    (r429ExactCompilerStructure : R429ExactCompilerStructure)
    (R429QuantitativeTraceEntropyBound :
      R429ExactCompilerStructure → R429TraceCarrier → Set)
    (R429SameObjectTraceAttachment :
      SelectedCMP116Source → R429TraceCarrier → Set)

    {Measure Schwinger Observable Energy Bound : Set}
    (closure : Limit.FiniteToContinuumOSClosure Measure Schwinger)
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound) : Set₁ where
  field
    cmp109SourceSemantics :
      CMP109.CMP109CanonicalSourceSemanticsObligations
        SelectedSource selectedSource
        Producer ProducerBelongsToSelectedSource
        TubePoint ShootingMap BetaScalar
        ShootingMapBelongsToSelectedSource
        initialInverseSquare renormalisationMap cumulativeBeta minus
        betaDifferenceAlgebra
        Component Background Tangent D1Scalar
        physicalCompositeD1 substitutedD1
        D1BelongsToSelectedSource
        physicalCompositeD1BelongsToSelectedSource
        substitutedD1BelongsToSelectedSource
        cutoff

    physicalTransferGap :
      TransferGap.SelectedPhysicalTransferGapObligation closure spectrum

    cmp116SelectedTermReplay :
      R409.CMP116CanonicalSelectedTermReplay
        SelectedCMP116Source selectedCMP116Source
        SelectedCMP116Term selectedCMP116Term
        SelectedCMP116TermBelongsToSource
        selectedCMP116TermSourceAttachment
        CMP116ProofBearingEquality
        SourceTranscriptionReceipt ExecutionReplayReceipt

    cmp116TraceEntropyBudget :
      R429.CMP116CanonicalTraceEntropyBudget
        SelectedCMP116Source selectedCMP116Source
        R429TraceCarrier selectedR429Trace
        R429ExactCompilerStructure r429ExactCompilerStructure
        R429QuantitativeTraceEntropyBound
        R429SameObjectTraceAttachment

------------------------------------------------------------------------

open YangMillsCanonicalClayResidual public

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

clayPromotion : Bool
clayPromotion = false
