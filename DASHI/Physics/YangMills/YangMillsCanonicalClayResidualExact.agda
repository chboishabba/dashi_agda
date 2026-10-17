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
-- threaded into the canonical owner.  The residual constructor cannot invent
-- a trivial same-object relation or choose its own substituted D1 reference.
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
