module DASHI.Physics.Semiconductor.Device.LitavisSPADCoarseFineReductionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerRelativeReductionKernelExact as Kernel
import DASHI.Physics.Semiconductor.Device.LitavisSPADConsumerSafeReductionExact as Reduction

------------------------------------------------------------------------
-- LITAVIS SPAD COARSE/FINE REDUCTION BRIDGE
--
-- Cross-pollination with the existing coarse/fine relative-fibre kernel.
-- Histogram output is the coarse code; exact timestamp is the retained relative
-- fine coordinate.  The pair exactly reopens the finite event state.
--
-- This is repository-local formal structure.  The Litavis source motivates the
-- existence of histogram/timing modes but does not claim that this exact finite
-- model is the sensor implementation.
------------------------------------------------------------------------

litavisCoarseFineReopening :
  Fibre.CoarseFineReopening Reduction.PhotonEventState
litavisCoarseFineReopening =
  Fibre.coarseFineReopening
    Reduction.HistogramReduction
    Reduction.ExactTimestampObservation
    Reduction.histogramReduction
    Reduction.exactTimestampObservation
    reopen
    reopenExact
  where
    reopen :
      Reduction.HistogramReduction →
      Reduction.ExactTimestampObservation →
      Reduction.PhotonEventState
    reopen Reduction.sameHistogramBin Reduction.timestampA = Reduction.eventA
    reopen Reduction.sameHistogramBin Reduction.timestampB = Reduction.eventB

    reopenExact :
      (state : Reduction.PhotonEventState) →
      reopen
        (Reduction.histogramReduction state)
        (Reduction.exactTimestampObservation state)
      ≡ state
    reopenExact Reduction.eventA = refl
    reopenExact Reduction.eventB = refl

CoarseFineReopeningReceipt : Set₁
CoarseFineReopeningReceipt =
  Fibre.CoarseFineReopening Reduction.PhotonEventState

canonicalCoarseFineReopeningReceipt : CoarseFineReopeningReceipt
canonicalCoarseFineReopeningReceipt = litavisCoarseFineReopening

------------------------------------------------------------------------
-- Declared mode dynamics.
--
-- One software-visible action swaps the retained timing state while leaving the
-- histogram code unchanged.  This demonstrates the exact distinction between
-- dynamics that close on a coarse surface and a finer consumer that can still
-- separate states inside that coarse fibre.
------------------------------------------------------------------------

data DeclaredModeAction : Set where
  toggleTimingResidual : DeclaredModeAction

modeStep :
  DeclaredModeAction →
  Reduction.PhotonEventState →
  Reduction.PhotonEventState
modeStep toggleTimingResidual Reduction.eventA = Reduction.eventB
modeStep toggleTimingResidual Reduction.eventB = Reduction.eventA

coarseModeStep :
  DeclaredModeAction →
  Reduction.HistogramReduction →
  Reduction.HistogramReduction
coarseModeStep toggleTimingResidual Reduction.sameHistogramBin =
  Reduction.sameHistogramBin

litavisDeclaredModeDynamics :
  Fibre.CoarseDynamicsClosure litavisCoarseFineReopening modeStep
litavisDeclaredModeDynamics =
  Fibre.coarseDynamicsClosure
    coarseModeStep
    stepCommutes
  where
    stepCommutes :
      (action : DeclaredModeAction) →
      (state : Reduction.PhotonEventState) →
      Fibre.coarse litavisCoarseFineReopening (modeStep action state)
      ≡ coarseModeStep action (Fibre.coarse litavisCoarseFineReopening state)
    stepCommutes toggleTimingResidual Reduction.eventA = refl
    stepCommutes toggleTimingResidual Reduction.eventB = refl

DeclaredModeDynamicsReceipt : Set₁
DeclaredModeDynamicsReceipt =
  Fibre.CoarseDynamicsClosure litavisCoarseFineReopening modeStep

canonicalDeclaredModeDynamicsReceipt : DeclaredModeDynamicsReceipt
canonicalDeclaredModeDynamicsReceipt = litavisDeclaredModeDynamics

------------------------------------------------------------------------
-- Consumer-relative reduction.
------------------------------------------------------------------------

histogramConsumer : Reduction.PhotonEventState → Reduction.ReductionAnswer
histogramConsumer state =
  Reduction.reductionAnswer Reduction.histogramBinQuery state

coarseHistogramConsumer :
  Reduction.HistogramReduction → Reduction.ReductionAnswer
coarseHistogramConsumer Reduction.sameHistogramBin = Reduction.histogramBinAnswer

litavisHistogramConsumerFactorisation :
  Fibre.CoarseConsumerFactorisation
    litavisCoarseFineReopening
    histogramConsumer
litavisHistogramConsumerFactorisation =
  Fibre.coarseConsumerFactorisation
    coarseHistogramConsumer
    factors
  where
    factors : (state : Reduction.PhotonEventState) →
      histogramConsumer state ≡
      coarseHistogramConsumer
        (Fibre.coarse litavisCoarseFineReopening state)
    factors Reduction.eventA = refl
    factors Reduction.eventB = refl

HistogramConsumerReceipt : Set₁
HistogramConsumerReceipt =
  Fibre.CoarseConsumerFactorisation
    litavisCoarseFineReopening
    histogramConsumer

canonicalHistogramConsumerReceipt : HistogramConsumerReceipt
canonicalHistogramConsumerReceipt = litavisHistogramConsumerFactorisation

litavisHistogramExactReduction :
  Kernel.ConsumerRelativeReduction
    Reduction.PhotonEventState
    DeclaredModeAction
    Reduction.ReductionAnswer
litavisHistogramExactReduction =
  Fibre.coarseProjectionAsExactReduction
    litavisCoarseFineReopening
    litavisDeclaredModeDynamics
    litavisHistogramConsumerFactorisation

litavisHistogramResidualReopening :
  Kernel.ExactResidualReopening litavisHistogramExactReduction
litavisHistogramResidualReopening =
  Fibre.coarseProjectionRetainsRelativeFineResidual
    litavisCoarseFineReopening
    litavisDeclaredModeDynamics
    litavisHistogramConsumerFactorisation

------------------------------------------------------------------------
-- Fine-sensitive timestamp consumer refutes the same coarse code.
------------------------------------------------------------------------

exactTimestampConsumer : Reduction.PhotonEventState → Reduction.ReductionAnswer
exactTimestampConsumer state =
  Reduction.reductionAnswer Reduction.exactTimestampQuery state

litavisExactTimestampSensitive :
  Fibre.FineSensitiveConsumer
    litavisCoarseFineReopening
    exactTimestampConsumer
litavisExactTimestampSensitive =
  Fibre.fineSensitiveConsumer
    Reduction.eventA
    Reduction.eventB
    refl
    (λ ())
    "same histogram code, different exact timestamp answer"

ExactTimestampFailureReceipt : Set
ExactTimestampFailureReceipt =
  Kernel.CandidateReductionFailure
    modeStep
    exactTimestampConsumer
    (Fibre.coarse litavisCoarseFineReopening)

canonicalExactTimestampFailureReceipt : ExactTimestampFailureReceipt
canonicalExactTimestampFailureReceipt =
  Fibre.fineSensitivityRefutesCoarseOnlyReduction
    litavisCoarseFineReopening
    litavisExactTimestampSensitive

------------------------------------------------------------------------
-- Boundary: a safe coarse reduction may retain an exact residual.  Safety for
-- one declared consumer/action language does not require deleting the residual,
-- nor does it promote the coarse code into a sufficient representation for a
-- finer consumer.
------------------------------------------------------------------------

record CoarseFineBridgeBoundary : Set where
  constructor coarse-fine-bridge-boundary
  field
    histogramCodeCanBeExactForHistogramConsumer : Bool
    histogramCodeCanBeExactForHistogramConsumerIsTrue :
      histogramCodeCanBeExactForHistogramConsumer ≡ true
    coarseDynamicsClosureImpliesFineConsumerAdequacy : Bool
    coarseDynamicsClosureImpliesFineConsumerAdequacyIsFalse :
      coarseDynamicsClosureImpliesFineConsumerAdequacy ≡ false
    retainedTimestampResidualCanExactlyReopenFineState : Bool
    retainedTimestampResidualCanExactlyReopenFineStateIsTrue :
      retainedTimestampResidualCanExactlyReopenFineState ≡ true
    safeCoarseReductionRequiresResidualDeletion : Bool
    safeCoarseReductionRequiresResidualDeletionIsFalse :
      safeCoarseReductionRequiresResidualDeletion ≡ false
    sameCoarseCodeCanFailFineSensitiveConsumer : Bool
    sameCoarseCodeCanFailFineSensitiveConsumerIsTrue :
      sameCoarseCodeCanFailFineSensitiveConsumer ≡ true
    sourceArchitectureClaimProvesThisReductionModel : Bool
    sourceArchitectureClaimProvesThisReductionModelIsFalse :
      sourceArchitectureClaimProvesThisReductionModel ≡ false

canonicalCoarseFineBridgeBoundary : CoarseFineBridgeBoundary
canonicalCoarseFineBridgeBoundary =
  coarse-fine-bridge-boundary
    true refl
    false refl
    true refl
    false refl
    true refl
    false refl
