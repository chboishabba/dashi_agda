module DASHI.Biology.JCoarseFineConsumerReductionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Biology.JFineCoarseRelativeScaleExact as Scale
import DASHI.Biology.JCoarseFineEvaluationFibreExact as Evaluation
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Modular

------------------------------------------------------------------------
-- JCOARSE / JFINE -> GENERIC CONSUMER REDUCTION
--
-- The existing Biology owners already make the crucial distinction: JFine is a
-- relative fine factor/fibre over JCoarse, not merely an absolute "bigger
-- model" label.  This module exports that geometry into the repo-wide
-- consumer-relative reduction kernel without promoting the finite J model to a
-- literal modular curve or physical ontology.
------------------------------------------------------------------------

jCoarseFineReopening : Fibre.CoarseFineReopening Modular.AbsoluteAddress
jCoarseFineReopening =
  Fibre.coarseFineReopening
    Modular.CoarseAddress
    Modular.FineAddress
    Modular.forgetFine
    Modular.finePart
    (λ coarse fine → coarse , fine)
    (λ { (coarse , fine) → refl })

jFineIsRelativeFactorNotAbsoluteFine :
  Scale.jAbsoluteFineFrequency
  ≡ Scale.jCoarseFrequency * Scale.jFineFrequency
jFineIsRelativeFactorNotAbsoluteFine =
  Scale.jAbsoluteFineIsCoarseTimesJFine

jAddressDepthSplitsCoarsePlusFine :
  Modular.jAbsoluteAddressDepth
  ≡ Modular.jCoarseAddressDepth + Modular.jFineAddressDepth
jAddressDepthSplitsCoarsePlusFine =
  Modular.jAbsoluteAddressDepthReconstructs

jFineEvaluationHasSection :
  (fine : Evaluation.Fine canonical) →
  Evaluation.evaluateAtDistinguished canonical
    (Evaluation.section canonical fine)
  ≡ fine
jFineEvaluationHasSection = Evaluation.evaluateSection canonical
  where
    canonical : Evaluation.PointedCoarseFineEvaluation
    canonical = Evaluation.canonicalJCoarseFineEvaluation

------------------------------------------------------------------------
-- A consumer that distinguishes two absolute J states in the same coarse fibre
-- immediately refutes the coarse-only code for that consumer.
------------------------------------------------------------------------

jFineSensitiveConsumerRefutesJCoarseOnly :
  ∀ {Action Observation}
    {step : Action → Modular.AbsoluteAddress → Modular.AbsoluteAddress}
    {observe : Modular.AbsoluteAddress → Observation} →
  Fibre.FineSensitiveConsumer jCoarseFineReopening observe →
  Reduction.CandidateReductionFailure
    step observe Modular.forgetFine
jFineSensitiveConsumerRefutesJCoarseOnly =
  Fibre.fineSensitivityRefutesCoarseOnlyReduction jCoarseFineReopening

------------------------------------------------------------------------
-- Conversely, if dynamics and a declared consumer really do factor through
-- JCoarse, then JCoarse is an exact ROM for that consumer while JFine remains
-- available as an exact reopening residual.
------------------------------------------------------------------------

jCoarseExactReductionRetainingJFine :
  ∀ {Action Observation}
    {step : Action → Modular.AbsoluteAddress → Modular.AbsoluteAddress}
    {observe : Modular.AbsoluteAddress → Observation} →
  (dynamics : Fibre.CoarseDynamicsClosure jCoarseFineReopening step) →
  (consumer : Fibre.CoarseConsumerFactorisation jCoarseFineReopening observe) →
  Σ (Reduction.ConsumerRelativeReduction
      Modular.AbsoluteAddress Action Observation)
    (λ rom → Reduction.ExactResidualReopening rom)
jCoarseExactReductionRetainingJFine dynamics consumer =
  rom , Fibre.coarseProjectionRetainsRelativeFineResidual
          jCoarseFineReopening dynamics consumer
  where
    rom : Reduction.ConsumerRelativeReduction
      Modular.AbsoluteAddress Action Observation
    rom = Fibre.coarseProjectionAsExactReduction
      jCoarseFineReopening dynamics consumer

record JCoarseFineConsumerReductionBoundary : Set where
  constructor jCoarseFineConsumerReductionBoundary
  field
    jFineIsMerelyAnotherNameForMaximumComputeFidelity : Bool
    jFineIsMerelyAnotherNameForMaximumComputeFidelityIsFalse :
      jFineIsMerelyAnotherNameForMaximumComputeFidelity ≡ false

    jFineCanServeAsExactReopeningResidual : Bool
    jFineCanServeAsExactReopeningResidualIsTrue :
      jFineCanServeAsExactReopeningResidual ≡ true

    jCoarseCanBeConsumerSafeWhileJFineIsRetained : Bool
    jCoarseCanBeConsumerSafeWhileJFineIsRetainedIsTrue :
      jCoarseCanBeConsumerSafeWhileJFineIsRetained ≡ true

    fineSensitiveConsumerCanRefuteJCoarseOnly : Bool
    fineSensitiveConsumerCanRefuteJCoarseOnlyIsTrue :
      fineSensitiveConsumerCanRefuteJCoarseOnly ≡ true

    finiteJGeometryAutomaticallyDefinesEveryRepoFidelityHierarchy : Bool
    finiteJGeometryAutomaticallyDefinesEveryRepoFidelityHierarchyIsFalse :
      finiteJGeometryAutomaticallyDefinesEveryRepoFidelityHierarchy ≡ false

canonicalJCoarseFineConsumerReductionBoundary :
  JCoarseFineConsumerReductionBoundary
canonicalJCoarseFineConsumerReductionBoundary =
  jCoarseFineConsumerReductionBoundary
    false refl true refl true refl true refl false refl
