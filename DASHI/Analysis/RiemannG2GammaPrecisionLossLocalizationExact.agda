module DASHI.Analysis.RiemannG2GammaPrecisionLossLocalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientGammaBudgetTargetExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerReconciliation8889Exact as PQ8889

------------------------------------------------------------------------
-- GAMMA PRECISION-LOSS LOCALIZATION
--
-- The 8889 checked-Lean return already owns a uniform Gamma bound, but that
-- bound is too coarse for the sharp pole-quotient cluster comparison window.
-- Therefore the live theorem-search task is not another existence proof for an
-- upper bound.  It is to locate the first precision-losing step in the actual
-- same-taper producer chain and replace only that step by a consumer-adequate
-- estimate.
--
-- The vendored exact source now identifies the first coarse scaling mechanism:
-- PoleQuotientGammaBudget factors through stripConst, whose sample-test C2 norm
-- contains a second-derivative L1 term that grows quadratically as support
-- shrinks.  Thus taperNormEstimate is the recovered precision-loss stage.
------------------------------------------------------------------------

data GammaPrecisionStage : Set where
  sourceKernelEstimate : GammaPrecisionStage
  absoluteEnvelope : GammaPrecisionStage
  taperNormEstimate : GammaPrecisionStage
  parameterUniformisation : GammaPrecisionStage
  asymptoticRemainder : GammaPrecisionStage
  finalConstantComparison : GammaPrecisionStage
  sourceLocalizationStillRequired : GammaPrecisionStage

currentGammaPrecisionLossStage : GammaPrecisionStage
currentGammaPrecisionLossStage = taperNormEstimate


record ExistingCoarseGammaProducer : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    producerReference : String
    knownUpperBoundOwned : Set
    knownUpperBoundTooCoarseForSharpWindow : Set

open ExistingCoarseGammaProducer public

record GammaPrecisionLossLocalization
    (producer : ExistingCoarseGammaProducer) : Set₁ where
  field
    firstLosingStage : GammaPrecisionStage
    exactSourceStepIdentified : Set
    lossAtThatStep : Set
    earlierStepsPreserveRequiredPrecision : Set
    localizationReference : String

open GammaPrecisionLossLocalization public

------------------------------------------------------------------------
-- A repair must still produce the exact existing Agda Gamma target on the same
-- literal universal pole-quotient taper and must additionally fit the final
-- sharp budget window.  Merely localizing the loss is diagnostic, not closure.
------------------------------------------------------------------------

record SharpGammaProducer : Set₁ where
  field
    target : Gamma.PoleQuotientGammaBudgetTarget
    sameLiteralPoleQuotientTaperAsFinalConsumer : Set
    fitsSharpClusterAccuracyWindow : Set
    repairReference : String

open SharpGammaProducer public

sharpProducerClosesGammaPrecisionRepair :
  SharpGammaProducer -> PQ8889.GammaPrecisionRepair
sharpProducerClosesGammaPrecisionRepair producer = record
  { PQ8889.target = target producer
  ; PQ8889.sameLiteralPoleQuotientTaperAsFinalConsumer =
      sameLiteralPoleQuotientTaperAsFinalConsumer producer
  ; PQ8889.fitsSharpClusterAccuracyWindow =
      fitsSharpClusterAccuracyWindow producer
  ; PQ8889.producerReference = repairReference producer
  }

------------------------------------------------------------------------
-- Search pruning and admissible repair families.
------------------------------------------------------------------------

data GammaRepairAction : Set where
  reuseCoarseUniformBoundUnchanged : GammaRepairAction
  localizeFirstPrecisionLoss : GammaRepairAction
  sharpenLocatedKernelStep : GammaRepairAction
  sharpenLocatedEnvelopeStep : GammaRepairAction
  sharpenLocatedTaperNormStep : GammaRepairAction
  sharpenLocatedUniformisationStep : GammaRepairAction
  sharpenLocatedRemainderStep : GammaRepairAction
  repairFinalConstantComparison : GammaRepairAction


RepairRelevant : GammaRepairAction -> Set
RepairRelevant reuseCoarseUniformBoundUnchanged = ⊥
RepairRelevant localizeFirstPrecisionLoss = ⊤
RepairRelevant sharpenLocatedKernelStep = ⊤
RepairRelevant sharpenLocatedEnvelopeStep = ⊤
RepairRelevant sharpenLocatedTaperNormStep = ⊤
RepairRelevant sharpenLocatedUniformisationStep = ⊤
RepairRelevant sharpenLocatedRemainderStep = ⊤
RepairRelevant repairFinalConstantComparison = ⊤

reuseCoarseUniformBoundUnchangedPruned :
  RepairRelevant reuseCoarseUniformBoundUnchanged -> ⊥
reuseCoarseUniformBoundUnchangedPruned x = x

arbitraryGammaSearchAlreadyPruned :
  PQ8889.LeafRelevant PQ8889.findAnyGammaUpperBound -> ⊥
arbitraryGammaSearchAlreadyPruned = PQ8889.findAnyGammaUpperBoundPruned

checkedLeanOwnsSomeUniformGammaBound :
  PQ8889.gammaUniformBoundOwned
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ true
checkedLeanOwnsSomeUniformGammaBound =
  PQ8889.gammaUniformBoundOwnedIsTrue
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889

checkedLeanUniformBoundMissesSharpWindow :
  PQ8889.gammaUniformBoundFitsRequiredWindow
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889 ≡ false
checkedLeanUniformBoundMissesSharpWindow =
  PQ8889.gammaUniformBoundFitsRequiredWindowIsFalse
    PQ8889.canonicalCheckedLeanPoleQuotientReturn8889

record GammaPrecisionLocalizationBoundary : Set where
  constructor gamma-precision-localization-boundary
  field
    gammaUpperBoundExistenceIsStillTheResearchQuestion : Bool
    gammaUpperBoundExistenceIsStillTheResearchQuestionIsFalse :
      gammaUpperBoundExistenceIsStillTheResearchQuestion ≡ false

    exactPrecisionLossStepAlreadyRecoveredOnThisBranch : Bool
    exactPrecisionLossStepAlreadyRecoveredOnThisBranchIsTrue :
      exactPrecisionLossStepAlreadyRecoveredOnThisBranch ≡ true

    precisionLossLocalizationIsLive : Bool
    precisionLossLocalizationIsLiveIsTrue :
      precisionLossLocalizationIsLive ≡ true

    localizationAloneClosesGammaConsumer : Bool
    localizationAloneClosesGammaConsumerIsFalse :
      localizationAloneClosesGammaConsumer ≡ false

    sharpSameTaperProducerClosesGammaRepairInterface : Bool
    sharpSameTaperProducerClosesGammaRepairInterfaceIsTrue :
      sharpSameTaperProducerClosesGammaRepairInterface ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalGammaPrecisionLocalizationBoundary : GammaPrecisionLocalizationBoundary
canonicalGammaPrecisionLocalizationBoundary =
  gamma-precision-localization-boundary
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    "The vendored exact 8889 PoleQuotientGammaBudget source is now recovered. Its proof factors through gammaConeEnvelope and stripConst, and its own source commentary identifies the failure mechanism: stripConst includes the sample-test second-derivative L1 norm, which grows quadratically as the high-ordinate taper support shrinks. Treat taperNormEstimate/stripConst as the localized precision-loss stage. Repair that C2 envelope or bypass it with a sharper same-taper Gamma theorem; a generic Gamma existence proof is already owned. RH is not derived."
