module DASHI.Biology.Agriculture.BNFMechanismToFieldPromotionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Agriculture.NitrogenaseChemistryCrossPollinationExact as Nitrogenase
import DASHI.Biology.Agriculture.HungriaEconomicEmissionModel2023Exact as Econ2023
import DASHI.Biology.Agriculture.HungriaSourceAttributionPromotionBoundaryExact as Attribution
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolism
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Chemistry

------------------------------------------------------------------------
-- BIDI MECHANISM -> FIELD PROMOTION BRIDGE
--
-- External source roles used here:
--
--   Seefeldt, Hoffman, Dean 2009
--     DOI 10.1146/annurev.biochem.78.070907.103812
--     limiting Mo-nitrogenase reaction / mechanism.
--
--   Baral, Teixeira da Silva, Izaguirre-Mayoral 2016
--     DOI 10.1016/j.jplph.2016.01.013
--     review of nodule formation, ureide synthesis and transport; fixed N is
--     incorporated into transport compounds rather than jumping directly from
--     an enzyme equation to a whole-plant N balance.
--
--   Salvagiotti et al. 2008
--     DOI 10.1016/j.fcr.2008.03.001
--     637 field data sets; mean BNF contribution around 50-60% of soybean N
--     demand in that review, with a larger high-yield N gap in many settings.
--
-- These source propositions are NOT attributed as DASHI theorem machinery.
------------------------------------------------------------------------

data MechanismStage : Set where
  nitrogenaseOverallReaction : MechanismStage
  inNoduleEnablement : MechanismStage
  fixedNAssimilationToTransportPool : MechanismStage
  xylemTransportToShoot : MechanismStage
  seasonalPlantNAccumulation : MechanismStage
  fieldBNFShare : MechanismStage
  mineralNCounterfactual : MechanismStage
  avoidedCostAndEmissionAccounting : MechanismStage


data EvidenceState : Set where
  sourceBacked : EvidenceState
  typedRepoBridgeAvailable : EvidenceState
  sameObjectReplayOpen : EvidenceState

record StageReceipt : Set where
  constructor stageReceipt
  field
    stage : MechanismStage
    sourceEvidence : EvidenceState
    repoBridge : EvidenceState
    sameObject2024Replay : EvidenceState
    sourceReference : String
    boundedMeaning : String

open StageReceipt public

nitrogenaseStageReceipt : StageReceipt
nitrogenaseStageReceipt =
  stageReceipt
    nitrogenaseOverallReaction
    sourceBacked
    typedRepoBridgeAvailable
    sameObjectReplayOpen
    "Seefeldt, Hoffman, Dean 2009; DOI 10.1146/annurev.biochem.78.070907.103812"
    "Limiting overall Mo-nitrogenase reaction is source-backed; in-vivo seasonal flux is not inferred from stoichiometry alone"

ureideAssimilationReceipt : StageReceipt
ureideAssimilationReceipt =
  stageReceipt
    fixedNAssimilationToTransportPool
    sourceBacked
    typedRepoBridgeAvailable
    sameObjectReplayOpen
    "Baral, Teixeira da Silva, Izaguirre-Mayoral 2016; DOI 10.1016/j.jplph.2016.01.013"
    "Review supports conversion of nodule-fixed N into ureide transport chemistry in relevant nodulated legumes; does not quantify the 2024 Brazil-wide seasonal flux"

ureideTransportReceipt : StageReceipt
ureideTransportReceipt =
  stageReceipt
    xylemTransportToShoot
    sourceBacked
    typedRepoBridgeAvailable
    sameObjectReplayOpen
    "Baral, Teixeira da Silva, Izaguirre-Mayoral 2016; DOI 10.1016/j.jplph.2016.01.013"
    "Newly synthesized ureides are transported from nodule/root vascular tissue to aerial organs; this is a mechanism receipt, not a field-scale mass-balance replay"

fieldBNFShareReceipt : StageReceipt
fieldBNFShareReceipt =
  stageReceipt
    fieldBNFShare
    sourceBacked
    typedRepoBridgeAvailable
    sameObjectReplayOpen
    "Salvagiotti, Cassman, Specht, Walters, Weiss, Dobermann 2008; DOI 10.1016/j.fcr.2008.03.001"
    "Review of 637 data sets reports mean BNF contribution around 50-60% of soybean N demand and warns of a high-yield N gap; therefore universal 100% seasonal supply is not licensed"

accountingStageReceipt : StageReceipt
accountingStageReceipt =
  stageReceipt
    avoidedCostAndEmissionAccounting
    sourceBacked
    typedRepoBridgeAvailable
    sameObjectReplayOpen
    "Telles, Nogueira, Hungria 2023; DOI 10.1016/j.eti.2023.103158"
    "Avoided-cost and emissions accounting is source-backed for the paper's own input vintage; 2024 headline replay remains separate"

------------------------------------------------------------------------
-- Repo-native x-pollination surfaces.
------------------------------------------------------------------------

chemistryEnablementSurface : Set₁
chemistryEnablementSurface =
  ∀ {transition} → Chemistry.TypedReactionSemantics transition → Set

metabolicFluxSurface : Set₁
metabolicFluxSurface = Metabolism.OpenMetabolicNetwork

------------------------------------------------------------------------
-- The critical distinction is now two-dimensional:
--
--   mechanism proposition source-backed
--       != same-object 2024 Brazil-wide quantitative replay.
------------------------------------------------------------------------

mechanismSourceBackedDoesNotClose2024Replay :
  sameObject2024Replay ureideTransportReceipt ≡ sameObjectReplayOpen
mechanismSourceBackedDoesNotClose2024Replay = refl

fieldReviewDoesNotClose2024Replay :
  sameObject2024Replay fieldBNFShareReceipt ≡ sameObjectReplayOpen
fieldReviewDoesNotClose2024Replay = refl

accountingPaperDoesNotClose2024Replay :
  sameObject2024Replay accountingStageReceipt ≡ sameObjectReplayOpen
accountingPaperDoesNotClose2024Replay = refl

------------------------------------------------------------------------
-- DASHI-original promotion firewalls.
------------------------------------------------------------------------

record MechanismPromotionBoundary : Set where
  constructor mechanismPromotionBoundary
  field
    enzymeStoichiometryImpliesSeasonalPlantFlux : Bool
    enzymeStoichiometryImpliesSeasonalPlantFluxIsFalse :
      enzymeStoichiometryImpliesSeasonalPlantFlux ≡ false
    ureideTransportImpliesWholeCropDemandSatisfied : Bool
    ureideTransportImpliesWholeCropDemandSatisfiedIsFalse :
      ureideTransportImpliesWholeCropDemandSatisfied ≡ false
    meanBNFShareImpliesEveryFieldSameShare : Bool
    meanBNFShareImpliesEveryFieldSameShareIsFalse :
      meanBNFShareImpliesEveryFieldSameShare ≡ false
    noAppliedNImpliesBNFAloneSuppliedEveryNAtom : Bool
    noAppliedNImpliesBNFAloneSuppliedEveryNAtomIsFalse :
      noAppliedNImpliesBNFAloneSuppliedEveryNAtom ≡ false
    sourceMechanismImpliesEconomicHeadline : Bool
    sourceMechanismImpliesEconomicHeadlineIsFalse :
      sourceMechanismImpliesEconomicHeadline ≡ false

canonicalMechanismPromotionBoundary : MechanismPromotionBoundary
canonicalMechanismPromotionBoundary =
  mechanismPromotionBoundary false refl false refl false refl false refl false refl

------------------------------------------------------------------------
-- Backward frontier from the 2024 headline consumer.
------------------------------------------------------------------------

data Required2024Producer : Set where
  brazil2024SoybeanAreaProducer : Required2024Producer
  brazil2024YieldProducer : Required2024Producer
  brazil2024BNFCounterfactualNProducer : Required2024Producer
  brazil2024UreaPriceProducer : Required2024Producer
  brazil2024EmissionFactorProducer : Required2024Producer
  modelIdentityProducer : Required2024Producer
  exactCalculationReplayProducer : Required2024Producer

producerClosed : Required2024Producer → Bool
producerClosed brazil2024SoybeanAreaProducer = false
producerClosed brazil2024YieldProducer = false
producerClosed brazil2024BNFCounterfactualNProducer = false
producerClosed brazil2024UreaPriceProducer = false
producerClosed brazil2024EmissionFactorProducer = false
producerClosed modelIdentityProducer = false
producerClosed exactCalculationReplayProducer = false

exactReplayStillOpen : producerClosed exactCalculationReplayProducer ≡ false
exactReplayStillOpen = refl

------------------------------------------------------------------------
-- Reuse the source-attribution rule explicitly: a quoted 2024 headline does
-- not become the hidden calculation workbook or transfer formal ownership.
------------------------------------------------------------------------

quoteDoesNotSupplyReplay = Attribution.speakerQuoteDoesNotSupplyCalculationReplay
sourceDoesNotTransferDASHIOwnership = Attribution.sourceArgumentDoesNotTransferDASHIOwnership

------------------------------------------------------------------------
-- Existing paper outputs remain versioned source facts.
------------------------------------------------------------------------

paperAvoidedCost2019_2020 = Econ2023.avoidedUreaCostIs15200MillionUSD
paperMitigation2019_2020 = Econ2023.mitigationIs183MillionMg
nitrogenaseStoichiometryClosed = Nitrogenase.enzymeStoichiometryClosed
