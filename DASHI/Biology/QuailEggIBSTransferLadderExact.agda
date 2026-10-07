module DASHI.Biology.QuailEggIBSTransferLadderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.QuailEggHistamineGutSnowballExact as Gut
import DASHI.Biology.QuailEggGutTransferRound2Exact as Round2
import DASHI.Biology.QuailEggOralGIAnimalBridgeExact as Animal
import DASHI.Biology.QuailEggHumanOralTransferExact as HumanOral
import DASHI.Biology.QuailEggAllergySafetyBoundaryExact as Safety
import DASHI.Biology.GutMastCellMechanismRouteAtlasExact as Routes
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Snowball

data TransferStage : Set where
  biochemicalStabilityStage : TransferStage
  cellMastCellStage : TransferStage
  oralGIAnimalStage : TransferStage
  humanOralNonIBSStage : TransferStage
  humanIBSMechanismStage : TransferStage
  humanIBSQuailInterventionStage : TransferStage

data TransferStatus : Set where
  paidBounded : TransferStatus
  paidAdjacent : TransferStatus
  openTerminal : TransferStatus

record TransferStageReceipt : Set where
  constructor transfer-stage-receipt
  field stage : TransferStage
        status : TransferStatus
        ownerReference : String
        paidReading : String
        residual : String

biochemicalStageReceipt : TransferStageReceipt
biochemicalStageReceipt = transfer-stage-receipt
  biochemicalStabilityStage paidBounded
  "QuailEggGutTransferRound2Exact.quailOvomucoidStability1994Receipt"
  "quail ovomucoid retains trypsin-inhibitory activity across severe biochemical stability/digestion challenges"
  "anti-mast-cell activity after digestion and human intestinal target engagement remain unpaid"

cellMastCellStageReceipt : TransferStageReceipt
cellMastCellStageReceipt = transfer-stage-receipt
  cellMastCellStage paidBounded
  "QuailEggHistamineGutSnowballExact.lianto2018QuailEggReceipt"
  "quail albumen suppresses histamine/tryptase/degranulation mediators in tested mast-cell conditions"
  "cell concentration, digestion/exposure, target identity and human IBS transfer remain open"

oralGIAnimalStageReceipt : TransferStageReceipt
oralGIAnimalStageReceipt = transfer-stage-receipt
  oralGIAnimalStage paidBounded
  "QuailEggOralGIAnimalBridgeExact.lianto2018EoEReceipt"
  "daily oral whole-quail intervention has GI/allergic pathway effects in a peanut-sensitized EoE-like mouse model"
  "species and disease-model transfer to human IBS remain open"

humanOralStageReceipt : TransferStageReceipt
humanOralStageReceipt = transfer-stage-receipt
  humanOralNonIBSStage paidBounded
  "QuailEggHumanOralTransferExact.benichou2014Receipt + andaloro2023Receipt"
  "randomized human oral quail-product exposure with rhinitis/allergen-challenge outcomes"
  "gut target engagement, IBS endpoint and clean component attribution remain open"

humanIBSMechanismStageReceipt : TransferStageReceipt
humanIBSMechanismStageReceipt = transfer-stage-receipt
  humanIBSMechanismStage paidAdjacent
  "GutMastCellMechanismRouteAtlasExact + De Palma 2022 + Wouters 2016 + Gao 2025"
  "human IBS has bounded histamine/mast-cell/barrier mechanisms, with H1/TRPV1, microbial-H4 and LPS/TLR4 routes kept distinct"
  "these IBS mechanism studies do not contain a quail intervention"

humanIBSQuailStageReceipt : TransferStageReceipt
humanIBSQuailStageReceipt = transfer-stage-receipt
  humanIBSQuailInterventionStage openTerminal
  "QuailEggGutTransferRound2Exact.canonicalSameObjectQuailGutExperiment"
  "terminal is specified as a same-object experiment rather than inferred from adjacent studies"
  "need quail-specific human IBS exposure with quantified treatment identity, target engagement/mechanism, clinical endpoint and safety"

record HumanIBSQuailTerminalReceipt : Set where
  constructor human-ibs-quail-terminal-receipt
  field
    route : Snowball.DiscoveryRoute
    terminalClosed : Bool
    terminalClosedIsFalse : terminalClosed ≡ false
    sameObjectExperiment : Round2.SameObjectQuailGutExperiment
    safetyRequirement : Safety.QuailEggInterventionSafetyRequirement
    mechanismAtlas : Routes.GutMastCellMechanismRouteAtlas
    acquisitionReference : String

canonicalHumanIBSQuailTerminalReceipt : HumanIBSQuailTerminalReceipt
canonicalHumanIBSQuailTerminalReceipt = human-ibs-quail-terminal-receipt
  Snowball.experimentalDesign false refl
  Round2.canonicalSameObjectQuailGutExperiment
  Safety.canonicalQuailEggInterventionSafetyRequirement
  Routes.canonicalGutMastCellMechanismRouteAtlas
  "Acquire a prospective human IBS quail intervention or equivalent same-object evidence; adjacent rhinitis, mouse-EoE, cell, biochemical and non-quail IBS mechanism studies do not close this terminal."

data AdjacentEvidenceClosesHumanIBSPermission : Set where
adjacentEvidenceDoesNotCloseHumanIBS : AdjacentEvidenceClosesHumanIBSPermission → ⊥
adjacentEvidenceDoesNotCloseHumanIBS ()

record QuailEggIBSTransferLadder : Set where
  constructor quail-egg-ibs-transfer-ladder
  field
    stages : List TransferStageReceipt
    terminal : HumanIBSQuailTerminalReceipt
    sourceRolesRetained : Bool
    sourceRolesRetainedIsTrue : sourceRolesRetained ≡ true
    adjacentEvidenceRetainedWithoutPromotion : Bool
    adjacentEvidenceRetainedWithoutPromotionIsTrue : adjacentEvidenceRetainedWithoutPromotion ≡ true

canonicalQuailEggIBSTransferLadder : QuailEggIBSTransferLadder
canonicalQuailEggIBSTransferLadder = quail-egg-ibs-transfer-ladder
  (biochemicalStageReceipt ∷ cellMastCellStageReceipt ∷ oralGIAnimalStageReceipt ∷
   humanOralStageReceipt ∷ humanIBSMechanismStageReceipt ∷ humanIBSQuailStageReceipt ∷ [])
  canonicalHumanIBSQuailTerminalReceipt
  true refl true refl

record QuailEggIBSTransferLadderBoundary : Set where
  constructor quail-egg-ibs-transfer-ladder-boundary
  field
    biochemicalSurvivalPaid : Bool
    biochemicalSurvivalPaidIsTrue : biochemicalSurvivalPaid ≡ true
    preclinicalMastCellPaid : Bool
    preclinicalMastCellPaidIsTrue : preclinicalMastCellPaid ≡ true
    oralGIAnimalPaid : Bool
    oralGIAnimalPaidIsTrue : oralGIAnimalPaid ≡ true
    humanOralExposurePaid : Bool
    humanOralExposurePaidIsTrue : humanOralExposurePaid ≡ true
    humanIBSMechanismsPaidAdjacent : Bool
    humanIBSMechanismsPaidAdjacentIsTrue : humanIBSMechanismsPaidAdjacent ≡ true
    quailSpecificHumanIBSTerminalClosed : Bool
    quailSpecificHumanIBSTerminalClosedIsFalse : quailSpecificHumanIBSTerminalClosed ≡ false
    furtherAdjacentLiteratureCannotSubstituteForTerminal : Bool
    furtherAdjacentLiteratureCannotSubstituteForTerminalIsTrue :
      furtherAdjacentLiteratureCannotSubstituteForTerminal ≡ true

canonicalQuailEggIBSTransferLadderBoundary : QuailEggIBSTransferLadderBoundary
canonicalQuailEggIBSTransferLadderBoundary = quail-egg-ibs-transfer-ladder-boundary
  true refl true refl true refl true refl true refl false refl true refl
