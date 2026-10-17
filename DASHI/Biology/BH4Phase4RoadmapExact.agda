module DASHI.Biology.BH4Phase4RoadmapExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Phase-4 roadmap after the live panel chemistry + joint-flux execution.
------------------------------------------------------------------------

data BH4Phase : Set where
  identityAndProvenancePhase : BH4Phase
  literalReactionPhase : BH4Phase
  systemStateQuantitativePhase : BH4Phase
  mechanisticDiscriminationPhase : BH4Phase
  clinicalPromotionPhase : BH4Phase

currentBH4Phase : BH4Phase
currentBH4Phase = systemStateQuantitativePhase

data BH4Phase4Residual : Set where
  executePanelRheaAcquisition : BH4Phase4Residual
  promoteFinitePanelReactionReceipts : BH4Phase4Residual
  resolveNonFiniteMTORProteinReactionRepresentation : BH4Phase4Residual
  acquirePDBSIFTSResidueSiteWitnesses : BH4Phase4Residual
  payReactionSpecificFluxBounds : BH4Phase4Residual
  payCompartmentSpecificBH4BH2RedoxState : BH4Phase4Residual
  paySimultaneousConsumerDemand : BH4Phase4Residual
  payTransportOxidationExchangeVector : BH4Phase4Residual
  payIsoformSpecificNOSCouplingTransitions : BH4Phase4Residual
  payUpstreamToTSC2SameObjectTransport : BH4Phase4Residual
  discriminateAlternativeMechanisms : BH4Phase4Residual

-- executePanelRheaAcquisition and promoteFinitePanelReactionReceipts remain in
-- the historical vocabulary but are absent here after the 2026-10-17 live run:
-- 24 links -> 12 finite reaction columns + 3 explicit MTOR residual reactions.
livePhase4Residuals : List BH4Phase4Residual
livePhase4Residuals =
  resolveNonFiniteMTORProteinReactionRepresentation
  ∷ acquirePDBSIFTSResidueSiteWitnesses
  ∷ payReactionSpecificFluxBounds
  ∷ payCompartmentSpecificBH4BH2RedoxState
  ∷ paySimultaneousConsumerDemand
  ∷ payTransportOxidationExchangeVector
  ∷ payIsoformSpecificNOSCouplingTransitions
  ∷ payUpstreamToTSC2SameObjectTransport
  ∷ discriminateAlternativeMechanisms
  ∷ []

panelRheaAcquisitionExecuted : Bool
panelRheaAcquisitionExecuted = Executed.acquisitionExecuted Executed.canonicalExecutedPanelReactionReceipt

finitePanelReactionPromotionClosed : Bool
finitePanelReactionPromotionClosed = true

executedPanelSpeciesCount : Nat
executedPanelSpeciesCount = Matrix.executedPanelSpeciesCount

executedPanelReactionCount : Nat
executedPanelReactionCount = Matrix.executedPanelReactionCount

quantitativeCoordinateCount : Nat
quantitativeCoordinateCount = 27

wholeSystemFluxBalanceAttempted : Bool
wholeSystemFluxBalanceAttempted = true

firstJointFluxOutcome : Flux.FluxFeasibilityStatus
firstJointFluxOutcome = Flux.underdetermined

missingReactionFluxBounds : Nat
missingReactionFluxBounds = 12

missingReactionFluxValues : Nat
missingReactionFluxValues = 12

missingExternalExchangeCoordinates : Nat
missingExternalExchangeCoordinates = 29

executedPanelDimensionsExact :
  executedPanelSpeciesCount ≡ 29
executedPanelDimensionsExact = refl

executedPanelReactionsExact :
  executedPanelReactionCount ≡ 12
executedPanelReactionsExact = refl

firstFluxAttemptMissingBoundsExact :
  missingReactionFluxBounds ≡ 12
firstFluxAttemptMissingBoundsExact = refl

firstFluxAttemptMissingValuesExact :
  missingReactionFluxValues ≡ 12
firstFluxAttemptMissingValuesExact = refl

firstFluxAttemptMissingExchangeExact :
  missingExternalExchangeCoordinates ≡ 29
firstFluxAttemptMissingExchangeExact = refl

record BH4Phase4Boundary : Set where
  constructor bh4-phase4-boundary
  field
    underdeterminedMeansMechanismFalse : Bool
    underdeterminedMeansMechanismFalseIsFalse : underdeterminedMeansMechanismFalse ≡ false
    underdeterminedMeansMechanismTrue : Bool
    underdeterminedMeansMechanismTrueIsFalse : underdeterminedMeansMechanismTrue ≡ false
    finitePanelExecutionPaysQuantitativeFlux : Bool
    finitePanelExecutionPaysQuantitativeFluxIsFalse :
      finitePanelExecutionPaysQuantitativeFlux ≡ false
    residualMTORReactionMayBeInsertedAsZeroColumn : Bool
    residualMTORReactionMayBeInsertedAsZeroColumnIsFalse :
      residualMTORReactionMayBeInsertedAsZeroColumn ≡ false
    phase4CompletionAutomaticallyPromotesDiseaseCausation : Bool
    phase4CompletionAutomaticallyPromotesDiseaseCausationIsFalse :
      phase4CompletionAutomaticallyPromotesDiseaseCausation ≡ false
    phase4CompletionAutomaticallyPromotesClinicalAction : Bool
    phase4CompletionAutomaticallyPromotesClinicalActionIsFalse :
      phase4CompletionAutomaticallyPromotesClinicalAction ≡ false

open BH4Phase4Boundary public

canonicalBH4Phase4Boundary : BH4Phase4Boundary
canonicalBH4Phase4Boundary =
  bh4-phase4-boundary
    false refl false refl false refl false refl false refl false refl

canonicalBH4Phase4RoadmapReceipt : Receipt.GenericReceipt
canonicalBH4Phase4RoadmapReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative system-state roadmap"
    "DASHI.Biology.BH4Phase4RoadmapExact"
    "executed 16-protein panel -> 24 Rhea links -> 12 finite reactions + 3 MTOR residuals -> 29x12 matrix -> 27-coordinate parameter manifest -> first open-system flux attempt"
    "closes panel Rhea execution and finite-reaction promotion; records the first real joint flux attempt as underdetermined with exactly 12 missing reaction bounds, 12 missing flux values and 29 missing external-exchange coordinates"
    "underdetermined proves neither mechanism truth nor falsity; finite reaction coverage does not pay kinetics/flux; residual protein reactions are not zero columns; even Phase-4 closure does not automatically establish disease causation or clinical action"
    "python3 scripts/check_kitzerow_bh4_priority_all.py"
