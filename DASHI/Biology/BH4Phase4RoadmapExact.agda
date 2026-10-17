module DASHI.Biology.BH4Phase4RoadmapExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4JointFluxFeasibilityExact as Flux
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Executed
import DASHI.Biology.Molecular.BH4PanelStoichiometricMatrixExact as Matrix
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Phase-4 roadmap after the live panel chemistry + first joint-flux execution,
-- with the next quantitative acquisition/interval-solver tranche implemented.
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
  acquireSABIOKineticCandidateEvidence : BH4Phase4Residual
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
  ∷ acquireSABIOKineticCandidateEvidence
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

quantitativeAcquisitionToolingReady : Bool
quantitativeAcquisitionToolingReady = true

intervalFluxSolverReady : Bool
intervalFluxSolverReady = true

executedPanelSpeciesCount : Nat
executedPanelSpeciesCount = Matrix.executedPanelSpeciesCount

executedPanelReactionCount : Nat
executedPanelReactionCount = Matrix.executedPanelReactionCount

-- Historical first live template: 15 core + 12 reaction-flux coordinates.
firstQuantitativeCoordinateCount : Nat
firstQuantitativeCoordinateCount = 27

-- Next-run template: 15 core + 12 reaction fluxes + 29 explicit exchanges.
expandedQuantitativeCoordinateCount : Nat
expandedQuantitativeCoordinateCount = 56

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

executedPanelDimensionsExact : executedPanelSpeciesCount ≡ 29
executedPanelDimensionsExact = refl

executedPanelReactionsExact : executedPanelReactionCount ≡ 12
executedPanelReactionsExact = refl

firstCoordinateCountExact : firstQuantitativeCoordinateCount ≡ 27
firstCoordinateCountExact = refl

expandedCoordinateCountExact : expandedQuantitativeCoordinateCount ≡ 56
expandedCoordinateCountExact = refl

firstFluxAttemptMissingBoundsExact : missingReactionFluxBounds ≡ 12
firstFluxAttemptMissingBoundsExact = refl

firstFluxAttemptMissingValuesExact : missingReactionFluxValues ≡ 12
firstFluxAttemptMissingValuesExact = refl

firstFluxAttemptMissingExchangeExact : missingExternalExchangeCoordinates ≡ 29
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
    candidateKineticEvidenceAutomaticallyPaysFluxBounds : Bool
    candidateKineticEvidenceAutomaticallyPaysFluxBoundsIsFalse :
      candidateKineticEvidenceAutomaticallyPaysFluxBounds ≡ false
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
    false refl false refl false refl false refl false refl false refl false refl

canonicalBH4Phase4RoadmapReceipt : Receipt.GenericReceipt
canonicalBH4Phase4RoadmapReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Phase-4 quantitative system-state roadmap"
    "DASHI.Biology.BH4Phase4RoadmapExact"
    "executed 16-protein panel -> 24 Rhea links -> 12 finite reactions + 3 MTOR residuals -> 29x12 matrix -> first 27-coordinate attempt -> next 56-coordinate reaction+exchange interval problem"
    "closes panel Rhea execution and finite-reaction promotion; records the first joint attempt as underdetermined and provides SABIO/PDBe-SIFTS acquisition plus a bounded interval steady-state solver for the next run"
    "underdetermined proves neither mechanism truth nor falsity; candidate kinetics do not automatically become flux bounds; residual protein reactions are not zero columns; Phase-4 closure does not automatically establish disease causation or clinical action"
    "python3 scripts/run_bh4_phase4_maxcut.py"
