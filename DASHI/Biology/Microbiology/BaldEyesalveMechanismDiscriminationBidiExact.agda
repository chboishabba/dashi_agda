module DASHI.Biology.Microbiology.BaldEyesalveMechanismDiscriminationBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.MechanismDiscriminationExact as MD
import DASHI.Biology.Microbiology.BaldEyesalveMechanismExperimentSelectionExact as Experiments
import DASHI.Biology.Microbiology.BaldEyesalveNineDayMechanismWeldExact as Weld
import DASHI.Biology.Cell.StaphylococcusAllicinFunctionCellStateBidiExact as FunctionState

------------------------------------------------------------------------
-- BALD'S EYESALVE MECHANISM DISCRIMINATION
--
-- The current evidence does not identify a unique mechanism.  This layer makes
-- competing mechanistic families predict different matched readout patterns so
-- residuals can selectively reopen the relevant carrier instead of merely
-- accumulating more descriptive observations.
------------------------------------------------------------------------

thiolDamageDominant : MD.MechanismHypothesis
thiolDamageDominant = MD.mechanismHypothesis
  "BE-M1 thiol-damage dominant"
  "allicin/related reactive sulfur species drive protein/LMW-thiol modification strongly enough to dominate phenotype"
  "target-preparation reactive sulfur exposure + target-system thiol modification + downstream functional/state effect"
  "must not be inferred from allicin presence or pure-compound thiol chemistry alone"

recoveryDominant : MD.MechanismHypothesis
recoveryDominant = MD.mechanismHypothesis
  "BE-M2 recovery-buffered"
  "BSH/BrxAB/YpdA/MerA recovery substantially buffers molecular damage and determines survival/state trajectory"
  "matched damage and recovery kinetics under complete-preparation exposure"
  "detoxification-marker induction alone is not equivalent to effective recovery"

quorumDominant : MD.MechanismHypothesis
quorumDominant = MD.mechanismHypothesis
  "BE-M3 quorum/regulatory dominant"
  "quorum/virulence regulatory perturbation contributes materially to anti-biofilm phenotype beyond direct killing"
  "target-system signal/regulatory readout plus mediation/rescue"
  "garlic or ajoene anti-QS literature does not transfer automatically"

matrixPenetrationDominant : MD.MechanismHypothesis
matrixPenetrationDominant = MD.mechanismHypothesis
  "BE-M4 matrix/penetration dominant"
  "mixture context changes delivery, penetration, sequestration or extracellular-matrix interaction so biofilm activity exceeds what bulk planktonic potency predicts"
  "spatial/extracellular exposure and matrix-state measurements under matched chemistry"
  "biofilm killing alone does not identify penetration or matrix mediation"

mixedMechanism : MD.MechanismHypothesis
mixedMechanism = MD.mechanismHypothesis
  "BE-M5 mixed multi-lane"
  "two or more partially independent molecular/regulatory/transport lanes contribute to the phenotype"
  "same-panel evidence showing no single admitted lane accounts for the joint readout pattern"
  "mixed is not a fallback label for unresolved data"

mechanismHypotheses : List MD.MechanismHypothesis
mechanismHypotheses =
  thiolDamageDominant ∷
  recoveryDominant ∷
  quorumDominant ∷
  matrixPenetrationDominant ∷
  mixedMechanism ∷ []

------------------------------------------------------------------------
-- Matched observable panel.
------------------------------------------------------------------------

sulfurExposure : MD.ObservableCoordinate
sulfurExposure = MD.observableCoordinate
  "BE-O1 reactive sulfur exposure"
  "time-resolved target-preparation LC-MS/GC-MS and matched exposure quantification"
  "fresh/day-9 complete reconstructed preparation"

proteinThiolModification : MD.ObservableCoordinate
proteinThiolModification = MD.observableCoordinate
  "BE-O2 protein/LMW-thiol modification"
  "S-thioallylome plus BSH/redox readout"
  "S. aureus under matched preparation exposure"

functionalPerturbation : MD.ObservableCoordinate
functionalPerturbation = MD.observableCoordinate
  "BE-O3 protein-function/cell-state perturbation"
  "translation/activity/metabolite-flux/RNA/proteome state panel"
  "same exposure and time window as molecular readouts"

recoveryFlux : MD.ObservableCoordinate
recoveryFlux = MD.observableCoordinate
  "BE-O4 thiol-recovery response"
  "BSH/BrxAB/YpdA/MerA activity/state and recovery kinetics"
  "matched damage-versus-recovery time course"

quorumVirulenceOutput : MD.ObservableCoordinate
quorumVirulenceOutput = MD.observableCoordinate
  "BE-O5 quorum/virulence regulatory output"
  "organism-appropriate signal/regulatory reporter panel"
  "matched viability/exposure controls"

biofilmSpatialEffect : MD.ObservableCoordinate
biofilmSpatialEffect = MD.observableCoordinate
  "BE-O6 biofilm spatial/matrix effect"
  "matrix penetration, spatial exposure and biofilm viability profile"
  "synthetic-wound/biofilm geometry"

phenotype : MD.ObservableCoordinate
phenotype = MD.observableCoordinate
  "BE-O7 phenotype"
  "CFU/viability/biofilm reduction"
  "matched endpoint panel"

observablePanel : List MD.ObservableCoordinate
observablePanel =
  sulfurExposure ∷ proteinThiolModification ∷ functionalPerturbation ∷
  recoveryFlux ∷ quorumVirulenceOutput ∷ biofilmSpatialEffect ∷ phenotype ∷ []

------------------------------------------------------------------------
-- Qualitative signatures.  These are hypotheses to test, not measured facts.
------------------------------------------------------------------------

p-thiol-O2 : MD.PredictedCoordinate
p-thiol-O2 = MD.predictedCoordinate
  thiolDamageDominant proteinThiolModification MD.stronglyUp
  "damage-dominant lane predicts substantial thiol modification under active exposure"
  false

p-thiol-O3 : MD.PredictedCoordinate
p-thiol-O3 = MD.predictedCoordinate
  thiolDamageDominant functionalPerturbation MD.up
  "substantial modification should be accompanied by measurable function/cell-state perturbation if this lane mediates phenotype"
  false

p-recovery-O4 : MD.PredictedCoordinate
p-recovery-O4 = MD.predictedCoordinate
  recoveryDominant recoveryFlux MD.stronglyUp
  "recovery-buffered model predicts strong compensatory thiol-homeostasis response"
  false

p-recovery-O7 : MD.PredictedCoordinate
p-recovery-O7 = MD.predictedCoordinate
  recoveryDominant phenotype MD.unchanged
  "effective recovery can preserve substantial survival despite molecular stress; exact direction remains exposure-dependent"
  false

p-quorum-O5 : MD.PredictedCoordinate
p-quorum-O5 = MD.predictedCoordinate
  quorumDominant quorumVirulenceOutput MD.stronglyDown
  "quorum/regulatory-dominant model predicts a large matched reporter shift"
  false

p-quorum-O2 : MD.PredictedCoordinate
p-quorum-O2 = MD.predictedCoordinate
  quorumDominant proteinThiolModification MD.unresolved
  "quorum mediation does not require a unique thiol-modification direction"
  false

p-matrix-O6 : MD.PredictedCoordinate
p-matrix-O6 = MD.predictedCoordinate
  matrixPenetrationDominant biofilmSpatialEffect MD.stronglyUp
  "matrix/penetration model predicts an exposure or matrix-state difference specifically in structured biofilm context"
  false

p-matrix-O5 : MD.PredictedCoordinate
p-matrix-O5 = MD.predictedCoordinate
  matrixPenetrationDominant quorumVirulenceOutput MD.unchanged
  "matrix-dominant model does not require a large quorum reporter effect"
  false

predictedPanel : List MD.PredictedCoordinate
predictedPanel =
  p-thiol-O2 ∷ p-thiol-O3 ∷ p-recovery-O4 ∷ p-recovery-O7 ∷
  p-quorum-O5 ∷ p-quorum-O2 ∷ p-matrix-O6 ∷ p-matrix-O5 ∷ []

canonicalDiscriminationPanel : MD.DiscriminationPanel
canonicalDiscriminationPanel = MD.discriminationPanel
  mechanismHypotheses
  observablePanel
  predictedPanel
  Experiments.canonicalMechanismExperimentSelection
  true
  false

------------------------------------------------------------------------
-- Selective reopening.  Residuals do not invalidate the whole mechanism graph.
------------------------------------------------------------------------

reopenThiolLane : MD.ReopenTarget
reopenThiolLane = MD.reopenTarget
  thiolDamageDominant
  "chemical exposure -> thiol modification -> protein function"
  "re-measure reactive sulfur exposure, modification occupancy and same-target functional effect"
  "phenotype without predicted thiol/function pattern weakens the damage-dominant route"

reopenRecoveryLane : MD.ReopenTarget
reopenRecoveryLane = MD.reopenTarget
  recoveryDominant
  "BSH/BrxAB/YpdA/MerA recovery carrier"
  "resolve recovery kinetics and whether recovery restores function rather than only marker abundance"
  "damage/recovery mismatch reopens the buffering model"

reopenQuorumLane : MD.ReopenTarget
reopenQuorumLane = MD.reopenTarget
  quorumDominant
  "quorum/virulence regulatory carrier"
  "measure signal-system output and perform signal/genetic perturbation or rescue"
  "anti-biofilm phenotype without discriminating regulatory effect cannot close quorum mediation"

reopenMatrixLane : MD.ReopenTarget
reopenMatrixLane = MD.reopenTarget
  matrixPenetrationDominant
  "biofilm matrix/penetration carrier"
  "measure spatial drug exposure, matrix state and structured-versus-planktonic contrast"
  "structured-context advantage without molecular/regulatory explanation raises this lane's salience"

record BaldEyesalveDiscriminationBoundary : Set where
  constructor baldEyesalveDiscriminationBoundary
  field
    largestPhenotypeEffectIdentifiesDominantMechanism : Bool
    largestPhenotypeEffectIdentifiesDominantMechanismIsFalse :
      largestPhenotypeEffectIdentifiesDominantMechanism ≡ false

    pureAllicinSignatureTransfersToMixture : Bool
    pureAllicinSignatureTransfersToMixtureIsFalse :
      pureAllicinSignatureTransfersToMixture ≡ false

    quorumReporterShiftAloneClosesQuorumMediation : Bool
    quorumReporterShiftAloneClosesQuorumMediationIsFalse :
      quorumReporterShiftAloneClosesQuorumMediation ≡ false

    selectiveResidualReopeningPreferredToGlobalInvalidation : Bool
    selectiveResidualReopeningPreferredToGlobalInvalidationIsTrue :
      selectiveResidualReopeningPreferredToGlobalInvalidation ≡ true

    matchedPanelCanTurnMechanismAtlasIntoModelSelectionProblem : Bool
    matchedPanelCanTurnMechanismAtlasIntoModelSelectionProblemIsTrue :
      matchedPanelCanTurnMechanismAtlasIntoModelSelectionProblem ≡ true

canonicalBaldEyesalveDiscriminationBoundary : BaldEyesalveDiscriminationBoundary
canonicalBaldEyesalveDiscriminationBoundary = baldEyesalveDiscriminationBoundary
  false refl false refl false refl true refl true refl

existingWeldBoundary : Weld.NineDayMechanismBoundary
existingWeldBoundary = Weld.canonicalNineDayMechanismBoundary

existingFunctionStateBoundary : FunctionState.FunctionCellStateBoundary
existingFunctionStateBoundary = FunctionState.canonicalFunctionCellStateBoundary
