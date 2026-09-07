module DASHI.Biology.Cell.StaphylococcusAllicinFunctionCellStateBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Protein.ProteinFunctionProjection as ProteinFunction
import DASHI.Biology.Protein.StaphylococcusAllicinThiolomeExact as Thiolome
import DASHI.Biology.Cell.CellStateAttractor as CellState
import DASHI.Biology.Cell.CellRecoveryBoundary as Recovery
import DASHI.Biology.Cell.StaphylococcusAllicinRedoxRecoveryBidiExact as RedoxRecovery

------------------------------------------------------------------------
-- S. AUREUS ALLICIN: PROTEIN FUNCTION <-> CELL-STATE BIDI
------------------------------------------------------------------------

data TargetLane : Set where
  translationLane : TargetLane
  nucleotideMetabolismLane : TargetLane
  oxidativeStressLane : TargetLane
  globalRegulationLane : TargetLane
  virulenceBiofilmRegulationLane : TargetLane
  thiolHomeostasisLane : TargetLane


data FunctionalStatus : Set where
  modificationObserved : FunctionalStatus
  functionalEffectRelatedSource : FunctionalStatus
  functionalEffectDirectlyMeasured : FunctionalStatus
  cellStateEffectDirectlyMeasured : FunctionalStatus
  causalMediationEstablished : FunctionalStatus


record ProteinToCellStateReceipt : Set where
  constructor proteinToCellStateReceipt
  field
    proteinReference : String
    lane : TargetLane
    modificationReference : String
    proposedFunctionalEffect : String
    cellStateCoordinate : String
    status : FunctionalStatus
    sourceReference : String
    targetPreparationMeasured : Bool
    mediationMeasured : Bool
    boundary : String

open ProteinToCellStateReceipt public

efTuFunctionCandidate : ProteinToCellStateReceipt
efTuFunctionCandidate = proteinToCellStateReceipt
  "EF-Tu" translationLane
  "S-thioallylation observed under allicin stress"
  "possible translation perturbation; modification alone does not establish loss of elongation function"
  "proteome/translation state" modificationObserved
  "Loi et al. 2019 PMID 31121222" false false
  "requires direct activity/translation readout under the complete preparation"

guaBFunctionCandidate : ProteinToCellStateReceipt
guaBFunctionCandidate = proteinToCellStateReceipt
  "GuaB" nucleotideMetabolismLane
  "S-thioallylation observed under allicin stress"
  "possible IMP-dehydrogenase/nucleotide-metabolism perturbation"
  "metabolic state" modificationObserved
  "Loi et al. 2019 PMID 31121222" false false
  "requires target activity or metabolite-flux receipt"

mgrAFunctionCandidate : ProteinToCellStateReceipt
mgrAFunctionCandidate = proteinToCellStateReceipt
  "MgrA" globalRegulationLane
  "S-thioallylation observed under allicin stress"
  "possible redox-sensitive regulatory-state change"
  "RNA/regulatory state" modificationObserved
  "Loi et al. 2019 PMID 31121222" false false
  "regulator modification is not a transcriptome or phenotype theorem"

sarAFunctionCandidate : ProteinToCellStateReceipt
sarAFunctionCandidate = proteinToCellStateReceipt
  "SarA" virulenceBiofilmRegulationLane
  "S-thioallylation observed under allicin stress"
  "candidate change in SarA-dependent regulatory output relevant to biofilm/virulence context"
  "RNA/regulatory and downstream biofilm state" modificationObserved
  "Loi et al. 2019 PMID 31121222" false false
  "does not establish quorum sensing or anti-biofilm mediation"

bshRecoveryCandidate : ProteinToCellStateReceipt
bshRecoveryCandidate = proteinToCellStateReceipt
  "BSH/BrxAB/YpdA/MerA network" thiolHomeostasisLane
  "allicin-linked thiol/disulfide stress and recovery machinery"
  "reversal/buffering of thiol modification stress"
  "metabolic/redox recovery state" functionalEffectDirectlyMeasured
  "Loi et al. 2019 PMID 31121222" false false
  "pure-allicin recovery evidence does not establish complete-preparation recovery kinetics"

record FunctionCellStateWeld : Set₁ where
  field
    proteinFunctionSystem : ProteinFunction.ProteinFunctionSystem
    modificationFunctionBridge :
      ProteinFunction.ModificationFunctionBridge proteinFunctionSystem
    coupledCellState : CellState.CoupledCellState
    stressCellStateBridge : CellState.StressResponseCellStateBridge coupledCellState
    targetReceipt : ProteinToCellStateReceipt
    sameProteinTargetAsThiolome : Set
    modificationIdentityWeld : Set
    functionalEffectAssayWeld : Set
    proteomeOrRNAStateWeld : Set
    recoveryStateWeld : Set
    phenotypeMediationWeld : Set
    sameProteinWitness : sameProteinTargetAsThiolome
    modificationWitness : modificationIdentityWeld
    functionWitness : functionalEffectAssayWeld
    stateWitness : proteomeOrRNAStateWeld
    recoveryWitness : recoveryStateWeld
    mediationWitness : phenotypeMediationWeld

record FunctionCellStateBoundary : Set where
  constructor functionCellStateBoundary
  field
    modifiedTargetEqualsInhibitedTarget : Bool
    modifiedTargetEqualsInhibitedTargetIsFalse :
      modifiedTargetEqualsInhibitedTarget ≡ false
    alteredRegulatorEqualsAlteredWholeTranscriptome : Bool
    alteredRegulatorEqualsAlteredWholeTranscriptomeIsFalse :
      alteredRegulatorEqualsAlteredWholeTranscriptome ≡ false
    alteredCellStateEqualsBiofilmCausation : Bool
    alteredCellStateEqualsBiofilmCausationIsFalse :
      alteredCellStateEqualsBiofilmCausation ≡ false
    recoveryNetworkCanFeedExistingCellRecoveryOwner : Bool
    recoveryNetworkCanFeedExistingCellRecoveryOwnerIsTrue :
      recoveryNetworkCanFeedExistingCellRecoveryOwner ≡ true
    matchedFunctionAndStateAssaysCanRefineMechanism : Bool
    matchedFunctionAndStateAssaysCanRefineMechanismIsTrue :
      matchedFunctionAndStateAssaysCanRefineMechanism ≡ true

canonicalFunctionCellStateBoundary : FunctionCellStateBoundary
canonicalFunctionCellStateBoundary = functionCellStateBoundary
  false refl false refl false refl true refl true refl

existingChemicalStressBoundary :
  Recovery.ChemicalStressRecoveryBoundary → Recovery.ChemicalStressRecoveryBoundary
existingChemicalStressBoundary x = x

existingAllicinRecoveryBoundary : RedoxRecovery.RedoxRecoveryInterpretationBoundary
existingAllicinRecoveryBoundary = RedoxRecovery.canonicalRedoxRecoveryInterpretationBoundary
