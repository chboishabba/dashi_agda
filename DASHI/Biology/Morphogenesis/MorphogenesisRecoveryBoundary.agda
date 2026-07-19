module DASHI.Biology.Morphogenesis.MorphogenesisRecoveryBoundary where

import DASHI.Biology.Morphogenesis.MorphologicalGoalQuotient as Goal
import DASHI.Biology.Morphogenesis.LocalToGlobalControlBridge as LocalGlobal
import DASHI.Biology.Morphogenesis.RegenerativeRepairBoundary as Repair
import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection as Modes
import DASHI.Biology.Development.DevelopmentalGenomicInverseAdapter as Development
import DASHI.Biology.Agency.ScaleIndexedAgency as Agency

record MorphogenesisRecoveryBoundary : Set₁ where
  field
    goalSystem        : Goal.MorphologicalGoalSystem
    localGlobal       : LocalGlobal.LocalToGlobalMorphogenesis
    repairSystem      : Repair.RegenerativeRepairSystem
    modeSystem        : Modes.ReactionDiffusionModeSystem
    developmentalAdapter : Development.DevelopmentalGenomicInverseAdapter
    agencySystem      : Agency.ScaleIndexedAgencySystem

    CellStateToTissueGeometry : Set
    ReactionDiffusionToPattern : Set
    BioelectricToGoalControl  : Set
    LocalActionsToGlobalMorphology : Set
    DevelopmentToRegeneration : Set
    ScaleIndexedCompetencyComposition : Set

    cellTissueWitness : CellStateToTissueGeometry
    modePatternWitness : ReactionDiffusionToPattern
    bioelectricGoalWitness : BioelectricToGoalControl
    localGlobalWitness : LocalActionsToGlobalMorphology
    developmentRepairWitness : DevelopmentToRegeneration
    competencyCompositionWitness : ScaleIndexedCompetencyComposition

record MorphogenesisRecoveryWitness
  (M : MorphogenesisRecoveryBoundary) : Set₁ where
  field
    MorphologicalGoalRecovered : Set
    PatternSelectionRecovered  : Set
    LocalGlobalControlRecovered : Set
    RegenerativeRepairRecovered : Set
    DevelopmentalInverseIntegrated : Set

    goalWitness : MorphologicalGoalRecovered
    patternWitness : PatternSelectionRecovered
    controlWitness : LocalGlobalControlRecovered
    repairWitness : RegenerativeRepairRecovered
    developmentalWitness : DevelopmentalInverseIntegrated

record MorphogenesisOpenObligations
  (M : MorphogenesisRecoveryBoundary) : Set₁ where
  field
    calibratedCellTissueDynamics : Set
    coupledChemicalMechanicalBioelectricControl : Set
    finiteResourceControllability : Set
    interventionSensitivePatternMemory : Set
    regenerationAcrossPerturbationClasses : Set
    inverseGenomicCalibration : Set

morphogenesisRecoveryAvailable :
  {M : MorphogenesisRecoveryBoundary} →
  MorphogenesisRecoveryWitness M → MorphogenesisRecoveryWitness M
morphogenesisRecoveryAvailable witness = witness
