module DASHI.Biology.Morphogenesis.MorphogenesisRecoveryBoundary where

open import DASHI.Biology.Morphogenesis.MorphologicalGoalQuotient
open import DASHI.Biology.Morphogenesis.LocalToGlobalControlBridge
open import DASHI.Biology.Morphogenesis.RegenerativeRepairBoundary
open import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection
open import DASHI.Biology.Development.DevelopmentalGenomicInverseAdapter
open import DASHI.Biology.Agency.ScaleIndexedAgency

record MorphogenesisRecoveryBoundary : Set₁ where
  field
    goalSystem        : MorphologicalGoalSystem
    localGlobal       : LocalToGlobalMorphogenesis
    repairSystem      : RegenerativeRepairSystem
    modeSystem        : ReactionDiffusionModeSystem
    developmentalAdapter : DevelopmentalGenomicInverseAdapter
    agencySystem      : ScaleIndexedAgencySystem

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
