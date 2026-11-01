module DASHI.Biology.Morphogenesis.LocalToGlobalControlBridge where

-- Local cells act from partial observations while the tissue-level quotient
-- carries a global morphology.  The bridge requires coherence between local
-- updates and the induced global transition.
record LocalToGlobalMorphogenesis : Set₁ where
  field
    Cell          : Set
    CellState     : Set
    TissueState   : Set
    LocalObservation : Set
    LocalAction   : Set
    Morphology    : Set
    Environment   : Set

    observeLocal  : Cell → TissueState → LocalObservation
    chooseAction  : Environment → Cell → LocalObservation → LocalAction
    localUpdate   : Cell → LocalAction → TissueState → TissueState
    tissueStep    : Environment → TissueState → TissueState
    morphology    : TissueState → Morphology

    AdhesionCompatible : TissueState → Set
    PolarityCompatible : TissueState → Set
    MechanicalBalance  : TissueState → Set
    ChemicalFieldCompatible : TissueState → Set
    BioelectricCompatible   : TissueState → Set

record LocalGlobalCoherenceWitness
  (L : LocalToGlobalMorphogenesis) : Set₁ where
  open LocalToGlobalMorphogenesis L
  field
    environment : Environment
    tissue      : TissueState

    LocalSchedule : Set
    applySchedule : LocalSchedule → TissueState → TissueState
    schedule      : LocalSchedule

    SameMorphologicalTransition : TissueState → TissueState → Set

    localUpdatesRealiseGlobalStep :
      SameMorphologicalTransition
        (applySchedule schedule tissue)
        (tissueStep environment tissue)

    adhesionCompatible : AdhesionCompatible tissue
    polarityCompatible : PolarityCompatible tissue
    mechanicalBalance  : MechanicalBalance tissue
    chemicalCompatible : ChemicalFieldCompatible tissue
    bioelectricCompatible : BioelectricCompatible tissue

record DistributedControllabilityWitness
  (L : LocalToGlobalMorphogenesis) : Set₁ where
  open LocalToGlobalMorphogenesis L
  field
    Start Target : Morphology
    ReachableUnderLocalPolicies : Morphology → Morphology → Set
    controllable : ReachableUnderLocalPolicies Start Target

-- Neither a genome, voltage field, chemical morphogen, nor mechanical field is
-- made the sole controller.  Each enters as one coupled constraint channel.
record LocalGlobalAuthorityBoundary : Set₁ where
  field
    noSingleMasterCode : Set
    localCompetenceIsNotGlobalOmniscience : Set
    globalPatternIsNotCentralControllerByDefinition : Set
    modelControllabilityIsNotEmpiricalRegeneration : Set
