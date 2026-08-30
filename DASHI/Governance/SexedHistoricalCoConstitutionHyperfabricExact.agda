module DASHI.Governance.SexedHistoricalCoConstitutionHyperfabricExact where

------------------------------------------------------------------------
-- SEXED HISTORICAL CO-CONSTITUTION HYPERFABRIC
--
-- Cross-pollinates the provenance-preserving cultural hyperfabric with the
-- frame-relative sexed historical dialectic.  The 2x2 construction surface
-- keeps four directions distinct:
--
--   masculine -> masculine   masculine -> feminine
--   feminine  -> masculine   feminine  -> feminine
--
-- Mutual construction is explicitly independent of power parity.  Historical
-- epochs below are finite DASHI comparison frames, not claims that all people
-- in an era occupied one role or that sex/gender is binary in lived history.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.ProvenancePreservingCulturalHyperfabric as Hyper
import DASHI.Governance.SexedHistoricalSubjectDialecticBidiExact as Dialectic

------------------------------------------------------------------------
-- Historical base and four construction directions.
------------------------------------------------------------------------

data HistoricalEpoch : Set where
  witchTrialOrder
  suffrageRearticulation
  feministWitchReclamation
  reciprocalReconstitution
  : HistoricalEpoch

Position : Set
Position = Dialectic.HistoricalGenderedPosition

masculine : Position
masculine = Dialectic.masculineCoded

feminine : Position
feminine = Dialectic.feminineCoded

data ConstructionMode : Set where
  imposedNorm
  internalisedNorm
  counterFormation
  selfRearticulation
  reciprocalRevision
  pluralUnresolved
  : ConstructionMode

coConstructs : HistoricalEpoch → Position → Position → ConstructionMode
coConstructs witchTrialOrder masculine masculine = internalisedNorm
coConstructs witchTrialOrder masculine feminine = imposedNorm
coConstructs witchTrialOrder feminine masculine = reciprocalRevision
coConstructs witchTrialOrder feminine feminine = internalisedNorm

coConstructs suffrageRearticulation masculine masculine = pluralUnresolved
coConstructs suffrageRearticulation masculine feminine = pluralUnresolved
coConstructs suffrageRearticulation feminine masculine = counterFormation
coConstructs suffrageRearticulation feminine feminine = selfRearticulation

coConstructs feministWitchReclamation masculine masculine = pluralUnresolved
coConstructs feministWitchReclamation masculine feminine = pluralUnresolved
coConstructs feministWitchReclamation feminine masculine = counterFormation
coConstructs feministWitchReclamation feminine feminine = selfRearticulation

coConstructs reciprocalReconstitution masculine masculine = reciprocalRevision
coConstructs reciprocalReconstitution masculine feminine = reciprocalRevision
coConstructs reciprocalReconstitution feminine masculine = reciprocalRevision
coConstructs reciprocalReconstitution feminine feminine = reciprocalRevision

ConstructionTensor : Set
ConstructionTensor =
  (Position → Position → ConstructionMode)

constructionTensorAt : HistoricalEpoch → ConstructionTensor
constructionTensorAt epoch = coConstructs epoch

------------------------------------------------------------------------
-- Power is an independent fibre.  Construction does not imply equal capacity
-- to legislate, punish, allocate resources, define doctrine, or represent.
------------------------------------------------------------------------

data PowerAxis : Set where
  legalPower economicPower religiousPower familyPower
  sexualNormPower epistemicPower politicalRepresentationPower
  : PowerAxis

data PowerLevel : Set where
  lowPower mediumPower highPower : PowerLevel

powerAt : HistoricalEpoch → Position → PowerAxis → PowerLevel
powerAt witchTrialOrder masculine legalPower = highPower
powerAt witchTrialOrder masculine religiousPower = highPower
powerAt witchTrialOrder masculine politicalRepresentationPower = highPower
powerAt witchTrialOrder masculine _ = mediumPower
powerAt witchTrialOrder feminine legalPower = lowPower
powerAt witchTrialOrder feminine religiousPower = lowPower
powerAt witchTrialOrder feminine politicalRepresentationPower = lowPower
powerAt witchTrialOrder feminine _ = mediumPower

powerAt suffrageRearticulation masculine legalPower = highPower
powerAt suffrageRearticulation masculine politicalRepresentationPower = highPower
powerAt suffrageRearticulation feminine legalPower = mediumPower
powerAt suffrageRearticulation feminine politicalRepresentationPower = mediumPower
powerAt suffrageRearticulation _ _ = mediumPower

powerAt feministWitchReclamation _ _ = mediumPower
powerAt reciprocalReconstitution _ _ = mediumPower

PowerProfile : Set
PowerProfile = PowerAxis → PowerLevel

powerProfile : HistoricalEpoch → Position → PowerProfile
powerProfile epoch position = powerAt epoch position

witchTrialLegalPowerAsymmetry :
  powerAt witchTrialOrder masculine legalPower
  ≡ powerAt witchTrialOrder feminine legalPower → ⊥
witchTrialLegalPowerAsymmetry ()

------------------------------------------------------------------------
-- The 2x2 construction surface itself cannot recover power.
-- Two fine states share the same relation code but differ in legal power.
------------------------------------------------------------------------

record RelationalPoint : Set where
  constructor relational-point
  field
    epoch : HistoricalEpoch
    constructorPosition : Position
    constructedPosition : Position

open RelationalPoint public

relationSurface : RelationalPoint → ConstructionMode
relationSurface p =
  coConstructs (epoch p) (constructorPosition p) (constructedPosition p)

legalPowerOfConstructor : RelationalPoint → PowerLevel
legalPowerOfConstructor p =
  powerAt (epoch p) (constructorPosition p) legalPower

witchMasculineSelf : RelationalPoint
witchMasculineSelf = relational-point witchTrialOrder masculine masculine

witchFeminineSelf : RelationalPoint
witchFeminineSelf = relational-point witchTrialOrder feminine feminine

-- Both self-relations are internalisedNorm in the finite specimen, but legal
-- power differs.  Hence construction mode alone is not a power score.
constructionModeCannotRecoverLegalPower :
  INF.FactorsThrough relationSurface legalPowerOfConstructor → ⊥
constructionModeCannotRecoverLegalPower =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      witchMasculineSelf
      witchFeminineSelf
      refl
      (λ ()))

------------------------------------------------------------------------
-- Public sex/gender legibility likewise cannot recover the full 2x2 tensor.
------------------------------------------------------------------------

data PublicGenderSurface : Set where
  publiclyMasculine publiclyFeminine : PublicGenderSurface

publicGender : RelationalPoint → PublicGenderSurface
publicGender p with constructedPosition p
... | Dialectic.masculineCoded = publiclyMasculine
... | Dialectic.feminineCoded = publiclyFeminine

fullRelationalSignature : RelationalPoint → ConstructionMode × PowerLevel
fullRelationalSignature p = relationSurface p , legalPowerOfConstructor p

publicGenderCannotRecoverRelationalSignature :
  INF.FactorsThrough publicGender fullRelationalSignature → ⊥
publicGenderCannotRecoverRelationalSignature =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      witchMasculineSelf
      relational-point suffrageRearticulation masculine masculine
      refl
      (λ ()))

------------------------------------------------------------------------
-- Cultural hyperfabric instantiation.  Memory, practice, relation, knowledge,
-- material relation and provenance remain distinct fibres over historical time.
------------------------------------------------------------------------

data HistoricalMemory : Set where rememberedPersecution rememberedCitizenship rememberedReclamation : HistoricalMemory

data HistoricalPractice : Set where legalPractice politicalPractice ritualPractice : HistoricalPractice

data HistoricalKnowledge : Set where theologicalKnowledge civicKnowledge feministKnowledge : HistoricalKnowledge

data HistoricalMaterialRelation : Set where dependentMaterialRelation negotiatedMaterialRelation : HistoricalMaterialRelation

data HistoricalProvenance : Set where courtArchive suffrageArchive movementArchive comparativeConstruction : HistoricalProvenance

sexedHistoricalHyperfabric : Hyper.CulturalHyperfabric
sexedHistoricalHyperfabric =
  record
    { Hyper.Base = HistoricalEpoch
    ; Hyper.Point = λ _ → Position
    ; Hyper.Memory = λ _ _ → HistoricalMemory
    ; Hyper.Practice = λ _ _ → HistoricalPractice
    ; Hyper.Relation = λ _ _ → ConstructionTensor
    ; Hyper.Knowledge = λ _ _ → HistoricalKnowledge
    ; Hyper.MaterialRelation = λ _ _ → HistoricalMaterialRelation
    ; Hyper.Provenance = λ _ _ → HistoricalProvenance
    }

publicPositionProjection : Hyper.PublicProjection sexedHistoricalHyperfabric
publicPositionProjection =
  record
    { Hyper.Surface = PublicGenderSurface
    ; Hyper.project = λ _ position →
        casePosition position
    }
  where
    casePosition : Position → PublicGenderSurface
    casePosition Dialectic.masculineCoded = publiclyMasculine
    casePosition Dialectic.feminineCoded = publiclyFeminine

publicProjectionDoesNotBecomeWholeIdentity :
  Hyper.ProjectionPromotesGlobalIdentity
    sexedHistoricalHyperfabric publicPositionProjection → ⊥
publicProjectionDoesNotBecomeWholeIdentity =
  Hyper.projectionDoesNotPromoteGlobalIdentity

------------------------------------------------------------------------
-- Dialectical boundaries.
------------------------------------------------------------------------

data MutualConstructionImpliesPowerParity : Set where

data PowerAsymmetryImpliesOneWayConstruction : Set where

data ReciprocalRevisionGuaranteesHistoricalClosure : Set where

mutualConstructionDoesNotImplyPowerParity :
  MutualConstructionImpliesPowerParity → ⊥
mutualConstructionDoesNotImplyPowerParity ()

powerAsymmetryDoesNotEraseReverseConstruction :
  PowerAsymmetryImpliesOneWayConstruction → ⊥
powerAsymmetryDoesNotEraseReverseConstruction ()

reciprocalRevisionDoesNotGuaranteeClosure :
  ReciprocalRevisionGuaranteesHistoricalClosure → ⊥
reciprocalRevisionDoesNotGuaranteeClosure ()

record SexedHistoricalHyperfabricBoundary : Set where
  constructor sexed-historical-hyperfabric-boundary
  field
    mutualConstructionMeansEqualPower : Bool
    powerAsymmetryMeansOnlyDominantSideConstructs : Bool
    publicGenderCategoryRecoversConstructionTensor : Bool
    oneConstructionDirectionExhaustsHistory : Bool
    reciprocalFrameIsInevitableSynthesis : Bool
    fourConstructionDirectionsRemainDistinct : Bool
    powerRemainsIndependentFibre : Bool

canonicalSexedHistoricalHyperfabricBoundary : SexedHistoricalHyperfabricBoundary
canonicalSexedHistoricalHyperfabricBoundary =
  sexed-historical-hyperfabric-boundary
    false false false false false true true
