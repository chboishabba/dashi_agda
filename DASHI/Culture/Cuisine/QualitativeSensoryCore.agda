module DASHI.Culture.Cuisine.QualitativeSensoryCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A qualitative culinary carrier is not a scalar pleasantness score.
-- It keeps stimulus dimensions, temporal unfolding, observer context,
-- interpretation, and safety evidence distinct.
------------------------------------------------------------------------

data TasteDimension : Set where
  sweet  : TasteDimension
  salty  : TasteDimension
  sour   : TasteDimension
  bitter : TasteDimension
  umami  : TasteDimension

data AromaFamily : Set where
  floral      : AromaFamily
  fruity      : AromaFamily
  citrus      : AromaFamily
  herbal      : AromaFamily
  green       : AromaFamily
  roasted     : AromaFamily
  nutty       : AromaFamily
  caramel     : AromaFamily
  smoky       : AromaFamily
  earthy      : AromaFamily
  fungal      : AromaFamily
  sulfurous   : AromaFamily
  marine      : AromaFamily
  animalic    : AromaFamily
  fermented   : AromaFamily
  ammoniaLike : AromaFamily
  oxidative   : AromaFamily

data MouthfeelDimension : Set where
  crisp      : MouthfeelDimension
  tender     : MouthfeelDimension
  chewy      : MouthfeelDimension
  creamy     : MouthfeelDimension
  fatty      : MouthfeelDimension
  silky      : MouthfeelDimension
  grainy     : MouthfeelDimension
  slimy      : MouthfeelDimension
  gelatinous : MouthfeelDimension
  dry        : MouthfeelDimension
  astringent : MouthfeelDimension

data ChemestheticDimension : Set where
  warming        : ChemestheticDimension
  burning        : ChemestheticDimension
  cooling        : ChemestheticDimension
  tingling       : ChemestheticDimension
  numbing        : ChemestheticDimension
  nasalSharpness : ChemestheticDimension
  carbonation    : ChemestheticDimension

data TemporalPhase : Set where
  aromaBeforeBite  : TemporalPhase
  attack           : TemporalPhase
  midPalate        : TemporalPhase
  finish           : TemporalPhase
  aftertaste       : TemporalPhase
  retronasalReturn : TemporalPhase

record SensoryProfile : Set where
  field
    tasteIntensity        : TasteDimension → Nat
    aromaIntensity        : AromaFamily → Nat
    mouthfeelIntensity    : MouthfeelDimension → Nat
    chemestheticIntensity : ChemestheticDimension → Nat
    temporalIntensity     : TemporalPhase → Nat

open SensoryProfile public

data Valence : Set where
  attractive : Valence
  neutral    : Valence
  aversive   : Valence
  ambivalent : Valence

data Familiarity : Set where
  familiar   : Familiarity
  learned    : Familiarity
  unfamiliar : Familiarity
  estranged  : Familiarity

data InterpretationFrame : Set where
  comfortFrame     : InterpretationFrame
  celebrationFrame : InterpretationFrame
  prestigeFrame    : InterpretationFrame
  medicinalFrame   : InterpretationFrame
  spoilageFrame    : InterpretationFrame
  challengeFrame   : InterpretationFrame
  homeFrame        : InterpretationFrame
  noveltyFrame     : InterpretationFrame

record ObserverContext : Set where
  field
    community       : String
    exposureCount   : Nat
    setting         : String
    expectation     : String
    familiarity     : Familiarity

open ObserverContext public

record QualitativeReading
    (profile : SensoryProfile)
    (observer : ObserverContext) : Set where
  field
    valence       : Valence
    frame         : InterpretationFrame
    description   : String

open QualitativeReading public

record DivergentReadingWitness (profile : SensoryProfile) : Set where
  field
    firstObserver  : ObserverContext
    secondObserver : ObserverContext
    firstReading   : QualitativeReading profile firstObserver
    secondReading  : QualitativeReading profile secondObserver

open DivergentReadingWitness public

------------------------------------------------------------------------
-- Umami is represented with an explicit non-additive interaction term.
-- The formalism does not identify umami with saltiness or generic savoury
-- aroma.  Glutamate and nucleotide loads remain independently visible.
------------------------------------------------------------------------

record UmamiBlend : Set where
  field
    glutamateLoad       : Nat
    nucleotideLoad      : Nat
    additiveBaseline    : Nat
    interactionTerm     : Nat
    combinedIntensity   : Nat

    baselineLaw         : additiveBaseline ≡ glutamateLoad + nucleotideLoad
    interactionLaw      : interactionTerm ≡ glutamateLoad * nucleotideLoad
    combinedLaw         : combinedIntensity ≡ additiveBaseline + interactionTerm

open UmamiBlend public

kombuKatsuobushiUmami : UmamiBlend
kombuKatsuobushiUmami = record
  { glutamateLoad     = 2
  ; nucleotideLoad    = 3
  ; additiveBaseline  = 5
  ; interactionTerm   = 6
  ; combinedIntensity = 11
  ; baselineLaw       = refl
  ; interactionLaw    = refl
  ; combinedLaw       = refl
  }

kombuKatsuobushiInteractionIsSix :
  interactionTerm kombuKatsuobushiUmami ≡ 6
kombuKatsuobushiInteractionIsSix = refl

kombuKatsuobushiCombinedIsEleven :
  combinedIntensity kombuKatsuobushiUmami ≡ 11
kombuKatsuobushiCombinedIsEleven = refl

------------------------------------------------------------------------
-- Funk, stink, bitterness, slime, and other strange profiles can be
-- culinary resources.  Their sensory proximity to spoilage is kept
-- separate from process assurance and food-safety evidence.
------------------------------------------------------------------------

data StrangenessCue : Set where
  sulfurCue      : StrangenessCue
  animalicCue    : StrangenessCue
  ammoniaCue     : StrangenessCue
  fungalCue      : StrangenessCue
  marineCue      : StrangenessCue
  fermentationCue : StrangenessCue
  slimeCue       : StrangenessCue
  bitterCue      : StrangenessCue
  oxidativeCue   : StrangenessCue
  medicinalCue   : StrangenessCue

data RewardCue : Set where
  fatReward          : RewardCue
  umamiReward        : RewardCue
  sweetnessReward    : RewardCue
  aromaticComplexity : RewardCue
  texturalContrast   : RewardCue
  warmingReward      : RewardCue
  memoryReward       : RewardCue
  prestigeReward     : RewardCue

data ProcessAssurance : Set where
  validatedFermentation    : ProcessAssurance
  controlledAging          : ProcessAssurance
  controlledCuring         : ProcessAssurance
  verifiedFreshPreparation : ProcessAssurance
  unknownProcess           : ProcessAssurance

data SafetyEvidence : Set where
  safetyVerified : SafetyEvidence
  safetyUnknown  : SafetyEvidence
  safetyRejected : SafetyEvidence

record ControlledStrangeness : Set where
  field
    stimulusProfile : SensoryProfile
    strangeCues     : List StrangenessCue
    rewardCues      : List RewardCue
    processEvidence : ProcessAssurance
    safetyEvidence  : SafetyEvidence
    servingContext  : String

open ControlledStrangeness public

record StinkSafetyBoundary : Set where
  field
    sensoryProfile : SensoryProfile
    perceivedCue   : StrangenessCue
    processStatus  : ProcessAssurance
    safetyStatus   : SafetyEvidence

open StinkSafetyBoundary public

------------------------------------------------------------------------
-- Dashi-style restraint: flavour quality and flavour loudness are distinct.
------------------------------------------------------------------------

record IntensityRestraint : Set where
  field
    totalLoudness        : Nat
    structuralDefinition : Nat
    lingeringLoad        : Nat
    reading              : String

open IntensityRestraint public

------------------------------------------------------------------------
-- Finite qualitative witnesses.
------------------------------------------------------------------------

dashiTaste : TasteDimension → Nat
dashiTaste sweet  = 0
dashiTaste salty  = 2
dashiTaste sour   = 0
dashiTaste bitter = 1
dashiTaste umami  = 11

dashiAroma : AromaFamily → Nat
dashiAroma floral      = 0
dashiAroma fruity      = 0
dashiAroma citrus      = 0
dashiAroma herbal      = 0
dashiAroma green       = 1
dashiAroma roasted     = 0
dashiAroma nutty       = 0
dashiAroma caramel     = 0
dashiAroma smoky       = 2
dashiAroma earthy      = 1
dashiAroma fungal      = 0
dashiAroma sulfurous   = 0
dashiAroma marine      = 3
dashiAroma animalic    = 0
dashiAroma fermented   = 0
dashiAroma ammoniaLike = 0
dashiAroma oxidative   = 0

dashiMouthfeel : MouthfeelDimension → Nat
dashiMouthfeel crisp      = 0
dashiMouthfeel tender     = 0
dashiMouthfeel chewy      = 0
dashiMouthfeel creamy     = 0
dashiMouthfeel fatty      = 0
dashiMouthfeel silky      = 1
dashiMouthfeel grainy     = 0
dashiMouthfeel slimy      = 0
dashiMouthfeel gelatinous = 0
dashiMouthfeel dry        = 0
dashiMouthfeel astringent = 0

dashiChemesthetic : ChemestheticDimension → Nat
dashiChemesthetic warming        = 1
dashiChemesthetic burning        = 0
dashiChemesthetic cooling        = 0
dashiChemesthetic tingling       = 0
dashiChemesthetic numbing        = 0
dashiChemesthetic nasalSharpness = 0
dashiChemesthetic carbonation    = 0

dashiTemporal : TemporalPhase → Nat
dashiTemporal aromaBeforeBite  = 2
dashiTemporal attack           = 2
dashiTemporal midPalate        = 5
dashiTemporal finish           = 3
dashiTemporal aftertaste       = 2
dashiTemporal retronasalReturn = 2

dashiSensoryProfile : SensoryProfile
dashiSensoryProfile = record
  { tasteIntensity = dashiTaste
  ; aromaIntensity = dashiAroma
  ; mouthfeelIntensity = dashiMouthfeel
  ; chemestheticIntensity = dashiChemesthetic
  ; temporalIntensity = dashiTemporal
  }

dashiIntensityRestraint : IntensityRestraint
dashiIntensityRestraint = record
  { totalLoudness = 4
  ; structuralDefinition = 9
  ; lingeringLoad = 2
  ; reading = "quiet aromatic attack with a defined umami middle and clean finish"
  }

funkTaste : TasteDimension → Nat
funkTaste sweet  = 1
funkTaste salty  = 4
funkTaste sour   = 2
funkTaste bitter = 2
funkTaste umami  = 6

funkAroma : AromaFamily → Nat
funkAroma floral      = 0
funkAroma fruity      = 1
funkAroma citrus      = 0
funkAroma herbal      = 0
funkAroma green       = 0
funkAroma roasted     = 0
funkAroma nutty       = 2
funkAroma caramel     = 0
funkAroma smoky       = 0
funkAroma earthy      = 3
funkAroma fungal      = 5
funkAroma sulfurous   = 2
funkAroma marine      = 0
funkAroma animalic    = 4
funkAroma fermented   = 5
funkAroma ammoniaLike = 3
funkAroma oxidative   = 1

funkMouthfeel : MouthfeelDimension → Nat
funkMouthfeel crisp      = 0
funkMouthfeel tender     = 1
funkMouthfeel chewy      = 0
funkMouthfeel creamy     = 5
funkMouthfeel fatty      = 5
funkMouthfeel silky      = 3
funkMouthfeel grainy     = 1
funkMouthfeel slimy      = 0
funkMouthfeel gelatinous = 0
funkMouthfeel dry        = 0
funkMouthfeel astringent = 1

funkChemesthetic : ChemestheticDimension → Nat
funkChemesthetic warming        = 0
funkChemesthetic burning        = 0
funkChemesthetic cooling        = 0
funkChemesthetic tingling       = 0
funkChemesthetic numbing        = 0
funkChemesthetic nasalSharpness = 3
funkChemesthetic carbonation    = 0

funkTemporal : TemporalPhase → Nat
funkTemporal aromaBeforeBite  = 5
funkTemporal attack           = 4
funkTemporal midPalate        = 6
funkTemporal finish           = 5
funkTemporal aftertaste       = 5
funkTemporal retronasalReturn = 6

fermentedFunkProfile : SensoryProfile
fermentedFunkProfile = record
  { tasteIntensity = funkTaste
  ; aromaIntensity = funkAroma
  ; mouthfeelIntensity = funkMouthfeel
  ; chemestheticIntensity = funkChemesthetic
  ; temporalIntensity = funkTemporal
  }

trainedFunkObserver : ObserverContext
trainedFunkObserver = record
  { community = "aged-fermentation dining context"
  ; exposureCount = 40
  ; setting = "shared table"
  ; expectation = "controlled fungal and animalic complexity"
  ; familiarity = learned
  }

unfamiliarFunkObserver : ObserverContext
unfamiliarFunkObserver = record
  { community = "unfamiliar tasting context"
  ; exposureCount = 0
  ; setting = "first encounter"
  ; expectation = "mild fresh dairy aroma"
  ; familiarity = unfamiliar
  }

trainedFunkReading : QualitativeReading fermentedFunkProfile trainedFunkObserver
trainedFunkReading = record
  { valence = attractive
  ; frame = prestigeFrame
  ; description = "controlled funk, earthy depth, and long savoury return"
  }

unfamiliarFunkReading : QualitativeReading fermentedFunkProfile unfamiliarFunkObserver
unfamiliarFunkReading = record
  { valence = aversive
  ; frame = spoilageFrame
  ; description = "ammoniacal and animalic cues interpreted as spoilage-like"
  }

fermentedFunkDivergentReading : DivergentReadingWitness fermentedFunkProfile
fermentedFunkDivergentReading = record
  { firstObserver = trainedFunkObserver
  ; secondObserver = unfamiliarFunkObserver
  ; firstReading = trainedFunkReading
  ; secondReading = unfamiliarFunkReading
  }

controlledAgedFunk : ControlledStrangeness
controlledAgedFunk = record
  { stimulusProfile = fermentedFunkProfile
  ; strangeCues = fungalCue ∷ animalicCue ∷ ammoniaCue ∷ fermentationCue ∷ []
  ; rewardCues = fatReward ∷ umamiReward ∷ aromaticComplexity ∷ prestigeReward ∷ []
  ; processEvidence = controlledAging
  ; safetyEvidence = safetyVerified
  ; servingContext = "verified aged-food service context"
  }

record SameCueDifferentSafety : Set where
  field
    firstBoundary  : StinkSafetyBoundary
    secondBoundary : StinkSafetyBoundary

open SameCueDifferentSafety public

sameFunkCueDifferentSafety : SameCueDifferentSafety
sameFunkCueDifferentSafety = record
  { firstBoundary = record
      { sensoryProfile = fermentedFunkProfile
      ; perceivedCue = ammoniaCue
      ; processStatus = controlledAging
      ; safetyStatus = safetyVerified
      }
  ; secondBoundary = record
      { sensoryProfile = fermentedFunkProfile
      ; perceivedCue = ammoniaCue
      ; processStatus = unknownProcess
      ; safetyStatus = safetyUnknown
      }
  }
