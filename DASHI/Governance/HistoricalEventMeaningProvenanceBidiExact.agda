module DASHI.Governance.HistoricalEventMeaningProvenanceBidiExact where

------------------------------------------------------------------------
-- HISTORICAL EVENT / MEANING / OFFICIAL CLASSIFICATION BIDI
--
-- Reusable provenance pattern motivated by witch-trial attribution and Luddite
-- factory/machine-breaking history.  A shared physical surface does not recover
-- cause, actor motive, official meaning, or later historical interpretation.
--
-- Historical calibration for the Luddite example: UK National Archives
-- educational/source materials on Luddite protest and official notices.
-- Source role only; finite witnesses below do not reconstruct a named incident.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF

record HistoricalSourceReceipt : Set where
  constructor historical-source-receipt
  field
    institutionAuthor : String
    title : String
    identifier : String
    boundedRole : String

ludditeArchiveReceipt : HistoricalSourceReceipt
ludditeArchiveReceipt = historical-source-receipt
  "The National Archives (UK)"
  "Why did the Luddites protest?"
  "official educational archive/source collection; no DOI asserted"
  "supports source-bounded study of machine breaking, wages/labour disputes and official criminal classification; does not imply every industrial fire was Luddite arson"

------------------------------------------------------------------------
-- Same visible event, different causal histories.
------------------------------------------------------------------------

data FineFactoryFireState : Set where
  accidentalIndustrialFire politicallyMotivatedArson : FineFactoryFireState

data BurnedFactorySurface : Set where
  sameBurnedFactory : BurnedFactorySurface

data FireCauseClass : Set where
  accidentalCause politicalArsonCause : FireCauseClass

factorySurface : FineFactoryFireState → BurnedFactorySurface
factorySurface accidentalIndustrialFire = sameBurnedFactory
factorySurface politicallyMotivatedArson = sameBurnedFactory

fireCause : FineFactoryFireState → FireCauseClass
fireCause accidentalIndustrialFire = accidentalCause
fireCause politicallyMotivatedArson = politicalArsonCause

fireCauseDistinct :
  fireCause accidentalIndustrialFire ≡ fireCause politicallyMotivatedArson → ⊥
fireCauseDistinct ()

burnedSurfaceCannotRecoverCause :
  INF.FactorsThrough factorySurface fireCause → ⊥
burnedSurfaceCannotRecoverCause =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      accidentalIndustrialFire politicallyMotivatedArson refl fireCauseDistinct)

------------------------------------------------------------------------
-- Interpretation levels are typed separately.
------------------------------------------------------------------------

data HistoricalMeaningLayer : Set where
  physicalEventLayer
  causalAttributionLayer
  actorMeaningLayer
  officialClassificationLayer
  legalCulpabilityLayer
  laterHistoricalInterpretationLayer
  : HistoricalMeaningLayer

physical≠motive : physicalEventLayer ≡ actorMeaningLayer → ⊥
physical≠motive ()

actorMeaning≠officialClassification :
  actorMeaningLayer ≡ officialClassificationLayer → ⊥
actorMeaning≠officialClassification ()

officialClassification≠laterHistory :
  officialClassificationLayer ≡ laterHistoricalInterpretationLayer → ⊥
officialClassification≠laterHistory ()

------------------------------------------------------------------------
-- Luddite-specific promotion blocks.
------------------------------------------------------------------------

data FactoryFirePromotesArson : Set where
data ArsonPromotesLudditeActor : Set where
data MachineBreakingPromotesAntiTechnologyIdeology : Set where

data OfficialFelonyLabelPromotesCompleteActorMeaning : Set where

factoryFireDoesNotPromoteArson : FactoryFirePromotesArson → ⊥
factoryFireDoesNotPromoteArson ()

arsonDoesNotPromoteLudditeActor : ArsonPromotesLudditeActor → ⊥
arsonDoesNotPromoteLudditeActor ()

machineBreakingDoesNotPromoteAntiTechnologyIdeology :
  MachineBreakingPromotesAntiTechnologyIdeology → ⊥
machineBreakingDoesNotPromoteAntiTechnologyIdeology ()

officialLabelDoesNotPromoteCompleteActorMeaning :
  OfficialFelonyLabelPromotesCompleteActorMeaning → ⊥
officialLabelDoesNotPromoteCompleteActorMeaning ()

record HistoricalEventMeaningBoundary : Set where
  constructor historical-event-meaning-boundary
  field
    eventSurfaceDeterminesCause : Bool
    causeDeterminesActorMeaning : Bool
    officialClassificationEqualsActorMeaning : Bool
    officialClassificationEqualsHistoricalTruth : Bool
    burnedFactoryAutomaticallyMeansLudditeArson : Bool
    machineBreakingAutomaticallyMeansAntiTechnology : Bool

canonicalHistoricalEventMeaningBoundary : HistoricalEventMeaningBoundary
canonicalHistoricalEventMeaningBoundary =
  historical-event-meaning-boundary false false false false false false
