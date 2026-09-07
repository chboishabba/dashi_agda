module DASHI.Culture.DialecticLevelsAestheticConsumerFibreCrossPollinationExact where

------------------------------------------------------------------------
-- DIALECTIC / LEVELS / AESTHETIC CONSUMER-FIBRE CROSS-POLLINATION
--
-- This module adds no external historical or empirical proposition.  It reuses
-- already-source-bounded owners and the generic DASHI non-factorability theorem
-- to make three representation failures executable:
--
--   contradiction-present != full dialectic architecture
--   one level label != full developmental profile
--   gaze/liking surface != full aesthetic/value state
--
-- The finite collision witnesses below are DASHI synthetic countermodels.  They
-- show insufficiency of a coarse observer for a declared consumer; they are not
-- population claims about people, artworks, Hegel, or hoe_math.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Culture.DASHIDialecticGenealogyAttributionCorrectionExact as Genealogy
import DASHI.Culture.HegelDialecticPrimarySourceBoundaryExact as Hegel
import DASHI.Culture.HoeMathLevelsSourceBoundaryExact as Levels
import DASHI.Culture.AestheticPerceptionEyeTrackingSourceBoundaryExact as Aesthetics

------------------------------------------------------------------------
-- 1. Dialectic: the coarse fact "contradiction is present" cannot by itself
-- recover whether the downstream architecture is Hegel's selected self-movement
-- lane or DASHI's independently-developed residual/reopening lane.
------------------------------------------------------------------------

data DialecticComparisonState : Set where
  hegelContradictionSelfMovementState
  dashiContradictionResidualReopeningState
  : DialecticComparisonState

data ContradictionSurface : Set where
  contradictionPresent : ContradictionSurface

observeContradiction : DialecticComparisonState → ContradictionSurface
observeContradiction hegelContradictionSelfMovementState = contradictionPresent
observeContradiction dashiContradictionResidualReopeningState = contradictionPresent

data ResidualReopeningOwnership : Set where
  notOwnedBySelectedHegelPassages
  ownedByDASHIArchitecture
  : ResidualReopeningOwnership

residualReopeningConsumer : DialecticComparisonState → ResidualReopeningOwnership
residualReopeningConsumer hegelContradictionSelfMovementState = notOwnedBySelectedHegelPassages
residualReopeningConsumer dashiContradictionResidualReopeningState = ownedByDASHIArchitecture

residualOwnershipDiffers :
  residualReopeningConsumer hegelContradictionSelfMovementState ≡
  residualReopeningConsumer dashiContradictionResidualReopeningState → ⊥
residualOwnershipDiffers ()

contradictionSurfaceDoesNotFactorResidualArchitecture :
  NF.NonFactorabilityWitness observeContradiction residualReopeningConsumer
contradictionSurfaceDoesNotFactorResidualArchitecture =
  NF.nonFactorabilityWitness
    hegelContradictionSelfMovementState
    dashiContradictionResidualReopeningState
    refl
    residualOwnershipDiffers

contradictionAloneCannotRecoverResidualArchitecture :
  NF.FactorsThrough observeContradiction residualReopeningConsumer → ⊥
contradictionAloneCannotRecoverResidualArchitecture =
  NF.witnessRulesOutEveryFlatFactorisation
    contradictionSurfaceDoesNotFactorResidualArchitecture

------------------------------------------------------------------------
-- 2. Levels: one scalar/stage label can collide while a separately modelled
-- developmental line differs.  This is a structural countermodel matching the
-- source boundary's distinction between levels and independently developing
-- lines; it is not an empirical claim that any named person occupies a state.
------------------------------------------------------------------------

data DevelopmentProfileState : Set where
  sameLevelLineLow
  sameLevelLineHigh
  : DevelopmentProfileState

data SimplifiedLevelLabel : Set where
  sameSimplifiedLevel : SimplifiedLevelLabel

observeSimplifiedLevel : DevelopmentProfileState → SimplifiedLevelLabel
observeSimplifiedLevel sameLevelLineLow = sameSimplifiedLevel
observeSimplifiedLevel sameLevelLineHigh = sameSimplifiedLevel

data DevelopmentalLineState : Set where
  lineLower lineHigher : DevelopmentalLineState

developmentalLineConsumer : DevelopmentProfileState → DevelopmentalLineState
developmentalLineConsumer sameLevelLineLow = lineLower
developmentalLineConsumer sameLevelLineHigh = lineHigher

lineStateDiffers :
  developmentalLineConsumer sameLevelLineLow ≡
  developmentalLineConsumer sameLevelLineHigh → ⊥
lineStateDiffers ()

singleLevelDoesNotFactorDevelopmentalLine :
  NF.NonFactorabilityWitness observeSimplifiedLevel developmentalLineConsumer
singleLevelDoesNotFactorDevelopmentalLine =
  NF.nonFactorabilityWitness sameLevelLineLow sameLevelLineHigh refl lineStateDiffers

singleLevelCannotRecoverFullLineState :
  NF.FactorsThrough observeSimplifiedLevel developmentalLineConsumer → ⊥
singleLevelCannotRecoverFullLineState =
  NF.witnessRulesOutEveryFlatFactorisation singleLevelDoesNotFactorDevelopmentalLine

-- Any relabelling, score transform, or reweighting of the already-coarse level
-- observer remains insufficient for the line consumer.
singleLevelRechartCannotRecoverLine :
  ∀ {Recharted : Set} →
  (rechart : SimplifiedLevelLabel → Recharted) →
  NF.FactorsThrough
    (λ state → rechart (observeSimplifiedLevel state))
    developmentalLineConsumer →
  ⊥
singleLevelRechartCannotRecoverLine rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart singleLevelDoesNotFactorDevelopmentalLine

------------------------------------------------------------------------
-- 3. Aesthetics: gaze is a measured behavioural surface, not a sufficient
-- carrier for subjective evaluation; and even gaze + personal liking is not a
-- sufficient carrier for institutional status or market value.
------------------------------------------------------------------------

data AestheticWorld : Set where
  sameGazeLowLiking
  sameGazeHighLiking
  sameGazeLikingOutsideInstitution
  sameGazeLikingInsideInstitution
  sameGazeLikingLowPrice
  sameGazeLikingHighPrice
  : AestheticWorld

data GazeCode : Set where
  sameGaze : GazeCode

observeGaze : AestheticWorld → GazeCode
observeGaze _ = sameGaze

data LikingCode : Set where
  lowLiking highLiking : LikingCode

likingConsumer : AestheticWorld → LikingCode
likingConsumer sameGazeLowLiking = lowLiking
likingConsumer sameGazeHighLiking = highLiking
likingConsumer sameGazeLikingOutsideInstitution = highLiking
likingConsumer sameGazeLikingInsideInstitution = highLiking
likingConsumer sameGazeLikingLowPrice = highLiking
likingConsumer sameGazeLikingHighPrice = highLiking

likingDiffersAtSameGaze :
  likingConsumer sameGazeLowLiking ≡ likingConsumer sameGazeHighLiking → ⊥
likingDiffersAtSameGaze ()

gazeDoesNotFactorLiking :
  NF.NonFactorabilityWitness observeGaze likingConsumer
gazeDoesNotFactorLiking =
  NF.nonFactorabilityWitness
    sameGazeLowLiking
    sameGazeHighLiking
    refl
    likingDiffersAtSameGaze

data GazeLikingSurface : Set where
  sameGazeAndHighLiking : GazeLikingSurface

observeGazeAndLiking : AestheticWorld → GazeLikingSurface
observeGazeAndLiking _ = sameGazeAndHighLiking

data InstitutionalStatus : Set where
  outsideInstitution insideInstitution : InstitutionalStatus

institutionalStatusConsumer : AestheticWorld → InstitutionalStatus
institutionalStatusConsumer sameGazeLowLiking = outsideInstitution
institutionalStatusConsumer sameGazeHighLiking = outsideInstitution
institutionalStatusConsumer sameGazeLikingOutsideInstitution = outsideInstitution
institutionalStatusConsumer sameGazeLikingInsideInstitution = insideInstitution
institutionalStatusConsumer sameGazeLikingLowPrice = outsideInstitution
institutionalStatusConsumer sameGazeLikingHighPrice = outsideInstitution

institutionalStatusDiffers :
  institutionalStatusConsumer sameGazeLikingOutsideInstitution ≡
  institutionalStatusConsumer sameGazeLikingInsideInstitution → ⊥
institutionalStatusDiffers ()

gazeLikingDoesNotFactorInstitutionalStatus :
  NF.NonFactorabilityWitness observeGazeAndLiking institutionalStatusConsumer
gazeLikingDoesNotFactorInstitutionalStatus =
  NF.nonFactorabilityWitness
    sameGazeLikingOutsideInstitution
    sameGazeLikingInsideInstitution
    refl
    institutionalStatusDiffers

data MarketValueBand : Set where
  lowMarketValue highMarketValue : MarketValueBand

marketValueConsumer : AestheticWorld → MarketValueBand
marketValueConsumer sameGazeLowLiking = lowMarketValue
marketValueConsumer sameGazeHighLiking = lowMarketValue
marketValueConsumer sameGazeLikingOutsideInstitution = lowMarketValue
marketValueConsumer sameGazeLikingInsideInstitution = lowMarketValue
marketValueConsumer sameGazeLikingLowPrice = lowMarketValue
marketValueConsumer sameGazeLikingHighPrice = highMarketValue

marketValueDiffers :
  marketValueConsumer sameGazeLikingLowPrice ≡
  marketValueConsumer sameGazeLikingHighPrice → ⊥
marketValueDiffers ()

gazeLikingDoesNotFactorMarketValue :
  NF.NonFactorabilityWitness observeGazeAndLiking marketValueConsumer
gazeLikingDoesNotFactorMarketValue =
  NF.nonFactorabilityWitness
    sameGazeLikingLowPrice
    sameGazeLikingHighPrice
    refl
    marketValueDiffers

------------------------------------------------------------------------
-- 4. Shared theorem shape.
--
-- A coarse observation may be perfectly real and useful while remaining
-- insufficient for a different consumer.  The missing coordinate must be added
-- upstream; post-hoc reweighting of the coarse quotient cannot recreate it.
------------------------------------------------------------------------

data CoarseObservationIsFalseBecauseInsufficient : Set where
data ConsumerMismatchMeansRelativism : Set where
data MultiCoordinateStateMeansNoComparisonPossible : Set where

coarseObservationNeedNotBeFalse : CoarseObservationIsFalseBecauseInsufficient → ⊥
coarseObservationNeedNotBeFalse ()

consumerMismatchDoesNotMeanRelativism : ConsumerMismatchMeansRelativism → ⊥
consumerMismatchDoesNotMeanRelativism ()

multiCoordinateDoesNotMeanNoComparison : MultiCoordinateStateMeansNoComparisonPossible → ⊥
multiCoordinateDoesNotMeanNoComparison ()

------------------------------------------------------------------------
-- 5. Provenance / source-boundary weld.
------------------------------------------------------------------------

record DialecticLevelsAestheticConsumerFibreBoundary : Set where
  constructor dialectic-levels-aesthetic-consumer-fibre-boundary
  field
    genealogyBoundary : Genealogy.DASHIDialecticGenealogyCorrection
    hegelBoundary : Hegel.HegelDialecticPrimarySourceBoundary
    levelsBoundary : Levels.HoeMathLevelsSourceBoundary
    aestheticBoundary : Aesthetics.AestheticPerceptionEyeTrackingBoundary
    contradictionCollisionOwned : Bool
    levelCollisionOwned : Bool
    gazeLikingCollisionOwned : Bool
    gazeLikingInstitutionCollisionOwned : Bool
    gazeLikingMarketCollisionOwned : Bool
    syntheticWitnessesPromotedToEmpiricalPopulationClaims : Bool
    coarseObserverDeclaredFalse : Bool
    consumerSpecificAdequacyPreserved : Bool

canonicalDialecticLevelsAestheticConsumerFibreBoundary :
  DialecticLevelsAestheticConsumerFibreBoundary
canonicalDialecticLevelsAestheticConsumerFibreBoundary =
  dialectic-levels-aesthetic-consumer-fibre-boundary
    Genealogy.canonicalDASHIDialecticGenealogyCorrection
    Hegel.canonicalHegelDialecticPrimarySourceBoundary
    Levels.canonicalHoeMathLevelsSourceBoundary
    Aesthetics.canonicalAestheticPerceptionEyeTrackingBoundary
    true true true true true false false true
