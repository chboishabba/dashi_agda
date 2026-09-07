module DASHI.Culture.DialecticLevelsAestheticConsumerFibreCrossPollinationExact where

------------------------------------------------------------------------
-- DIALECTIC / LEVELS / AESTHETIC x INTERSECTIONALITY APPLICATION
--
-- CORRECTION / CANONICAL OWNER:
-- The general theorem shape here is NOT new to this tranche.  The repository
-- already owns it through:
--
--   DASHI.Core.IntersectionalNonFactorability
--   DASHI.Core.IntersectionalConstraintGeometryExact
--
-- Crenshaw's 1989/1991 work is the conceptual source for the intersectional
-- warning that a situated joint relation need not be reconstructible from
-- separately modelled/coarse single-axis surfaces.  The factorisation,
-- recharting and finite interaction theorems are DASHI mathematical
-- translations owned by those canonical Core modules, not by Hegel, hoe_math,
-- aesthetic-psychology authors, or this application module.
--
-- This file therefore does ONLY application work: it instantiates those
-- existing intersectionality owners on already-source-bounded dialectic,
-- developmental-level and aesthetic coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.IntersectionalConstraintGeometryExact as ICG
import DASHI.Culture.DASHIDialecticGenealogyAttributionCorrectionExact as Genealogy
import DASHI.Culture.HegelDialecticPrimarySourceBoundaryExact as Hegel
import DASHI.Culture.HoeMathLevelsSourceBoundaryExact as Levels
import DASHI.Culture.AestheticPerceptionEyeTrackingSourceBoundaryExact as Aesthetics

------------------------------------------------------------------------
-- 1. Dialectic application.
------------------------------------------------------------------------

data DialecticComparisonState : Set where
  hegelContradictionSelfMovementState
  dashiContradictionResidualReopeningState
  : DialecticComparisonState

data ContradictionSurface : Set where contradictionPresent : ContradictionSurface

observeContradiction : DialecticComparisonState → ContradictionSurface
observeContradiction _ = contradictionPresent

data ResidualReopeningOwnership : Set where
  notOwnedBySelectedHegelPassages
  ownedByDASHIArchitecture
  : ResidualReopeningOwnership

residualReopeningConsumer : DialecticComparisonState → ResidualReopeningOwnership
residualReopeningConsumer hegelContradictionSelfMovementState =
  notOwnedBySelectedHegelPassages
residualReopeningConsumer dashiContradictionResidualReopeningState =
  ownedByDASHIArchitecture

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
    refl residualOwnershipDiffers

contradictionAloneCannotRecoverResidualArchitecture :
  NF.FactorsThrough observeContradiction residualReopeningConsumer → ⊥
contradictionAloneCannotRecoverResidualArchitecture =
  NF.witnessRulesOutEveryFlatFactorisation
    contradictionSurfaceDoesNotFactorResidualArchitecture

------------------------------------------------------------------------
-- 2. Levels application.
--
-- This is exactly the intersectional warning in a different domain: a coarse
-- single coordinate can remain fixed while a relevant joint/other coordinate
-- changes.  It does NOT claim hoe_math's Levels model is intersectionality, nor
-- that Crenshaw authored developmental-stage theory.
------------------------------------------------------------------------

data DevelopmentProfileState : Set where
  sameLevelLineLow sameLevelLineHigh : DevelopmentProfileState

data SimplifiedLevelLabel : Set where sameSimplifiedLevel : SimplifiedLevelLabel

observeSimplifiedLevel : DevelopmentProfileState → SimplifiedLevelLabel
observeSimplifiedLevel _ = sameSimplifiedLevel

data DevelopmentalLineState : Set where lineLower lineHigher : DevelopmentalLineState

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

singleLevelRechartCannotRecoverLine :
  ∀ {Recharted : Set} →
  (rechart : SimplifiedLevelLabel → Recharted) →
  NF.FactorsThrough
    (λ state → rechart (observeSimplifiedLevel state))
    developmentalLineConsumer → ⊥
singleLevelRechartCannotRecoverLine rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart singleLevelDoesNotFactorDevelopmentalLine

------------------------------------------------------------------------
-- 3. Aesthetic application.
------------------------------------------------------------------------

data AestheticWorld : Set where
  sameGazeLowLiking
  sameGazeHighLiking
  sameGazeLikingOutsideInstitution
  sameGazeLikingInsideInstitution
  sameGazeLikingLowPrice
  sameGazeLikingHighPrice
  : AestheticWorld

data GazeCode : Set where sameGaze : GazeCode
observeGaze : AestheticWorld → GazeCode
observeGaze _ = sameGaze

data LikingCode : Set where lowLiking highLiking : LikingCode

likingConsumer : AestheticWorld → LikingCode
likingConsumer sameGazeLowLiking = lowLiking
likingConsumer _ = highLiking

likingDiffersAtSameGaze :
  likingConsumer sameGazeLowLiking ≡ likingConsumer sameGazeHighLiking → ⊥
likingDiffersAtSameGaze ()

gazeDoesNotFactorLiking : NF.NonFactorabilityWitness observeGaze likingConsumer
gazeDoesNotFactorLiking =
  NF.nonFactorabilityWitness
    sameGazeLowLiking sameGazeHighLiking refl likingDiffersAtSameGaze

data GazeLikingSurface : Set where sameGazeAndHighLiking : GazeLikingSurface
observeGazeAndLiking : AestheticWorld → GazeLikingSurface
observeGazeAndLiking _ = sameGazeAndHighLiking

data InstitutionalStatus : Set where outsideInstitution insideInstitution : InstitutionalStatus

institutionalStatusConsumer : AestheticWorld → InstitutionalStatus
institutionalStatusConsumer sameGazeLikingInsideInstitution = insideInstitution
institutionalStatusConsumer _ = outsideInstitution

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
    refl institutionalStatusDiffers

data MarketValueBand : Set where lowMarketValue highMarketValue : MarketValueBand

marketValueConsumer : AestheticWorld → MarketValueBand
marketValueConsumer sameGazeLikingHighPrice = highMarketValue
marketValueConsumer _ = lowMarketValue

marketValueDiffers :
  marketValueConsumer sameGazeLikingLowPrice ≡
  marketValueConsumer sameGazeLikingHighPrice → ⊥
marketValueDiffers ()

gazeLikingDoesNotFactorMarketValue :
  NF.NonFactorabilityWitness observeGazeAndLiking marketValueConsumer
gazeLikingDoesNotFactorMarketValue =
  NF.nonFactorabilityWitness
    sameGazeLikingLowPrice sameGazeLikingHighPrice refl marketValueDiffers

------------------------------------------------------------------------
-- 4. Canonical intersectionality pins.
------------------------------------------------------------------------

intersectionalityAlreadyOwnsSingleAxisNonFactorability :
  NF.FactorsThrough ICG.sexualityAxis ICG.jointConstraint → ⊥
intersectionalityAlreadyOwnsSingleAxisNonFactorability =
  ICG.sexualityAxisCannotRecoverJointConstraint

intersectionalityAlreadyOwnsRechartingNoRepair :
  ∀ {Chart : Set} →
  (rechart : ICG.SexualityAxisObservation → Chart) →
  NF.FactorsThrough
    (λ state → rechart (ICG.sexualityAxis state))
    ICG.jointConstraint → ⊥
intersectionalityAlreadyOwnsRechartingNoRepair =
  ICG.rechartedSexualityAxisCannotRecoverJointConstraint

intersectionalityAlreadyOwnsNonlinearInteraction :
  ICG.marginalPublicRecognition ICG.jointAxes ≡
  ICG.interactionPublicRecognition ICG.jointAxes → ⊥
intersectionalityAlreadyOwnsNonlinearInteraction =
  ICG.jointInteractionIsNotRecoveredByMarginalConjunction

------------------------------------------------------------------------
-- 5. Attribution / non-collapse.
------------------------------------------------------------------------

data ApplicationMakesCrenshawAuthorOfHegel : Set where
data ApplicationMakesCrenshawAuthorOfLevels : Set where
data ApplicationMakesCrenshawAuthorOfAesthetics : Set where
data ApplicationMakesHegelAuthorOfIntersectionality : Set where
data SharedFormalShapeMeansSharedDoctrine : Set where

crenshawNotMadeAuthorOfHegel : ApplicationMakesCrenshawAuthorOfHegel → ⊥
crenshawNotMadeAuthorOfHegel ()
crenshawNotMadeAuthorOfLevels : ApplicationMakesCrenshawAuthorOfLevels → ⊥
crenshawNotMadeAuthorOfLevels ()
crenshawNotMadeAuthorOfAesthetics : ApplicationMakesCrenshawAuthorOfAesthetics → ⊥
crenshawNotMadeAuthorOfAesthetics ()
hegelNotMadeAuthorOfIntersectionality : ApplicationMakesHegelAuthorOfIntersectionality → ⊥
hegelNotMadeAuthorOfIntersectionality ()
sharedFormalShapeDoesNotMeanSharedDoctrine : SharedFormalShapeMeansSharedDoctrine → ⊥
sharedFormalShapeDoesNotMeanSharedDoctrine ()

record DialecticLevelsAestheticConsumerFibreBoundary : Set where
  constructor dialectic-levels-aesthetic-consumer-fibre-boundary
  field
    canonicalIntersectionalGeometry : ICG.IntersectionalConstraintGeometryBoundary
    genealogyBoundary : Genealogy.DASHIDialecticGenealogyCorrection
    hegelBoundary : Hegel.HegelDialecticPrimarySourceBoundary
    levelsBoundary : Levels.HoeMathLevelsSourceBoundary
    aestheticBoundary : Aesthetics.AestheticPerceptionEyeTrackingBoundary
    generalNonFactorabilityAlreadyOwnedUpstream : Bool
    rechartingNoRepairAlreadyOwnedUpstream : Bool
    nonlinearInteractionAlreadyOwnedUpstream : Bool
    thisModuleAddsOnlyDomainInstantiations : Bool
    syntheticWitnessesPromotedToEmpiricalPopulationClaims : Bool
    sharedShapePromotedToSharedDoctrine : Bool

canonicalDialecticLevelsAestheticConsumerFibreBoundary :
  DialecticLevelsAestheticConsumerFibreBoundary
canonicalDialecticLevelsAestheticConsumerFibreBoundary =
  dialectic-levels-aesthetic-consumer-fibre-boundary
    ICG.canonicalIntersectionalConstraintGeometryBoundary
    Genealogy.canonicalDASHIDialecticGenealogyCorrection
    Hegel.canonicalHegelDialecticPrimarySourceBoundary
    Levels.canonicalHoeMathLevelsSourceBoundary
    Aesthetics.canonicalAestheticPerceptionEyeTrackingBoundary
    true true true true false false
