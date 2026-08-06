module DASHI.Biology.ResourceLimitedCrystallisationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact finite fast/slow analogue of nucleation, coarsening, and freeze-out.
-- Threshold control and mobility control are kept distinct: the former changes
-- which phase is favoured, while the latter changes whether the state can move.

data ResourceLevel : Set where
  resourceHigh : ResourceLevel
  resourceMedium : ResourceLevel
  resourceExhausted : ResourceLevel

data PatternStage : Set where
  homogeneousStage : PatternStage
  nucleatedStage : PatternStage
  coarseningStage : PatternStage
  frozenStage : PatternStage

record MaterialState : Set where
  constructor materialState
  field
    resource : ResourceLevel
    stage : PatternStage
    defectCount : Nat

open MaterialState public

mobility : ResourceLevel → Nat
mobility resourceHigh = 2
mobility resourceMedium = 1
mobility resourceExhausted = 0

thresholdFavoursOrder : ResourceLevel → Bool
thresholdFavoursOrder resourceHigh = true
thresholdFavoursOrder resourceMedium = true
thresholdFavoursOrder resourceExhausted = true

nextMaterialState : MaterialState → MaterialState
nextMaterialState (materialState resourceHigh homogeneousStage defects) =
  materialState resourceHigh nucleatedStage defects
nextMaterialState (materialState resourceHigh nucleatedStage zero) =
  materialState resourceMedium coarseningStage zero
nextMaterialState (materialState resourceHigh nucleatedStage (suc defects)) =
  materialState resourceMedium coarseningStage defects
nextMaterialState (materialState resourceHigh coarseningStage zero) =
  materialState resourceMedium coarseningStage zero
nextMaterialState (materialState resourceHigh coarseningStage (suc defects)) =
  materialState resourceMedium coarseningStage defects
nextMaterialState (materialState resourceHigh frozenStage defects) =
  materialState resourceMedium frozenStage defects
nextMaterialState (materialState resourceMedium homogeneousStage defects) =
  materialState resourceMedium nucleatedStage defects
nextMaterialState (materialState resourceMedium nucleatedStage zero) =
  materialState resourceExhausted frozenStage zero
nextMaterialState (materialState resourceMedium nucleatedStage (suc defects)) =
  materialState resourceExhausted frozenStage defects
nextMaterialState (materialState resourceMedium coarseningStage zero) =
  materialState resourceExhausted frozenStage zero
nextMaterialState (materialState resourceMedium coarseningStage (suc defects)) =
  materialState resourceExhausted frozenStage defects
nextMaterialState (materialState resourceMedium frozenStage defects) =
  materialState resourceExhausted frozenStage defects
nextMaterialState (materialState resourceExhausted stageNow defects) =
  materialState resourceExhausted frozenStage defects

initialMaterialState : MaterialState
initialMaterialState = materialState resourceHigh homogeneousStage 3

afterNucleation : MaterialState
afterNucleation = nextMaterialState initialMaterialState

afterCoarsening : MaterialState
afterCoarsening = nextMaterialState afterNucleation

afterFreezeOut : MaterialState
afterFreezeOut = nextMaterialState afterCoarsening

nucleationKeepsInitialDefects : defectCount afterNucleation ≡ 3
nucleationKeepsInitialDefects = refl

coarseningRemovesOneDefect : defectCount afterCoarsening ≡ 2
coarseningRemovesOneDefect = refl

freezeOutRetainsResidualDefect : defectCount afterFreezeOut ≡ 1
freezeOutRetainsResidualDefect = refl

freezeOutHasZeroMobility : mobility (resource afterFreezeOut) ≡ 0
freezeOutHasZeroMobility = refl

freezeOutIsIdempotent :
  nextMaterialState afterFreezeOut ≡ afterFreezeOut
freezeOutIsIdempotent = refl

------------------------------------------------------------------------
-- A finite timescale certificate: freeze-out occurs when the relaxation cost
-- is no smaller than the remaining drive time.

record FreezeOutCertificate : Set where
  constructor freezeOutCertificate
  field
    relaxationTime : Nat
    driveTime : Nat
    driveNoLongerOutrunsRelaxation : driveTime ≤ relaxationTime

open FreezeOutCertificate public

canonicalFreezeOutCertificate : FreezeOutCertificate
canonicalFreezeOutCertificate = freezeOutCertificate 3 2 (s≤s (s≤s z≤n))

------------------------------------------------------------------------
-- Grain boundaries are represented as transition residuals between local
-- orientation charts.  A zero residual glues; a nonzero residual remains.

data LocalOrientation : Set where
  orientationA : LocalOrientation
  orientationB : LocalOrientation
  orientationC : LocalOrientation

orientationMismatch : LocalOrientation → LocalOrientation → Nat
orientationMismatch orientationA orientationA = 0
orientationMismatch orientationB orientationB = 0
orientationMismatch orientationC orientationC = 0
orientationMismatch orientationA orientationB = 1
orientationMismatch orientationB orientationA = 1
orientationMismatch orientationA orientationC = 2
orientationMismatch orientationC orientationA = 2
orientationMismatch orientationB orientationC = 1
orientationMismatch orientationC orientationB = 1

grainBoundaryResidualPersists :
  orientationMismatch orientationA orientationC ≡ 2
grainBoundaryResidualPersists = refl

record ResourceLimitedCrystallisationBoundary : Set where
  constructor resourceLimitedCrystallisationBoundary
  field
    zeroMobilityChangesEnergyOrdering : Bool
    zeroMobilityChangesEnergyOrderingIsFalse :
      zeroMobilityChangesEnergyOrdering ≡ false

    localStabilityImpliesGlobalMinimum : Bool
    localStabilityImpliesGlobalMinimumIsFalse :
      localStabilityImpliesGlobalMinimum ≡ false

    freezeOutErasesAllDefects : Bool
    freezeOutErasesAllDefectsIsFalse :
      freezeOutErasesAllDefects ≡ false

open ResourceLimitedCrystallisationBoundary public

canonicalResourceLimitedCrystallisationBoundary :
  ResourceLimitedCrystallisationBoundary
canonicalResourceLimitedCrystallisationBoundary =
  resourceLimitedCrystallisationBoundary false refl false refl false refl
