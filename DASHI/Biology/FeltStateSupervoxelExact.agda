module DASHI.Biology.FeltStateSupervoxelExact where

open import DASHI.Core.Prelude

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Body
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

------------------------------------------------------------------------
-- FELT STATE AS A COARSE SUPERVOXEL, NOT A BIOCHEMICAL IDENTITY
------------------------------------------------------------------------

record FeltCubie : Set where
  constructor feltCubie
  field
    body : Body.BodyState
    prior : Body.InteroceptivePrior
    localAddress : Hyper.AxisBlock 3

open FeltCubie public

alarmCubieMobilised : FeltCubie
alarmCubieMobilised =
  feltCubie Body.mobilisedBody Body.threatPrior
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-mid
        (Hyper.block-cons Hyper.axis-low Hyper.block-root)))

alarmCubieProlonged : FeltCubie
alarmCubieProlonged =
  feltCubie Body.prolongedLoadBody Body.threatPrior
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-high
        (Hyper.block-cons Hyper.axis-low Hyper.block-root)))

samePhysiologySafetyPrior : FeltCubie
samePhysiologySafetyPrior =
  feltCubie Body.mobilisedBody Body.safetyPrior
    (Hyper.block-cons Hyper.axis-mid
      (Hyper.block-cons Hyper.axis-high
        (Hyper.block-cons Hyper.axis-mid Hyper.block-root)))

feltProjection : FeltCubie → Body.FeltState
feltProjection cubie =
  Body.inferFeltState (prior cubie) (Body.afference (body cubie))

mobilisedThreatProjectsAlarm :
  feltProjection alarmCubieMobilised ≡ Body.alarmedFeeling
mobilisedThreatProjectsAlarm = refl

prolongedThreatProjectsAlarm :
  feltProjection alarmCubieProlonged ≡ Body.alarmedFeeling
prolongedThreatProjectsAlarm = refl

sameAlarmDifferentPhysiology :
  alarmCubieMobilised ≡ alarmCubieProlonged → ⊥
sameAlarmDifferentPhysiology ()

samePhysiologyDifferentPriorChangesFeltState :
  feltProjection alarmCubieMobilised
  ≡ feltProjection samePhysiologySafetyPrior → ⊥
samePhysiologyDifferentPriorChangesFeltState ()

record FeltSupervoxel : Set where
  constructor feltSupervoxel
  field
    coarseFeeling : Body.FeltState
    firstCubie secondCubie : FeltCubie
    firstProjectsToCoarse : feltProjection firstCubie ≡ coarseFeeling
    secondProjectsToCoarse : feltProjection secondCubie ≡ coarseFeeling

alarmSupervoxel : FeltSupervoxel
alarmSupervoxel =
  feltSupervoxel
    Body.alarmedFeeling
    alarmCubieMobilised
    alarmCubieProlonged
    refl
    refl

record FeltSupervoxelBoundary : Set where
  constructor feltSupervoxelBoundary
  field
    alarmEqualsOneBodyState : Bool
    physiologyAloneDeterminesFeeling : Bool
    sameFeelingCanContainDifferentFineCubies : Bool
    localCubieExhaustsPhenomenology : Bool

canonicalFeltSupervoxelBoundary : FeltSupervoxelBoundary
canonicalFeltSupervoxelBoundary =
  feltSupervoxelBoundary false false true false
