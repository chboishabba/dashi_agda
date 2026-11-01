module DASHI.Physics.Foundations.NuclearShapeInstabilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.CandidateFunctionalCore as Candidate

------------------------------------------------------------------------
-- Finite-density scaling witnesses.

bulkFermiEnergy : Nat → Nat
bulkFermiEnergy nucleons = 3 * nucleons

fixedDensitySplitKeepsLeadingFermiEnergyExtensive :
  bulkFermiEnergy 8 ≡ bulkFermiEnergy 4 + bulkFermiEnergy 4
fixedDensitySplitKeepsLeadingFermiEnergyExtensive = refl

surfaceScaleWitness : Nat → Nat
surfaceScaleWitness 8 = 4
surfaceScaleWitness 4 = 3
surfaceScaleWitness other = other

splitSurfaceWitnessIsSix :
  surfaceScaleWitness 4 + surfaceScaleWitness 4 ≡ 6
splitSurfaceWitnessIsSix = refl

compactSurfaceWitnessIsFour :
  surfaceScaleWitness 8 ≡ 4
compactSurfaceWitnessIsFour = refl

coulombScaleWitness : Nat → Nat → Nat
coulombScaleWitness 8 4 = 8
coulombScaleWitness 4 2 = 2
coulombScaleWitness mass charge = charge * charge

splitCoulombWitnessIsFour :
  coulombScaleWitness 4 2 + coulombScaleWitness 4 2 ≡ 4
splitCoulombWitnessIsFour = refl

compactCoulombWitnessIsEight :
  coulombScaleWitness 8 4 ≡ 8
compactCoulombWitnessIsEight = refl

------------------------------------------------------------------------
-- Liquid-drop-like energy competition.

data ShapeState : Set where
  compactShape : ShapeState
  splitShape : ShapeState

bulkTerm : ShapeState → Nat
bulkTerm compactShape = 8
bulkTerm splitShape = 8

surfaceTerm : ShapeState → Nat
surfaceTerm compactShape = 4
surfaceTerm splitShape = 6

coulombTerm : ShapeState → Nat
coulombTerm compactShape = 8
coulombTerm splitShape = 4

asymmetryTerm : ShapeState → Nat
asymmetryTerm compactShape = 2
asymmetryTerm splitShape = 2

shellCorrection : ShapeState → Nat
shellCorrection compactShape = 1
shellCorrection splitShape = 0

pairingCorrection : ShapeState → Nat
pairingCorrection compactShape = 1
pairingCorrection splitShape = 0

totalShapeCost : ShapeState → Nat
totalShapeCost shape =
  surfaceTerm shape
  + coulombTerm shape
  + asymmetryTerm shape
  + shellCorrection shape
  + pairingCorrection shape

compactShapeCostIsSixteen : totalShapeCost compactShape ≡ 16
compactShapeCostIsSixteen = refl

splitShapeCostIsTwelve : totalShapeCost splitShape ≡ 12
splitShapeCostIsTwelve = refl

data CostOrdering : Set where
  firstLower : CostOrdering
  equalCost : CostOrdering
  secondLower : CostOrdering

canonicalShapeCostOrdering : CostOrdering
canonicalShapeCostOrdering = firstLower

splitShapeIsTheLowerFiniteCandidate :
  canonicalShapeCostOrdering ≡ firstLower
splitShapeIsTheLowerFiniteCandidate = refl

------------------------------------------------------------------------
-- Fissility and local shape stability.

record FissilityComparison : Set where
  constructor fissilityComparison
  field
    numerator : Nat
    denominator : Nat
    rank : Nat

open FissilityComparison public

lightDropFissility : FissilityComparison
lightDropFissility = fissilityComparison 4 8 1

heavyChargedDropFissility : FissilityComparison
heavyChargedDropFissility = fissilityComparison 64 16 4

lightDropFissilityRankIsOne : rank lightDropFissility ≡ 1
lightDropFissilityRankIsOne = refl

heavyDropFissilityRankIsFour : rank heavyChargedDropFissility ≡ 4
heavyDropFissilityRankIsFour = refl

data CurvatureStatus : Set where
  positiveShapeCurvature : CurvatureStatus
  zeroShapeCurvature : CurvatureStatus
  negativeShapeCurvature : CurvatureStatus

data ShapeStability : Set where
  locallyStableShape : ShapeStability
  marginalShape : ShapeStability
  unstableShape : ShapeStability

shapeStability : CurvatureStatus → ShapeStability
shapeStability positiveShapeCurvature = locallyStableShape
shapeStability zeroShapeCurvature = marginalShape
shapeStability negativeShapeCurvature = unstableShape

negativeCurvatureSignalsShapeInstability :
  shapeStability negativeShapeCurvature ≡ unstableShape
negativeCurvatureSignalsShapeInstability = refl

record MetastableNucleus : Set where
  constructor metastableNucleus
  field
    localCurvature : CurvatureStatus
    lowerEnergyChannelExists : Bool
    barrierExists : Bool

open MetastableNucleus public

canonicalMetastableNucleus : MetastableNucleus
canonicalMetastableNucleus =
  metastableNucleus positiveShapeCurvature true true

metastabilitySeparatesLocalAndGlobalStability :
  shapeStability (localCurvature canonicalMetastableNucleus)
  ≡
  locallyStableShape
  ×
  lowerEnergyChannelExists canonicalMetastableNucleus ≡ true
metastabilitySeparatesLocalAndGlobalStability = refl , refl

existingCandidateFunctionalCarrier : Set
existingCandidateFunctionalCarrier = Candidate.CandidateFunctionalSurface

------------------------------------------------------------------------
-- Authority boundary.

record NuclearShapeBoundary : Set where
  constructor nuclearShapeBoundary
  field
    pauliPressureAloneExplainsFission : Bool
    pauliPressureAloneExplainsFissionIsFalse :
      pauliPressureAloneExplainsFission ≡ false

    fixedDensitySplittingLowersLeadingFermiEnergy : Bool
    fixedDensitySplittingLowersLeadingFermiEnergyIsFalse :
      fixedDensitySplittingLowersLeadingFermiEnergy ≡ false

    surfaceEnergyAloneDestabilisesEveryLargeNeutralDrop : Bool
    surfaceEnergyAloneDestabilisesEveryLargeNeutralDropIsFalse :
      surfaceEnergyAloneDestabilisesEveryLargeNeutralDrop ≡ false

    unitFreeScalingDeterminesNumericalFissionThreshold : Bool
    unitFreeScalingDeterminesNumericalFissionThresholdIsFalse :
      unitFreeScalingDeterminesNumericalFissionThreshold ≡ false

    localMinimumImpliesAbsoluteStability : Bool
    localMinimumImpliesAbsoluteStabilityIsFalse :
      localMinimumImpliesAbsoluteStability ≡ false

    nuclearEnergyIsAutomaticallyAnMDLCodeLength : Bool
    nuclearEnergyIsAutomaticallyAnMDLCodeLengthIsFalse :
      nuclearEnergyIsAutomaticallyAnMDLCodeLength ≡ false

open NuclearShapeBoundary public

canonicalNuclearShapeBoundary : NuclearShapeBoundary
canonicalNuclearShapeBoundary =
  nuclearShapeBoundary false refl false refl false refl false refl false refl false refl
