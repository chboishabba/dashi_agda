module DASHI.Biology.ConsciousAccessRound3ExtendedRegression where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Biology.ConsciousAccessRound3Regression as CoreRegression
import DASHI.Biology.ConsciousAccessRound3FullBoundary as Full
import DASHI.Biology.NaturalGrowthAlgorithmAtlas as Growth
import DASHI.Biology.SquareApollonianPackingComparison as Packing
import DASHI.Biology.SignedDistanceBooleanGeometry as SDF
import DASHI.Biology.HallHybridManifoldTreeCarrier as Hybrid
import DASHI.Biology.PsychedelicAttractorReweightingBoundary as Attractor
import DASHI.Biology.VisualPathBraidResidual as Braid
import DASHI.Biology.QuantitativeStateDynamics as Quantitative
import DASHI.Biology.SymbolicCompromiseMinimizer as Symbolic
import DASHI.Biology.StableUnconsciousInvariantRegime as Unconscious
import DASHI.Biology.DynamicCoalitionPhaseEmergence as Phases

record ConsciousAccessRound3ExtendedRegression : Setω where
  field
    coreRegression :
      CoreRegression.ConsciousAccessRound3Regression

    lSystemBranches :
      Growth.firstLSystemGeneration
      ≡
      Growth.internodeSymbol
      ∷ Growth.leftBranchSymbol
      ∷ Growth.apexSymbol
      ∷ Growth.rightBranchSymbol
      ∷ Growth.apexSymbol
      ∷ []

    spaceColonisationSelectsMaximalTip :
      (t : Growth.GrowthTip) →
      Growth.attractionCount t
      ≤
      Growth.attractionCount Growth.selectedColonisingTip

    phyllotaxisSelectsMaximalSite :
      (s : Growth.PrimordiumSite) →
      Growth.phyllotacticScore s
      ≤
      Growth.phyllotacticScore Growth.selectedPrimordiumSite

    edenSelectsMaximalFrontier :
      (c : Growth.FrontierCell) →
      Growth.occupiedNeighbourCount c
      ≤
      Growth.occupiedNeighbourCount Growth.selectedEdenCell

    diffusionWalkerSticks :
      Growth.stickAt
        (Growth.walkerStep
          (Growth.walkerStep Growth.farPosition))
        Growth.seedAggregate
      ≡
      Growth.grownAggregate

    squareAndApollonianSignaturesDiffer :
      Packing.packingSignatureOf Packing.squarePackingFamily
      ≡
      Packing.packingSignatureOf Packing.apollonianSphereFamily
      →
      ⊥

    descartesIdentity :
      Packing.squareNat Packing.descartesSignedSum
      ≡
      2 * Packing.descartesSquareSum

    soddyGossetIdentity :
      Packing.squareNat Packing.soddyGossetSignedSum
      ≡
      3 * Packing.soddyGossetSquareSum

    hybridCarriesSquareAndTangency :
      Packing.globalTranslationPeriodicity
        (Packing.packingSignatureOf
          Packing.squareSeededApollonianFamily)
      ≡
      true
      ×
      Packing.localTangencyLaw
        (Packing.packingSignatureOf
          Packing.squareSeededApollonianFamily)
      ≡
      true

    sphereInteriorIsBooleanRemoved :
      SDF.perforatedRoomSign SDF.sphereInteriorSample
      ≡
      SDF.outsideSign

    repeatedDomainReturnsOriginCell :
      SDF.repeatToFundamentalCell SDF.coordinateTwo
      ≡
      SDF.cellZero

    hybridCrossBranchDistanceIsThree :
      Hybrid.hybridDistance
        Hybrid.habitualChartOrigin
        Hybrid.crossBranchNeighbour
      ≡
      3

    hybridLocalMovePreservesBranch :
      Hybrid.branchAddress
        (Hybrid.applyHybridTransition
          Hybrid.localDeformationTransition
          Hybrid.habitualChartOrigin)
      ≡
      Attractor.habitualAddress

    visualHistoryResidualIsOne :
      Braid.historyResidual
        Braid.inhibitionThenCompletion
        Braid.completionThenInhibition
        false
      ≡
      1

    amplifiedMagnitudeIsThree :
      Quantitative.magnitude
        (Quantitative.respond true Quantitative.amplifiedRegime)
      ≡
      3

    delayedResponseReleasesPending :
      Quantitative.magnitude
        (proj₁
          (Quantitative.quantitativeStep false
            (proj₂
              (Quantitative.quantitativeStep true
                Quantitative.initialDelayedCell))))
      ≡
      1

    symbolicMinimumExists :
      (candidate : Symbolic.SymbolCandidate) →
      Symbolic.symbolObjective true Symbolic.transformedCandidate
      ≤
      Symbolic.symbolObjective true candidate

    symbolicMinimumNeedNotBeUnique :
      Symbolic.symbolObjective true Symbolic.alternateTransformedCandidate
      ≡
      1

    unconsciousBlockingStable :
      (p : Unconscious.LocalPerturbation) →
      Unconscious.accessBlocked p true ≡ true

    unconsciousCarrierStillCausal :
      (p : Unconscious.LocalPerturbation) →
      Unconscious.actionInfluence p true
      ≡
      Unconscious.actionInfluence p false
      →
      ⊥

    coalitionFivePhaseReturn :
      Phases.classifyPhase
        (Phases.snapshotStep
          (Phases.snapshotStep
            (Phases.snapshotStep
              (Phases.snapshotStep
                (Phases.snapshotStep Phases.recruitmentSnapshot)))))
      ≡
      Phases.recruitmentPhase

    completeBoundary :
      Full.ConsciousAccessRound3FullBoundary

open ConsciousAccessRound3ExtendedRegression public

canonicalConsciousAccessRound3ExtendedRegression :
  ConsciousAccessRound3ExtendedRegression
canonicalConsciousAccessRound3ExtendedRegression =
  record
    { coreRegression =
        CoreRegression.canonicalConsciousAccessRound3Regression
    ; lSystemBranches =
        Growth.firstLSystemGenerationIsBranched
    ; spaceColonisationSelectsMaximalTip =
        Growth.selectedColonisingTipIsMaximal
    ; phyllotaxisSelectsMaximalSite =
        Growth.selectedPrimordiumSiteIsMaximal
    ; edenSelectsMaximalFrontier =
        Growth.selectedEdenCellIsMaximal
    ; diffusionWalkerSticks =
        Growth.firstContactGrowsAggregate
    ; squareAndApollonianSignaturesDiffer =
        Packing.squareAndApollonianSignaturesDiffer
    ; descartesIdentity =
        Packing.descartesCircleIdentity
    ; soddyGossetIdentity =
        Packing.soddyGossetSphereIdentity
    ; hybridCarriesSquareAndTangency =
        Packing.hybridCarriesBothSignatureFamilies
    ; sphereInteriorIsBooleanRemoved =
        SDF.sphereInteriorBecomesOutside
    ; repeatedDomainReturnsOriginCell =
        SDF.coordinateTwoRepeatsToOriginCell
    ; hybridCrossBranchDistanceIsThree =
        Hybrid.crossBranchAndChartMoveHasDistanceThree
    ; hybridLocalMovePreservesBranch =
        Hybrid.localTransitionPreservesBranch
    ; visualHistoryResidualIsOne =
        Braid.canonicalHistoryResidualIsOne
    ; amplifiedMagnitudeIsThree =
        Quantitative.amplifiedResponseIsThree
    ; delayedResponseReleasesPending =
        Quantitative.secondDelayedStepReleasesPendingMagnitude
    ; symbolicMinimumExists =
        Symbolic.selectedTrueSymbolMinimal
    ; symbolicMinimumNeedNotBeUnique =
        Symbolic.alternateTrueObjectiveAlsoOne
    ; unconsciousBlockingStable =
        Unconscious.stableBlockingAcrossPerturbations
    ; unconsciousCarrierStillCausal =
        Unconscious.blockedCarrierStillInfluencesAction
    ; coalitionFivePhaseReturn =
        Phases.fiveStepsReturnToRecruitment
    ; completeBoundary =
        Full.canonicalConsciousAccessRound3FullBoundary
    }
