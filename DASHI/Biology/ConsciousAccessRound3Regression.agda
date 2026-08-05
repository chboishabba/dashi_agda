module DASHI.Biology.ConsciousAccessRound3Regression where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Biology.PsychedelicVisualOperatorAlgebra as Visual
import DASHI.Biology.MorphogeneticVisualGenerator as Morphogenesis
import DASHI.Biology.RecursiveSpherePerforation as Perforation
import DASHI.Biology.NestedApertureVisibility as Visibility
import DASHI.Biology.LogPolarRetinotopyBridge as Retinotopy
import DASHI.Biology.PsychedelicMorphogeneticGeometryBoundary as Boundary
import DASHI.Biology.Morphogenesis.ReactionDiffusionModeSelection as RD
import DASHI.Biology.QuantitativeCompositionalDefect as Defect
import DASHI.Biology.VisualMotifTransitionOperator as Motifs
import DASHI.Biology.PostAcuteVisualAdaptation as PostAcute
import DASHI.Biology.HallOfHallsCoalition as HallCoalition
import DASHI.Biology.ConsciousAccessRound3SourceAtlas as Sources

record ConsciousAccessRound3Regression : Setω where
  field
    gainIndependentOfRetention :
      Visual.sensoryGain Visual.gainOnlyProfile ≡ 2
      ×
      Visual.temporalRetention Visual.gainOnlyProfile ≡
        Visual.temporalRetention Visual.baselineVisualProfile

    anchoringContinuum :
      Visual.AnchoringContinuumWitness

    temporalTraceChangesOutput :
      Visual.persistentOutput Visual.sameInputWithTrace ≡ 2
      ×
      Visual.persistentOutput Visual.sameInputNoTrace ≡ 1

    visualOrderIsNoncommutative :
      Visual.completeAfterDeform false
      ≡
      Visual.deformAfterComplete false
      →
      ⊥

    pareidolicThresholdCrossing :
      Visual.alteredSelectedInterpretation
      ≡
      Visual.faceInterpretation

    equalIntensityDifferentDepth :
      Visual.intensity Visual.geometricCoalition
      ≡
      Visual.intensity Visual.immersiveSceneCoalition

    motifCycleReturns :
      Motifs.motifStep Motifs.reweightedMotifRegime
        (Motifs.motifStep Motifs.reweightedMotifRegime
          (Motifs.motifStep Motifs.reweightedMotifRegime
            Motifs.latticeMotif))
      ≡
      Motifs.latticeMotif

    postAcuteBaselineRetainsSlowState :
      PostAcute.visualResponse
        PostAcute.baselineExposure
        PostAcute.preExposureState
      ≡
      1
      ×
      PostAcute.visualResponse
        PostAcute.baselineExposure
        PostAcute.postExposureAdaptedState
      ≡
      2

    hallCoalitionMinimal :
      (c : HallCoalition.HallCoalitionCandidate) →
      HallCoalition.hallObjective HallCoalition.selectedHallCoalition
      ≤
      HallCoalition.hallObjective c

    hallCoalitionRecurrent :
      HallCoalition.hallCoalitionUpdate
        HallCoalition.selectedHallCoalition
      ≡
      HallCoalition.selectedHallCoalition

    squareModeSelected :
      RD.TuringModeSelectionWitness
        Morphogenesis.finiteReactionDiffusionSystem

    sharedMorphologyWithoutMechanismIdentity :
      Morphogenesis.classOfMechanism Morphogenesis.neuralFieldCarrier
      ≡
      Morphogenesis.classOfMechanism
        Morphogenesis.biologicalMorphogenCarrier

    recursiveMaterialMonotone :
      Perforation.materialCells Perforation.roomStage3
      ≤
      Perforation.materialCells Perforation.roomStage2

    maximalResidualSite :
      (c : Perforation.CandidateSite) →
      Perforation.clearance c
      ≤
      Perforation.clearance Perforation.selectedResidualSite

    curvedTriangleFromTangency :
      Perforation.dominantGapShape Perforation.tangentTripleSeed
      ≡
      Perforation.curvedTriangularGap

    fixedCarrierDifferentVisibility :
      Visibility.ApertureVisibilityContrast

    depthParallax :
      Visibility.projectedShift Visibility.shiftedView Visibility.farLayer
      ≤
      Visibility.projectedShift Visibility.shiftedView Visibility.nearLayer

    scaleBecomesTranslation :
      Retinotopy.logRadiusCode
        (Retinotopy.doubleRadius Retinotopy.radiusOne)
      ≡
      suc (Retinotopy.logRadiusCode Retinotopy.radiusOne)

    distinctGeneratorsShareProjection :
      Retinotopy.corticalProjection Retinotopy.squareWorldGenerator
      ≡
      Retinotopy.corticalProjection Retinotopy.apollonianWorldGenerator

    selectedHallModelMinimal :
      (h : Boundary.HallGeneratorHypothesis) →
      Boundary.hallPenalty Boundary.selectedHallHypothesis
      ≤
      Boundary.hallPenalty h

    hallProductiveDefectIsOne :
      Defect.netDefect Boundary.hallDefectProfile ≡ 1

    sourceCountIsNine :
      Sources.canonicalRound3SourceCount ≡ 9

open ConsciousAccessRound3Regression public

canonicalConsciousAccessRound3Regression :
  ConsciousAccessRound3Regression
canonicalConsciousAccessRound3Regression =
  record
    { gainIndependentOfRetention =
        Visual.gainCanChangeWithoutRetention
    ; anchoringContinuum =
        Visual.canonicalAnchoringContinuumWitness
    ; temporalTraceChangesOutput =
        Visual.traceChangesOutput
    ; visualOrderIsNoncommutative =
        Visual.visualOperatorOrderResidual
    ; pareidolicThresholdCrossing =
        Visual.alteredSelectsFace
    ; equalIntensityDifferentDepth =
        Visual.equalIntensityDifferentDepth
    ; motifCycleReturns =
        Motifs.reweightedThreeCycleReturns
    ; postAcuteBaselineRetainsSlowState =
        PostAcute.baselineParameterDoesNotEraseSlowState
    ; hallCoalitionMinimal =
        HallCoalition.selectedHallCoalitionMinimal
    ; hallCoalitionRecurrent =
        HallCoalition.selectedHallCoalitionIsFixedPoint
    ; squareModeSelected =
        Morphogenesis.squareModeSelectionWitness
    ; sharedMorphologyWithoutMechanismIdentity =
        Morphogenesis.neuralAndBiologicalShareMorphologicalClass
    ; recursiveMaterialMonotone =
        Perforation.stage3IsContainedByStage2
    ; maximalResidualSite =
        Perforation.selectedResidualSiteIsMaximal
    ; curvedTriangleFromTangency =
        Perforation.tangentSeedHasCurvedTriangularGap
    ; fixedCarrierDifferentVisibility =
        Visibility.canonicalApertureVisibilityContrast
    ; depthParallax =
        Visibility.shiftedViewProducesDepthParallax
    ; scaleBecomesTranslation =
        Retinotopy.doublingAtRadiusOneIsUnitTranslation
    ; distinctGeneratorsShareProjection =
        Retinotopy.squareAndApollonianCanShareCorticalProjection
    ; selectedHallModelMinimal =
        Boundary.selectedHallHypothesisMinimal
    ; hallProductiveDefectIsOne =
        Boundary.hallNetDefectIsOne
    ; sourceCountIsNine =
        Sources.canonicalRound3SourceCountIsNine
    }
