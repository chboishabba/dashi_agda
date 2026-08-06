module DASHI.Biology.PsychedelicVisualOperatorAlgebra where

open import DASHI.Core.Prelude

import DASHI.Biology.StateDependentMultiplexTransducer as Stateful
import DASHI.Biology.ProductiveTransformCoherence as Coherence
import DASHI.Biology.PsychedelicAttractorReweightingBoundary as Attractor

------------------------------------------------------------------------
-- A finite operator algebra for psychedelic visual phenomenology.
--
-- The model separates exogenous anchoring, temporal retention, spatial
-- deformation, pattern completion, endogenous generation, prior precision,
-- and cross-network coupling.  The quantities are exact model values, not
-- calibrated psychophysics or pharmacology.
--
-- Source-facing references:
-- Sean Noah Miranda Shen et al.,
-- "A novel method for quantitative analysis of subjective experience
-- reports: application to psychedelic visual experiences",
-- DOI 10.3389/fpsyg.2024.1397064.
--
-- Robin Carhart-Harris and Karl Friston,
-- "REBUS and the Anarchic Brain: Toward a Unified Model of the Brain Action
-- of Psychedelics", DOI 10.1124/pr.118.017160.

record VisualParameterProfile : Set where
  constructor visualParameterProfile
  field
    sensoryGain : Nat
    temporalRetention : Nat
    spatialDeformation : Nat
    patternCompletion : Nat
    highLevelPriorPrecision : Nat
    endogenousGeneration : Nat
    crossNetworkCoupling : Nat

open VisualParameterProfile public

baselineVisualProfile : VisualParameterProfile
baselineVisualProfile =
  visualParameterProfile 1 0 0 0 2 0 0

gainOnlyProfile : VisualParameterProfile
gainOnlyProfile =
  visualParameterProfile 2 0 0 0 2 0 0

retentionOnlyProfile : VisualParameterProfile
retentionOnlyProfile =
  visualParameterProfile 1 2 0 0 2 0 0

deformationOnlyProfile : VisualParameterProfile
deformationOnlyProfile =
  visualParameterProfile 1 0 2 0 2 0 0

endogenousOnlyProfile : VisualParameterProfile
endogenousOnlyProfile =
  visualParameterProfile 1 0 0 0 2 2 0

couplingOnlyProfile : VisualParameterProfile
couplingOnlyProfile =
  visualParameterProfile 1 0 0 0 2 0 2

gainCanChangeWithoutRetention :
  sensoryGain gainOnlyProfile ≡ 2
  ×
  temporalRetention gainOnlyProfile ≡
    temporalRetention baselineVisualProfile
gainCanChangeWithoutRetention = refl , refl

retentionCanChangeWithoutDeformation :
  temporalRetention retentionOnlyProfile ≡ 2
  ×
  spatialDeformation retentionOnlyProfile ≡
    spatialDeformation baselineVisualProfile
retentionCanChangeWithoutDeformation = refl , refl

endogenousGenerationCanChangeWithoutCoupling :
  endogenousGeneration endogenousOnlyProfile ≡ 2
  ×
  crossNetworkCoupling endogenousOnlyProfile ≡
    crossNetworkCoupling baselineVisualProfile
endogenousGenerationCanChangeWithoutCoupling = refl , refl

couplingCanChangeWithoutEndogenousGeneration :
  crossNetworkCoupling couplingOnlyProfile ≡ 2
  ×
  endogenousGeneration couplingOnlyProfile ≡
    endogenousGeneration baselineVisualProfile
couplingCanChangeWithoutEndogenousGeneration = refl , refl

------------------------------------------------------------------------
-- OEV/CEV is represented as an anchoring continuum rather than a disjoint
-- type-level split.

data AnchoringRegime : Set where
  externallyAnchored : AnchoringRegime
  mixedAnchoring : AnchoringRegime
  endogenousDominant : AnchoringRegime

externalWeight : AnchoringRegime → Nat
externalWeight externallyAnchored = 2
externalWeight mixedAnchoring = 1
externalWeight endogenousDominant = 0

endogenousWeight : AnchoringRegime → Nat
endogenousWeight externallyAnchored = 0
endogenousWeight mixedAnchoring = 1
endogenousWeight endogenousDominant = 2

record AnchoringContinuumWitness : Set where
  constructor anchoringContinuumWitness
  field
    externalRegime : AnchoringRegime
    mixedRegime : AnchoringRegime
    endogenousRegime : AnchoringRegime

    externalHasMaxExternalWeight :
      externalWeight externalRegime ≡ 2

    mixedHasBothContributions :
      externalWeight mixedRegime ≡ 1
      ×
      endogenousWeight mixedRegime ≡ 1

    endogenousHasMaxEndogenousWeight :
      endogenousWeight endogenousRegime ≡ 2

open AnchoringContinuumWitness public

canonicalAnchoringContinuumWitness : AnchoringContinuumWitness
canonicalAnchoringContinuumWitness =
  anchoringContinuumWitness
    externallyAnchored
    mixedAnchoring
    endogenousDominant
    refl
    (refl , refl)
    refl

------------------------------------------------------------------------
-- Temporal persistence.  One fixed input can produce different output under
-- different retained state.

record TemporalVisualState : Set where
  constructor temporalVisualState
  field
    currentInput : Nat
    retainedTrace : Nat

open TemporalVisualState public

clearOutput : TemporalVisualState → Nat
clearOutput s = currentInput s

persistentOutput : TemporalVisualState → Nat
persistentOutput s = currentInput s + retainedTrace s

sameInputNoTrace : TemporalVisualState
sameInputNoTrace = temporalVisualState 1 0

sameInputWithTrace : TemporalVisualState
sameInputWithTrace = temporalVisualState 1 1

sameInputDifferentTemporalState :
  currentInput sameInputNoTrace ≡ currentInput sameInputWithTrace
sameInputDifferentTemporalState = refl

traceChangesOutput :
  persistentOutput sameInputWithTrace ≡ 2
  ×
  persistentOutput sameInputNoTrace ≡ 1
traceChangesOutput = refl , refl

------------------------------------------------------------------------
-- Spatial deformation under constant environmental input.

data VisualPoint : Set where
  leftPoint : VisualPoint
  centrePoint : VisualPoint
  rightPoint : VisualPoint

identityDeformation : VisualPoint → VisualPoint
identityDeformation x = x

driftRight : VisualPoint → VisualPoint
driftRight leftPoint = centrePoint
driftRight centrePoint = rightPoint
driftRight rightPoint = rightPoint

constantScenePoint : VisualPoint
constantScenePoint = centrePoint

staticInputCanHaveChangingInternalGeometry :
  identityDeformation constantScenePoint ≡ centrePoint
  ×
  driftRight constantScenePoint ≡ rightPoint
staticInputCanHaveChangingInternalGeometry = refl , refl

------------------------------------------------------------------------
-- Pattern completion and deformation do not generally commute.

completePattern : Bool → Bool
completePattern _ = true

deformPattern : Bool → Bool
deformPattern = Stateful.boolNot

completeAfterDeform : Bool → Bool
completeAfterDeform x = completePattern (deformPattern x)

deformAfterComplete : Bool → Bool
deformAfterComplete x = deformPattern (completePattern x)

completeAfterDeformFalseIsTrue :
  completeAfterDeform false ≡ true
completeAfterDeformFalseIsTrue = refl

deformAfterCompleteFalseIsFalse :
  deformAfterComplete false ≡ false
deformAfterCompleteFalseIsFalse = refl

visualOperatorOrderResidual :
  completeAfterDeform false ≡ deformAfterComplete false → ⊥
visualOperatorOrderResidual ()

------------------------------------------------------------------------
-- Pareidolic threshold crossing as model-relative coalition selection.

data VisualInterpretation : Set where
  faceInterpretation : VisualInterpretation
  noiseInterpretation : VisualInterpretation

ordinaryInterpretationCost : VisualInterpretation → Nat
ordinaryInterpretationCost faceInterpretation = 3
ordinaryInterpretationCost noiseInterpretation = 1

alteredInterpretationCost : VisualInterpretation → Nat
alteredInterpretationCost faceInterpretation = 1
alteredInterpretationCost noiseInterpretation = 2

ordinarySelectedInterpretation : VisualInterpretation
ordinarySelectedInterpretation = noiseInterpretation

alteredSelectedInterpretation : VisualInterpretation
alteredSelectedInterpretation = faceInterpretation

ordinarySelectsNoise :
  ordinarySelectedInterpretation ≡ noiseInterpretation
ordinarySelectsNoise = refl

alteredSelectsFace :
  alteredSelectedInterpretation ≡ faceInterpretation
alteredSelectsFace = refl

alteredFaceCostIsMinimal :
  (i : VisualInterpretation) →
  alteredInterpretationCost faceInterpretation
  ≤
  alteredInterpretationCost i
alteredFaceCostIsMinimal faceInterpretation = ≤-refl
alteredFaceCostIsMinimal noiseInterpretation = s≤s z≤n

------------------------------------------------------------------------
-- Equal intensity need not imply equal representational depth.

data RepresentationLevel : Set where
  featureLevel : RepresentationLevel
  contourLevel : RepresentationLevel
  objectLevel : RepresentationLevel
  sceneLevel : RepresentationLevel
  narrativeLevel : RepresentationLevel

levelDepth : RepresentationLevel → Nat
levelDepth featureLevel = 0
levelDepth contourLevel = 1
levelDepth objectLevel = 2
levelDepth sceneLevel = 3
levelDepth narrativeLevel = 4

record VisualCoalitionProfile : Set where
  constructor visualCoalitionProfile
  field
    intensity : Nat
    attainedLevel : RepresentationLevel

open VisualCoalitionProfile public

geometricCoalition : VisualCoalitionProfile
geometricCoalition =
  visualCoalitionProfile 3 contourLevel

immersiveSceneCoalition : VisualCoalitionProfile
immersiveSceneCoalition =
  visualCoalitionProfile 3 sceneLevel

equalIntensityDifferentDepth :
  intensity geometricCoalition
  ≡
  intensity immersiveSceneCoalition
equalIntensityDifferentDepth = refl

geometricAndSceneDepthDiffer :
  levelDepth (attainedLevel geometricCoalition)
  ≡
  levelDepth (attainedLevel immersiveSceneCoalition)
  →
  ⊥
geometricAndSceneDepthDiffer ()

------------------------------------------------------------------------
-- Same perturbation, different initial state.

alteredVisualStep : Bool → Bool
alteredVisualStep false = true
alteredVisualStep true = false

samePerturbationDifferentInitialState :
  alteredVisualStep false ≡ alteredVisualStep true → ⊥
samePerturbationDifferentInitialState ()

record VisualOperatorBoundary : Set where
  constructor visualOperatorBoundary
  field
    oneScalarExplainsAllVisualEffects : Bool
    oneScalarExplainsAllVisualEffectsIsFalse :
      oneScalarExplainsAllVisualEffects ≡ false

    oevAndCevAreMechanisticallyDisjoint : Bool
    oevAndCevAreMechanisticallyDisjointIsFalse :
      oevAndCevAreMechanisticallyDisjoint ≡ false

    modelParametersAreEmpiricallyCalibrated : Bool
    modelParametersAreEmpiricallyCalibratedIsFalse :
      modelParametersAreEmpiricallyCalibrated ≡ false

    attractorBoundary :
      Attractor.PsychedelicAttractorBoundary

open VisualOperatorBoundary public

canonicalVisualOperatorBoundary : VisualOperatorBoundary
canonicalVisualOperatorBoundary =
  visualOperatorBoundary
    false refl
    false refl
    false refl
    Attractor.canonicalPsychedelicAttractorBoundary
