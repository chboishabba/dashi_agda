module DASHI.Biology.MultiscaleAllostaticBodyHyperformalismExact where

open import DASHI.Core.Prelude

import DASHI.Biology.EmbodiedOptionConeInteroceptionExact as Body
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

------------------------------------------------------------------------
-- MULTISCALE ALLOSTATIC BODY SUPERVOXEL
--
-- The body carrier is a coupled stack of partially independent subsystem
-- coordinates, not a single cortisol/stress scalar.  The exact finite model is
-- deliberately qualitative and does not identify these coordinates with a
-- diagnosis or quantitative physiological fit.
------------------------------------------------------------------------

data BodyTimescale : Set where
  neuralFast autonomicFast endocrineSlower plasticSlow : BodyTimescale

record BodySupervoxel : Set where
  constructor bodySupervoxel
  field
    ans : Body.Activation
    hpa : Body.Activation
    immune : Body.Activation
    metabolic : Body.Activation
    cardiorespiratory : Body.Activation
    gastrointestinal : Body.Activation
    motor : Body.Activation
    circadian : Body.Activation

open BodySupervoxel public

regulatedStack : BodySupervoxel
regulatedStack =
  bodySupervoxel
    Body.low Body.medium Body.low Body.medium
    Body.low Body.low Body.low Body.medium

acuteMobilisedStack : BodySupervoxel
acuteMobilisedStack =
  bodySupervoxel
    Body.high Body.medium Body.low Body.medium
    Body.high Body.medium Body.high Body.medium

prolongedLoadStack : BodySupervoxel
prolongedLoadStack =
  bodySupervoxel
    Body.high Body.high Body.high Body.high
    Body.high Body.high Body.high Body.low

sameHPAAtDifferentWholeBodyStates :
  hpa regulatedStack ≡ hpa acuteMobilisedStack
sameHPAAtDifferentWholeBodyStates = refl

hpaCoordinateDoesNotRecoverWholeBody :
  regulatedStack ≡ acuteMobilisedStack → ⊥
hpaCoordinateDoesNotRecoverWholeBody ()

------------------------------------------------------------------------
-- A local embodied cubie uses the existing rank-three ternary block.  The
-- three axes are only local coordinates; they are not claimed to exhaust body
-- physiology.
------------------------------------------------------------------------

EmbodiedCubie : Set
EmbodiedCubie = Hyper.AxisBlock 3

historyBodyFutureCubie : EmbodiedCubie
historyBodyFutureCubie =
  Hyper.block-cons Hyper.axis-mid
    (Hyper.block-cons Hyper.axis-high
      (Hyper.block-cons Hyper.axis-low Hyper.block-root))

------------------------------------------------------------------------
-- Predictive/allostatic control: anticipated demand can change a regulatory
-- policy before the external-demand observation itself changes.
------------------------------------------------------------------------

data PredictedDemand : Set where
  lowDemand highDemand : PredictedDemand

data RegulatoryPolicy : Set where
  recoverPolicy preparePolicy : RegulatoryPolicy

policyFor : PredictedDemand → RegulatoryPolicy
policyFor lowDemand = recoverPolicy
policyFor highDemand = preparePolicy

applyPolicy : RegulatoryPolicy → BodySupervoxel → BodySupervoxel
applyPolicy recoverPolicy body = regulatedStack
applyPolicy preparePolicy body = acuteMobilisedStack

highPredictedDemandPreparesBody :
  applyPolicy (policyFor highDemand) regulatedStack ≡ acuteMobilisedStack
highPredictedDemandPreparesBody = refl

lowPredictedDemandRecoversBody :
  applyPolicy (policyFor lowDemand) acuteMobilisedStack ≡ regulatedStack
lowPredictedDemandRecoversBody = refl

anticipatedDemandCanChangeBodyBeforeDemandObservation :
  applyPolicy (policyFor highDemand) regulatedStack
  ≡ applyPolicy (policyFor lowDemand) regulatedStack → ⊥
anticipatedDemandCanChangeBodyBeforeDemandObservation ()

------------------------------------------------------------------------
-- Appraisal is vector-valued: equal predicted harm need not mean equal
-- controllability/escape geometry or equal regulatory policy.
------------------------------------------------------------------------

record AppraisalGeometry : Set where
  constructor appraisalGeometry
  field
    predictedHarm : Body.Activation
    controllability : Body.Activation
    escapeability : Body.Activation
    uncertainty : Body.Activation
    socialEvaluation : Body.Activation
    timePressure : Body.Activation
    resourceDeficit : Body.Activation
    novelty : Body.Activation
    learnedSimilarity : Body.Activation

open AppraisalGeometry public

highHarmHighControl : AppraisalGeometry
highHarmHighControl =
  appraisalGeometry
    Body.high Body.high Body.high Body.medium Body.low
    Body.medium Body.low Body.medium Body.low

highHarmLowControl : AppraisalGeometry
highHarmLowControl =
  appraisalGeometry
    Body.high Body.low Body.low Body.medium Body.low
    Body.medium Body.low Body.medium Body.low

samePredictedHarm :
  predictedHarm highHarmHighControl ≡ predictedHarm highHarmLowControl
samePredictedHarm = refl

controlStillDiffers :
  highHarmHighControl ≡ highHarmLowControl → ⊥
controlStillDiffers ()

policyFromControl : Body.Activation → RegulatoryPolicy
policyFromControl Body.low = preparePolicy
policyFromControl Body.medium = recoverPolicy
policyFromControl Body.high = recoverPolicy

policyFromAppraisal : AppraisalGeometry → RegulatoryPolicy
policyFromAppraisal appraisal = policyFromControl (controllability appraisal)

sameHarmDifferentControlChangesPolicy :
  policyFromAppraisal highHarmHighControl
  ≡ policyFromAppraisal highHarmLowControl → ⊥
sameHarmDifferentControlChangesPolicy ()

record MultiscaleAllostaticBoundary : Set where
  constructor multiscaleAllostaticBoundary
  field
    oneHormoneDeterminesWholeBody : Bool
    subsystemTimescalesAreIdentical : Bool
    anticipatoryPolicyIsRetrocausalClaim : Bool
    finiteStackDiagnosesPerson : Bool
    localCubieExhaustsPhysiology : Bool

canonicalMultiscaleAllostaticBoundary : MultiscaleAllostaticBoundary
canonicalMultiscaleAllostaticBoundary =
  multiscaleAllostaticBoundary false false false false false
