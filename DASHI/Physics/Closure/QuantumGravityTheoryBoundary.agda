module DASHI.Physics.Closure.QuantumGravityTheoryBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Quantum-gravity theory boundary.
--
-- Sharing an action carrier or placing a finite quantum model beside a flat GR
-- model is not quantum gravity.  The target requires quantum gravitational
-- degrees of freedom, gauge control, dynamics, observables, limits, and tests.

record QuantumGravityKinematics : Set where
  constructor mkQuantumGravityKinematics
  field
    kinematicsLabel : String
    gravitationalStateSpaceConstructed : Bool
    matterStateSpaceConstructed : Bool
    diffeomorphismGaugeQuotientConstructed : Bool
    localLorentzOrFrameGaugeControlled : Bool
    physicalInnerProductOrPositiveMeasureConstructed : Bool
    kinematicsScope : String

open QuantumGravityKinematics public

record QuantumGravityDynamics (K : QuantumGravityKinematics) : Set where
  constructor mkQuantumGravityDynamics
  field
    dynamicsLabel : String
    HamiltonianOrAmplitudeRuleConstructed : Bool
    constraintsCloseWithoutAnomaly : Bool
    compositionOrGluingLawProved : Bool
    unitarityOrReflectionPositivityProved : Bool
    renormalisationControlled : Bool
    ultravioletCompletionOrPredictiveEFTProved : Bool
    dynamicsScope : String

open QuantumGravityDynamics public

record QuantumGravityLimits
  (K : QuantumGravityKinematics)
  (D : QuantumGravityDynamics K) : Set where
  constructor mkQuantumGravityLimits
  field
    semiclassicalStatesConstructed : Bool
    EinsteinDynamicsRecovered : Bool
    quantumFieldTheoryOnCurvedSpacetimeRecovered : Bool
    backreactionControlled : Bool
    lowEnergyConstantsMatched : Bool
    blackHoleOrCosmologicalRegimeChecked : Bool
    limitsScope : String

open QuantumGravityLimits public

record QuantumGravityEmpirics
  (K : QuantumGravityKinematics)
  (D : QuantumGravityDynamics K)
  (L : QuantumGravityLimits K D) : Set where
  constructor mkQuantumGravityEmpirics
  field
    observableMapConstructed : Bool
    novelQuantitativePredictionLocked : Bool
    experimentalOrObservationalTestPerformed : Bool
    predictionValidated : Bool
    independentReplicationAvailable : Bool
    empiricsScope : String

open QuantumGravityEmpirics public

record QuantumGravityTheoryReceipt : Set where
  constructor mkQuantumGravityTheoryReceipt
  field
    kinematics : QuantumGravityKinematics
    dynamics : QuantumGravityDynamics kinematics
    limits : QuantumGravityLimits kinematics dynamics
    empirics : QuantumGravityEmpirics kinematics dynamics limits
    receiptScope : String

open QuantumGravityTheoryReceipt public

record QuantumGravityPromotionBoundary : Set where
  constructor mkQuantumGravityPromotionBoundary
  field
    targetInterfacesImplemented : Bool
    finiteJointQuantumGRModelAvailable : Bool
    gravitationalQuantumStateSpaceConstructed : Bool
    anomalyFreeDynamicsProved : Bool
    semiclassicalEinsteinLimitProved : Bool
    validatedQuantumGravityPrediction : Bool
    quantumGravityClaimPermitted : Bool
    theoryOfEverythingClaimPermitted : Bool
    boundaryStatement : String

open QuantumGravityPromotionBoundary public

canonicalQuantumGravityPromotionBoundary : QuantumGravityPromotionBoundary
canonicalQuantumGravityPromotionBoundary =
  mkQuantumGravityPromotionBoundary
    true true false false false false false false
    "the complete promotion target is typed; the repository has no interacting anomaly-free quantum gravity theory or validated prediction"

canonicalQuantumGravityBlocked :
  quantumGravityClaimPermitted canonicalQuantumGravityPromotionBoundary ≡ false
canonicalQuantumGravityBlocked = refl

canonicalTheoryOfEverythingBlocked :
  theoryOfEverythingClaimPermitted canonicalQuantumGravityPromotionBoundary ≡ false
canonicalTheoryOfEverythingBlocked = refl
