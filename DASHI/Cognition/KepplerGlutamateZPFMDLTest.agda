module DASHI.Cognition.KepplerGlutamateZPFMDLTest where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Physical carrier vocabulary: hypothesis only, not promoted fact
------------------------------------------------------------------------

record CorticalMicrocolumn : Set where
  constructor corticalMicrocolumn
  field
    columnCount : Nat
    geometryTag : String

record GlutamatePool : Set where
  constructor glutamatePool
  field
    populationCount : Nat
    modeTag          : String

record ZPFMode : Set where
  constructor zpfMode
  field
    modeIndex    : Nat
    frequencyTag : String

record ResonanceWitness : Set where
  constructor resonanceWitness
  field
    glutamateModeResolved : Bool
    fieldModeResolved     : Bool
    frequencyMatched      : Bool
    ensembleThresholdSeen : Bool

record KepplerCouplingCandidate : Set where
  constructor kepplerCouplingCandidate
  field
    microcolumn : CorticalMicrocolumn
    glutamate   : GlutamatePool
    mode        : ZPFMode
    witness     : ResonanceWitness
    couplingStrengthCode : Nat

candidateCouplingClosed : KepplerCouplingCandidate → Bool
candidateCouplingClosed candidate =
  ResonanceWitness.frequencyMatched
    (KepplerCouplingCandidate.witness candidate)

------------------------------------------------------------------------
-- Null versus extra-coupling predictive code length
------------------------------------------------------------------------

record PredictiveCode : Set where
  constructor predictiveCode
  field
    modelCost    : Nat
    residualCost : Nat

totalCode : PredictiveCode → Nat
totalCode code = add
  (PredictiveCode.modelCost code)
  (PredictiveCode.residualCost code)
  where
  add : Nat → Nat → Nat
  add zero    n = n
  add (suc m) n = suc (add m n)

record ModelComparison : Set where
  constructor modelComparison
  field
    nullCode        : PredictiveCode
    kepplerCode     : PredictiveCode
    nullWins        : Bool
    kepplerWins     : Bool
    frequencySelectivityPredicted : Bool
    heldOutImprovementWitnessed   : Bool

------------------------------------------------------------------------
-- Generic decision boundary: evidence must be supplied, never fabricated
------------------------------------------------------------------------

data ModelDecision : Set where
  retainScalarControl : ModelDecision
  retainKepplerCandidate : ModelDecision
  unresolvedComparison : ModelDecision

selectModel : ModelComparison → ModelDecision
selectModel comparison with
  ModelComparison.nullWins comparison |
  ModelComparison.kepplerWins comparison |
  ModelComparison.frequencySelectivityPredicted comparison |
  ModelComparison.heldOutImprovementWitnessed comparison
... | true  | false | _     | _     = retainScalarControl
... | false | true  | true  | true  = retainKepplerCandidate
... | _     | _     | _     | _     = unresolvedComparison

------------------------------------------------------------------------
-- Small calibration fixture corresponding only to the synthetic test bench
------------------------------------------------------------------------

syntheticNullCode : PredictiveCode
syntheticNullCode = predictiveCode 11 4

syntheticKepplerCode : PredictiveCode
syntheticKepplerCode = predictiveCode 12 7

syntheticCalibrationComparison : ModelComparison
syntheticCalibrationComparison =
  modelComparison
    syntheticNullCode
    syntheticKepplerCode
    true
    false
    false
    false

syntheticCalibrationSelectsScalarControl :
  selectModel syntheticCalibrationComparison ≡ retainScalarControl
syntheticCalibrationSelectsScalarControl = refl

------------------------------------------------------------------------
-- What would make the Keppler term earn its keep
------------------------------------------------------------------------

record FrequencySelectiveTest : Set where
  constructor frequencySelectiveTest
  field
    predictedBandTag       : String
    offBandControlIncluded : Bool
    glutamateControlIncluded : Bool
    geometryControlIncluded  : Bool
    anestheticConditions     : Nat

record KepplerEarnsKeepWitness : Set where
  constructor kepplerEarnsKeepWitness
  field
    lowerHeldOutCodeLength : Bool
    predictedBandSpecific  : Bool
    offBandFailsToImprove  : Bool
    stableAcrossConditions : Bool

kepplerEarnsKeep : KepplerEarnsKeepWitness → Bool
kepplerEarnsKeep witness with
  KepplerEarnsKeepWitness.lowerHeldOutCodeLength witness |
  KepplerEarnsKeepWitness.predictedBandSpecific witness |
  KepplerEarnsKeepWitness.offBandFailsToImprove witness |
  KepplerEarnsKeepWitness.stableAcrossConditions witness
... | true | true | true | true = true
... | _    | _    | _    | _    = false

canonicalUnresolvedEarnsKeepWitness : KepplerEarnsKeepWitness
canonicalUnresolvedEarnsKeepWitness =
  kepplerEarnsKeepWitness false false false false

canonicalKepplerNotPromoted :
  kepplerEarnsKeep canonicalUnresolvedEarnsKeepWitness ≡ false
canonicalKepplerNotPromoted = refl

------------------------------------------------------------------------
-- Empirical authority boundary
------------------------------------------------------------------------

record KepplerEmpiricalBoundary : Set where
  constructor kepplerEmpiricalBoundary
  field
    formalCandidateDefined       : Bool
    syntheticCalibrationSeparated : Bool
    realDatasetBound             : Bool
    physicalCouplingEstablished  : Bool
    consciousnessCauseEstablished : Bool

canonicalKepplerEmpiricalBoundary : KepplerEmpiricalBoundary
canonicalKepplerEmpiricalBoundary =
  kepplerEmpiricalBoundary true true false false false

realDatasetStillRequired :
  KepplerEmpiricalBoundary.realDatasetBound
    canonicalKepplerEmpiricalBoundary ≡ false
realDatasetStillRequired = refl

noConsciousnessCausePromotion :
  KepplerEmpiricalBoundary.consciousnessCauseEstablished
    canonicalKepplerEmpiricalBoundary ≡ false
noConsciousnessCausePromotion = refl
