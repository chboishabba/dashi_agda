module DASHI.Physics.Closure.QuantumGRActionCompatibilityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.AdmissibilityJetSpec as Spec
import DASHI.Physics.Closure.EinsteinHilbertVariationConditional as EH
import DASHI.Physics.Closure.StressEnergyBianchiConditional as Source
import DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary as Vacuum

------------------------------------------------------------------------
-- Quantum / GR action compatibility boundary.
--
-- A common action/quotient vocabulary is not yet a quantum-gravity theory.
-- This module records the strongest compositional seam justified by the
-- current formalism: classical geometry and quantum amplitudes may consume
-- the same admissible action carrier, provided gauge fixing, measure,
-- unitarity/reflection-positivity, renormalisation, and classical-limit
-- obligations are separately supplied.

record SharedActionCarrier : Set where
  constructor mkSharedActionCarrier
  field
    actionLabel : String
    geometricSpec : Spec.DepthAdmissibilitySpec
    spinorSpec : Spec.DepthAdmissibilitySpec
    EinsteinHilbertReceiptAvailable : Bool
    conservedSourceReceiptAvailable : Bool
    quotientFirst : Bool
    finiteJetAtEffectiveDepth : Bool
    actionStatement : String

open SharedActionCarrier public

record QuantumMeasureWitness (action : SharedActionCarrier) : Set where
  constructor mkQuantumMeasureWitness
  field
    measureLabel : String
    stateOrHistorySpaceSupplied : Bool
    gaugeRedundancyControlled : Bool
    measureOrAmplitudeRuleSupplied : Bool
    compositionLawSupplied : Bool
    positivityOrUnitarityConditionSupplied : Bool
    anomalyFreedomSupplied : Bool
    quantumStatement : String

open QuantumMeasureWitness public

record QuantumGRLimitWitness
  (action : SharedActionCarrier)
  (quantum : QuantumMeasureWitness action) : Set where
  constructor mkQuantumGRLimitWitness
  field
    renormalisationSchemeSupplied : Bool
    continuumOrControlledEffectiveLimitSupplied : Bool
    semiclassicalLimitSupplied : Bool
    EinsteinEquationRecoveredInLimit : Bool
    quantumMatterBackreactionControlled : Bool
    empiricalConstantsMatched : Bool
    limitStatement : String

open QuantumGRLimitWitness public

record QuantumGRCompatibilityReceipt
  (action : SharedActionCarrier)
  (quantum : QuantumMeasureWitness action)
  (limit : QuantumGRLimitWitness action quantum) : Set where
  constructor mkQuantumGRCompatibilityReceipt
  field
    sharedActionReceipt : EinsteinHilbertReceiptAvailable action ≡ true
    sourceReceipt : conservedSourceReceiptAvailable action ≡ true
    stateSpaceReceipt : stateOrHistorySpaceSupplied quantum ≡ true
    gaugeReceipt : gaugeRedundancyControlled quantum ≡ true
    amplitudeReceipt : measureOrAmplitudeRuleSupplied quantum ≡ true
    compositionReceipt : compositionLawSupplied quantum ≡ true
    positivityReceipt : positivityOrUnitarityConditionSupplied quantum ≡ true
    anomalyReceipt : anomalyFreedomSupplied quantum ≡ true
    renormalisationReceipt : renormalisationSchemeSupplied limit ≡ true
    semiclassicalReceipt : semiclassicalLimitSupplied limit ≡ true
    EinsteinLimitReceipt : EinsteinEquationRecoveredInLimit limit ≡ true
    backreactionReceipt : quantumMatterBackreactionControlled limit ≡ true

open QuantumGRCompatibilityReceipt public

assembleQuantumGRCompatibilityReceipt :
  (action : SharedActionCarrier) →
  (quantum : QuantumMeasureWitness action) →
  (limit : QuantumGRLimitWitness action quantum) →
  EinsteinHilbertReceiptAvailable action ≡ true →
  conservedSourceReceiptAvailable action ≡ true →
  stateOrHistorySpaceSupplied quantum ≡ true →
  gaugeRedundancyControlled quantum ≡ true →
  measureOrAmplitudeRuleSupplied quantum ≡ true →
  compositionLawSupplied quantum ≡ true →
  positivityOrUnitarityConditionSupplied quantum ≡ true →
  anomalyFreedomSupplied quantum ≡ true →
  renormalisationSchemeSupplied limit ≡ true →
  semiclassicalLimitSupplied limit ≡ true →
  EinsteinEquationRecoveredInLimit limit ≡ true →
  quantumMatterBackreactionControlled limit ≡ true →
  QuantumGRCompatibilityReceipt action quantum limit
assembleQuantumGRCompatibilityReceipt action quantum limit shared source state gauge amplitude composition positivity anomaly rg semiclassical einstein backreaction =
  mkQuantumGRCompatibilityReceipt shared source state gauge amplitude composition positivity anomaly rg semiclassical einstein backreaction

canonicalSharedActionCarrier : SharedActionCarrier
canonicalSharedActionCarrier =
  mkSharedActionCarrier
    "conditional-shared-quantum-gr-action"
    Spec.metricDiffeomorphismTwoJetSpec
    Spec.spinorOneJetSpec
    true
    true
    true
    true
    "the GR and matter lanes share an admissible action vocabulary; this alone is not quantisation or unification"

canonicalConditionalQuantumMeasure :
  QuantumMeasureWitness canonicalSharedActionCarrier
canonicalConditionalQuantumMeasure =
  mkQuantumMeasureWitness
    "conditional-quantum-measure"
    true true true true true true
    "state/history space, redundancy control, amplitude law, composition, positivity/unitarity, and anomaly freedom are supplied hypotheses"

canonicalConditionalQuantumGRLimit :
  QuantumGRLimitWitness canonicalSharedActionCarrier canonicalConditionalQuantumMeasure
canonicalConditionalQuantumGRLimit =
  mkQuantumGRLimitWitness
    true true true true true false
    "the controlled limit is supplied conditionally; empirical constants are not derived or matched by this module"

canonicalConditionalQuantumGRCompatibility :
  QuantumGRCompatibilityReceipt
    canonicalSharedActionCarrier
    canonicalConditionalQuantumMeasure
    canonicalConditionalQuantumGRLimit
canonicalConditionalQuantumGRCompatibility =
  assembleQuantumGRCompatibilityReceipt
    canonicalSharedActionCarrier
    canonicalConditionalQuantumMeasure
    canonicalConditionalQuantumGRLimit
    refl refl refl refl refl refl refl refl refl refl refl refl

record UnificationPromotionBoundary : Set where
  constructor mkUnificationPromotionBoundary
  field
    conditionalCompatibilityTyped : Bool
    commonKernelTowerDerived : Bool
    StandardModelGaugeGroupDerived : Bool
    observedRepresentationsDerived : Bool
    couplingConstantsDerived : Bool
    quantumGravityUVCompletionProved : Bool
    allKnownRegimesRecovered : Bool
    novelFalsifiablePredictionValidated : Bool
    quantumGRUnificationProved : Bool
    theoryOfEverythingPromotionPermitted : Bool
    promotionStatement : String

open UnificationPromotionBoundary public

canonicalUnificationPromotionBoundary : UnificationPromotionBoundary
canonicalUnificationPromotionBoundary =
  mkUnificationPromotionBoundary
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false
    "conditional interface compatibility is typed, while derivation, UV completion, empirical recovery, and ToE promotion remain blocked"

canonicalQuantumGRUnificationBlocked :
  quantumGRUnificationProved canonicalUnificationPromotionBoundary ≡ false
canonicalQuantumGRUnificationBlocked = refl

canonicalTheoryOfEverythingBlocked :
  theoryOfEverythingPromotionPermitted canonicalUnificationPromotionBoundary ≡ false
canonicalTheoryOfEverythingBlocked = refl
