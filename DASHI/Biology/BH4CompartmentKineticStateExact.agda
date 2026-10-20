module DASHI.Biology.BH4CompartmentKineticStateExact where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Quantitative evidence coordinates for the BH4 open system.
--
-- Values are useful only together with source, same-object, compartment and
-- measurement-time coordinates.  An unresolved coordinate is not a measured
-- zero and may not be substituted into a promoted flux calculation.
------------------------------------------------------------------------

data ParameterPaymentStatus : Set where
  measuredParameter : ParameterPaymentStatus
  derivedParameter : ParameterPaymentStatus
  boundedLiteratureParameter : ParameterPaymentStatus
  unresolvedParameter : ParameterPaymentStatus

data BH4ParameterKind : Set where
  poolAmount : BH4ParameterKind
  poolConcentration : BH4ParameterKind
  reactionFlux : BH4ParameterKind
  kineticConstant : BH4ParameterKind
  enzymeAbundance : BH4ParameterKind
  enzymeActivity : BH4ParameterKind
  transportFlux : BH4ParameterKind
  oxidationFlux : BH4ParameterKind
  redoxRatio : BH4ParameterKind
  substrateAmount : BH4ParameterKind
  productAmount : BH4ParameterKind

record QuantitativeInterval : Set where
  constructor quantitative-interval
  field
    lowerNumerator : Nat
    upperNumerator : Nat
    scaleReference : String
    unitReference : String

open QuantitativeInterval public

record BH4ParameterEvidence : Set where
  constructor bh4-parameter-evidence
  field
    parameterId : String
    kind : BH4ParameterKind
    valueInterval : QuantitativeInterval
    paymentStatus : ParameterPaymentStatus
    sourceReference : String
    sameObjectReference : String
    compartmentReference : String
    measurementTimeReference : String
    methodReference : String
    directlyMeasured : Bool
    usableForJointFluxWitness : Bool

open BH4ParameterEvidence public

unresolvedInterval : QuantitativeInterval
unresolvedInterval = quantitative-interval 0 0 "unresolved-not-zero" "unresolved"

unresolvedBH4Pool : BH4ParameterEvidence
unresolvedBH4Pool =
  bh4-parameter-evidence
    "BH4_POOL"
    poolConcentration
    unresolvedInterval
    unresolvedParameter
    "no source-specific quantitative value admitted yet"
    "same-object state not yet paid"
    "compartment unresolved"
    "measurement time unresolved"
    "method unresolved"
    false
    false

unresolvedQDPRFlux : BH4ParameterEvidence
unresolvedQDPRFlux =
  bh4-parameter-evidence
    "QDPR_RHEA32253_FLUX"
    reactionFlux
    unresolvedInterval
    unresolvedParameter
    "reaction identity paid; kinetic/flux source not yet admitted"
    "RHEA:32253 identity only"
    "compartment unresolved"
    "measurement time unresolved"
    "method unresolved"
    false
    false

record BH4QuantitativeState : Set where
  constructor bh4-quantitative-state
  field
    systemState : System.BH4SystemState
    parameters : List BH4ParameterEvidence
    allRequiredSameObjectCoordinatesPaid : Bool
    allRequiredCompartmentsPaid : Bool
    allRequiredMeasurementTimesPaid : Bool
    allRequiredFluxBoundsPaid : Bool

open BH4QuantitativeState public

record BH4ParameterBoundary : Set where
  constructor bh4-parameter-boundary
  field
    unresolvedParameterMayBeReadAsMeasuredZero : Bool
    unresolvedParameterMayBeReadAsMeasuredZeroIsFalse :
      unresolvedParameterMayBeReadAsMeasuredZero ≡ false
    sameMoleculeDifferentCompartmentMayBeCollapsed : Bool
    sameMoleculeDifferentCompartmentMayBeCollapsedIsFalse :
      sameMoleculeDifferentCompartmentMayBeCollapsed ≡ false
    valuesFromDifferentMeasurementTimesCreateSameStateWitness : Bool
    valuesFromDifferentMeasurementTimesCreateSameStateWitnessIsFalse :
      valuesFromDifferentMeasurementTimesCreateSameStateWitness ≡ false
    literatureBoundIsDirectMeasurement : Bool
    literatureBoundIsDirectMeasurementIsFalse : literatureBoundIsDirectMeasurement ≡ false
    reactionIdentityCreatesKineticConstant : Bool
    reactionIdentityCreatesKineticConstantIsFalse : reactionIdentityCreatesKineticConstant ≡ false
    proteinAbundanceCreatesReactionFlux : Bool
    proteinAbundanceCreatesReactionFluxIsFalse : proteinAbundanceCreatesReactionFlux ≡ false

open BH4ParameterBoundary public

canonicalBH4ParameterBoundary : BH4ParameterBoundary
canonicalBH4ParameterBoundary =
  bh4-parameter-boundary false refl false refl false refl false refl false refl false refl

canonicalBH4CompartmentKineticStateReceipt : Receipt.GenericReceipt
canonicalBH4CompartmentKineticStateReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 compartment and kinetic evidence coordinates"
    "DASHI.Biology.BH4CompartmentKineticStateExact"
    "interval-valued pool/reaction/enzyme/transport/redox parameters with source + same-object + compartment + time coordinates"
    "lets measured, derived, literature-bounded and unresolved parameters coexist without silently replacing missing data by zero"
    "identity is not kinetics; abundance is not flux; cross-compartment or cross-time values do not create one same-object state; unresolved is not measured zero"
    "python3 scripts/acquire_bh4_parameter_evidence.py --template"
