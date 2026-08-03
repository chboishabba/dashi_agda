module DASHI.Physics.YangMills.BalabanClayT5MassScaleDimensionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: David J. Gross and Frank Wilczek.
-- Title: "Ultraviolet Behavior of Non-Abelian Gauge Theories".
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- Author: H. David Politzer.
-- Title: "Reliable Perturbative Results for Strong Interactions?".
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- PURPOSE
-- Refine the existing T5 dimensional-transmutation receipt.  Multiplying a
-- dimensionless lattice gap by inverse spacing first produces an inverse
-- correlation length.  Calling that object an SI mass additionally requires an
-- explicit hbar/c conversion (or an explicitly selected natural-unit system).
-- Renormalization scheme matching and scheme independence are separate from
-- this dimension theorem and remain visible obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ; _*_)

import DASHI.Physics.Units.MechanicalDimensionExact as Dimension
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMassTransportExact as T5
open import DASHI.Physics.YangMills.CompactLieProofLevel

inverseCorrelationLengthScale :
  T5.DimensionalTransmutationWitness →
  Dimension.Quantity ℚ Dimension.inverseLengthDimension
inverseCorrelationLengthScale witness =
  Dimension.quantity
    (T5.dimensionlessTerminalGap witness
      * T5.inverseTerminalSpacing witness)

inverseCorrelationLengthMagnitudeMatchesT5 :
  (witness : T5.DimensionalTransmutationWitness) →
  Dimension.magnitude (inverseCorrelationLengthScale witness)
  ≡ T5.terminalPhysicalMass
      (T5.dimensionlessTerminalGap witness)
      (T5.inverseTerminalSpacing witness)
inverseCorrelationLengthMagnitudeMatchesT5 witness = refl

record RenormalizationScheme : Set where
  field
    schemeName : String
    referenceScaleName : String
    latticeActionName : String

open RenormalizationScheme public

record SchemeSpecificMassInterpretation
    (witness : T5.DimensionalTransmutationWitness) : Set₁ where
  field
    scheme : RenormalizationScheme
    matchingFunction : ℚ → ℚ
    matchedDimensionlessGap : ℚ
    matchingFunctionMeaning :
      matchedDimensionlessGap
      ≡ matchingFunction (T5.dimensionlessTerminalGap witness)

open SchemeSpecificMassInterpretation public

record NaturalUnitMassConversion : Set₁ where
  field
    inverseLengthToMass :
      Dimension.Quantity ℚ Dimension.inverseLengthDimension →
      Dimension.Quantity ℚ Dimension.massDimension

    HBarOverCConversionLaw : Set
    hBarOverCConversionLaw : HBarOverCConversionLaw

    naturalUnitsSelected : Bool

open NaturalUnitMassConversion public

siMassFromGap :
  (conversion : NaturalUnitMassConversion) →
  (witness : T5.DimensionalTransmutationWitness) →
  Dimension.Quantity ℚ Dimension.massDimension
siMassFromGap conversion witness =
  inverseLengthToMass conversion (inverseCorrelationLengthScale witness)

------------------------------------------------------------------------
-- Scheme independence is a matching theorem, not a consequence of dimensions.
------------------------------------------------------------------------

record SchemeIndependenceObligation
    (witness : T5.DimensionalTransmutationWitness)
    (left right : SchemeSpecificMassInterpretation witness) : Set₁ where
  field
    conversionFactor : ℚ
    matchedMassesAgreeAfterConversion : Set
    agreementReceipt : matchedMassesAgreeAfterConversion

open SchemeIndependenceObligation public

inverseLengthDimensionTheoremLevel : ProofLevel
inverseLengthDimensionTheoremLevel = machineChecked

existingT5MassTransportReusedLevel : ProofLevel
existingT5MassTransportReusedLevel = machineChecked

naturalUnitMassConversionLevel : ProofLevel
naturalUnitMassConversionLevel = conditional

renormalizationSchemeMatchingLevel : ProofLevel
renormalizationSchemeMatchingLevel = conditional

schemeIndependenceProved : Bool
schemeIndependenceProved = false

inverseLengthSilentlyIdentifiedWithSIMass : Bool
inverseLengthSilentlyIdentifiedWithSIMass = false

schemeIndependenceProvedIsFalse :
  schemeIndependenceProved ≡ false
schemeIndependenceProvedIsFalse = refl

inverseLengthSilentlyIdentifiedWithSIMassIsFalse :
  inverseLengthSilentlyIdentifiedWithSIMass ≡ false
inverseLengthSilentlyIdentifiedWithSIMassIsFalse = refl
