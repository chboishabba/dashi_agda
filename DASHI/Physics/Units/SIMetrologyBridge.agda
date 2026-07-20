module DASHI.Physics.Units.SIMetrologyBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Units.SI using
  ( Dimension; DecimalScale; Quantity; Unit
  ; Measurement; measurement
  )
open import DASHI.Physics.Laws.ConstantsMetrologyBoundary using
  ( QuantityRole; baseQuantity; derivedQuantity; constitutiveParameter
  ; DimensionalQuantitySystem
  ; ConstantAuthority; definitionExact; experimentallyMeasured; modelDerived
  )

------------------------------------------------------------------------
-- Existential packaging lets the generic metrology boundary carry quantities
-- while preserving each quantity's hidden dimension and decimal scale.

record AnySIQuantity : Set₁ where
  constructor anySI
  field
    dimension : Dimension
    scale : DecimalScale
    quantity : Quantity dimension scale
    unit : Unit dimension
    role : QuantityRole

record AnySIMeasurement : Set₁ where
  constructor anyMeasurement
  field
    dimension : Dimension
    scale : DecimalScale
    measurement : Measurement dimension scale
    authority : ConstantAuthority

SIValue : Set
SIValue = Nat

sameDimension : AnySIQuantity → AnySIQuantity → Set
sameDimension x y = AnySIQuantity.dimension x ≡ AnySIQuantity.dimension y

sameUnitDimension : AnySIQuantity → AnySIQuantity → Set
sameUnitDimension = sameDimension

record SIRegistry : Set₁ where
  field
    QuantityId : Set
    quantity : QuantityId → AnySIQuantity
    source : QuantityId → String
    version : QuantityId → String
    authority : QuantityId → ConstantAuthority

record SIConversionReceipt (source target : AnySIQuantity) : Set where
  field
    dimensionsAgree : AnySIQuantity.dimension source ≡ AnySIQuantity.dimension target
    exactScaleFactor : Nat
    conversionLaw : Set

record SIMetrologyAuthority : Set where
  field
    baseUnitsDefinitionExact : ConstantAuthority
    measuredParametersMeasured : ConstantAuthority
    fittedChemistryModelDerived : ConstantAuthority

siMetrologyAuthority : SIMetrologyAuthority
siMetrologyAuthority = record
  { baseUnitsDefinitionExact = definitionExact
  ; measuredParametersMeasured = experimentallyMeasured
  ; fittedChemistryModelDerived = modelDerived
  }

------------------------------------------------------------------------
-- The concrete SI system refines the repository-wide generic boundary. A full
-- arithmetic instance is deliberately separated from the dimension registry:
-- dimensional validity is exact even when a measured value has uncertainty.

record SIQuantitySystemReceipt : Set₁ where
  field
    quantitiesCarryDimensions : Set
    unitsCarryDimensions : Set
    unlikeDimensionsCannotShareTypedAddition : Set
    conversionsPreserveDimension : Set
    measurementsCarrySourceVersionUncertainty : Set

siQuantitySystemReceipt : SIQuantitySystemReceipt
siQuantitySystemReceipt = record
  { quantitiesCarryDimensions = AnySIQuantity
  ; unitsCarryDimensions = AnySIQuantity
  ; unlikeDimensionsCannotShareTypedAddition = sameDimension
  ; conversionsPreserveDimension = SIConversionReceipt
  ; measurementsCarrySourceVersionUncertainty = AnySIMeasurement
  }
