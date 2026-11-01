module DASHI.Physics.Laws.ConstantsMetrologyBoundary where

-- Mathematical laws are dimensionally and numerically incomplete until their
-- quantities, units, constants, conventions, and calibration authority are
-- fixed.  Exact SI definitions and measured constants are different statuses.
data ConstantAuthority : Set where
  definitionExact       : ConstantAuthority
  experimentallyMeasured : ConstantAuthority
  conventionDependent   : ConstantAuthority
  modelDerived          : ConstantAuthority
  candidateOnly         : ConstantAuthority

data QuantityRole : Set where
  baseQuantity       : QuantityRole
  derivedQuantity    : QuantityRole
  dimensionlessRatio : QuantityRole
  conversionFactor   : QuantityRole
  couplingParameter  : QuantityRole
  initialCondition   : QuantityRole
  constitutiveParameter : QuantityRole

record DimensionalQuantitySystem : Set₁ where
  field
    Quantity   : Set
    Dimension  : Set
    Unit       : Set
    Value      : Set

    dimensionOf : Quantity → Dimension
    unitOf      : Quantity → Unit
    valueOf     : Quantity → Value
    roleOf      : Quantity → QuantityRole

    CompatibleUnits : Unit → Unit → Set
    ConvertsTo      : Unit → Unit → Value → Value
    Dimensionless   : Quantity → Set

record PhysicalConstantRegistry : Set₁ where
  field
    Constant    : Set
    Symbol      : Set
    Value       : Set
    Unit        : Set
    Uncertainty : Set
    Source      : Set
    Version     : Set

    symbol      : Constant → Symbol
    value       : Constant → Value
    unit        : Constant → Unit
    uncertainty : Constant → Uncertainty
    source      : Constant → Source
    version     : Constant → Version
    authority   : Constant → ConstantAuthority

record CalibrationChain : Set₁ where
  field
    Instrument  : Set
    Reference   : Set
    Measurement : Set
    Correction  : Set
    Uncertainty : Set

    calibrate   : Instrument → Reference → Correction
    measure     : Instrument → Measurement
    corrected   : Correction → Measurement → Measurement
    uncertainty : Instrument → Reference → Uncertainty
    TraceableToReference : Instrument → Reference → Set

record UnitConventionBridge : Set₁ where
  field
    SourceConvention : Set
    TargetConvention : Set
    Quantity         : Set
    ConvertedQuantity : Set

    convert : SourceConvention → TargetConvention → Quantity → ConvertedQuantity
    invertibleOnDomain : SourceConvention → TargetConvention → Set
    preservesDimension : Quantity → Set

record DimensionlessClosure : Set₁ where
  field
    Quantity : Set
    Combination : Set
    Ratio : Set

    combine : Combination → Quantity → Ratio
    DimensionlessCombination : Combination → Set
    InvariantUnderUnitChange : Combination → Set

record MetrologyAuthorityBoundary : Set₁ where
  field
    exactDefinitionIsNotMeasuredPrecision : Set
    measuredValueRequiresVersionAndUncertainty : Set
    naturalUnitsDoNotEraseDimensions : Set
    unitConversionIsNotPhysicalDerivation : Set
    fittedParameterIsNotFundamentalConstant : Set
    dimensionlessNumericalCoincidenceIsNotMechanism : Set
    empiricalPredictionRequiresCalibrationChain : Set
