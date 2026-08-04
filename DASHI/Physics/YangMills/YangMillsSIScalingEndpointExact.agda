module DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Bureau International des Poids et Mesures,
-- "The International System of Units (SI)", ninth edition (2019),
-- current version 4.01, June 2026.
-- DOI: 10.59161/AUEZ1291.
--
-- Edgar Buckingham,
-- "On Physically Similar Systems; Illustrations of the Use of Dimensional
-- Equations", Physical Review 4 (1914), 345--376.
-- DOI: 10.1103/PhysRev.4.345.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- PURPOSE
-- Connect the existing mechanical-dimension and SI lanes to the Yang--Mills
-- terminal gap.  A lattice gap is dimensionless; multiplying by inverse lattice
-- spacing produces inverse length.  Conversion to SI mass or energy remains an
-- explicit hbar/c or hbar*c law and is never silently definitional.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Units.MechanicalDimensionExact as Mechanical
import DASHI.Physics.Units.PhysicalNormalizationExact as Normalization
open import DASHI.Physics.YangMills.CompactLieProofLevel

mechanicalToSI : Mechanical.MechanicalDimension → SI.Dimension
mechanicalToSI (Mechanical.dimension mass length time) =
  SI.dim length mass time SI.zeroI SI.zeroI SI.zeroI SI.zeroI

mechanicalDimensionlessToSI :
  mechanicalToSI Mechanical.dimensionless ≡ SI.Dimensionless
mechanicalDimensionlessToSI = refl

mechanicalLengthToSI :
  mechanicalToSI Mechanical.lengthDimension ≡ SI.Length
mechanicalLengthToSI = refl

mechanicalMassToSI :
  mechanicalToSI Mechanical.massDimension ≡ SI.Mass
mechanicalMassToSI = refl

mechanicalTimeToSI :
  mechanicalToSI Mechanical.timeDimension ≡ SI.Time
mechanicalTimeToSI = refl

mechanicalFrequencyToSI :
  mechanicalToSI Mechanical.frequencyDimension ≡ SI.Frequency
mechanicalFrequencyToSI = refl

mechanicalEnergyToSI :
  mechanicalToSI Mechanical.energyDimension ≡ SI.Energy
mechanicalEnergyToSI = refl

record SIIndexedQuantity
    (Scalar : Set)
    (dimension : SI.Dimension) : Set where
  constructor siQuantity
  field magnitude : Scalar

open SIIndexedQuantity public

mechanicalQuantityToSI :
  ∀ {Scalar dimension} →
  Mechanical.Quantity Scalar dimension →
  SIIndexedQuantity Scalar (mechanicalToSI dimension)
mechanicalQuantityToSI (Mechanical.quantity value) =
  siQuantity value

record YangMillsGapScales (Scalar : Set) : Set₁ where
  field
    multiply : Scalar → Scalar → Scalar

    dimensionlessLatticeGap :
      SIIndexedQuantity Scalar SI.Dimensionless

    inverseLatticeSpacing :
      SIIndexedQuantity Scalar (mechanicalToSI Mechanical.inverseLengthDimension)

    inverseCorrelationLength :
      SIIndexedQuantity Scalar (mechanicalToSI Mechanical.inverseLengthDimension)

    inverseCorrelationLengthDefinition :
      magnitude inverseCorrelationLength
      ≡ multiply
          (magnitude dimensionlessLatticeGap)
          (magnitude inverseLatticeSpacing)

open YangMillsGapScales public

record NaturalUnitConversion (Scalar : Set) : Set₁ where
  field
    inverseLengthToMass :
      SIIndexedQuantity Scalar
        (mechanicalToSI Mechanical.inverseLengthDimension) →
      SIIndexedQuantity Scalar SI.Mass

    inverseLengthToEnergy :
      SIIndexedQuantity Scalar
        (mechanicalToSI Mechanical.inverseLengthDimension) →
      SIIndexedQuantity Scalar SI.Energy

    hBarOverCConversionLaw : Set
    hBarOverCConversionLawEvidence : hBarOverCConversionLaw

    hBarTimesCConversionLaw : Set
    hBarTimesCConversionLawEvidence : hBarTimesCConversionLaw

    naturalUnitsSelected : Bool

open NaturalUnitConversion public

record SIYangMillsMassGap
    (Scalar : Set)
    (scales : YangMillsGapScales Scalar) : Set₁ where
  field
    conversion : NaturalUnitConversion Scalar

    massGap : SIIndexedQuantity Scalar SI.Mass
    massGapDefinition :
      massGap ≡ inverseLengthToMass conversion
        (inverseCorrelationLength scales)

    energyGap : SIIndexedQuantity Scalar SI.Energy
    energyGapDefinition :
      energyGap ≡ inverseLengthToEnergy conversion
        (inverseCorrelationLength scales)

    strictlyPositiveInPhysicalUnits : Set
    strictlyPositiveInPhysicalUnitsEvidence :
      strictlyPositiveInPhysicalUnits

    renormalizationSchemeMatching : Set
    renormalizationSchemeMatchingEvidence :
      renormalizationSchemeMatching

    schemeIndependence : Set
    schemeIndependenceEvidence : schemeIndependence

open SIYangMillsMassGap public

record YangMillsScaleNormalization
    (Scalar : Set) : Set₁ where
  field
    scaleAlgebra : Normalization.ScaleAlgebra Scalar
    latticeSpacing : Normalization.PositiveScale scaleAlgebra
    referenceVelocity : Normalization.PositiveScale scaleAlgebra

    dimensionlessActionNormalization : Set
    dimensionlessActionNormalizationEvidence :
      dimensionlessActionNormalization

    runningCouplingDimensionless : Set
    runningCouplingDimensionlessEvidence :
      runningCouplingDimensionless

    correlationLengthRescalesWithLatticeSpacing : Set
    correlationLengthRescalesWithLatticeSpacingEvidence :
      correlationLengthRescalesWithLatticeSpacing

open YangMillsScaleNormalization public

siDimensionsIntegrated : Bool
siDimensionsIntegrated = true

inverseLengthSilentlyIdentifiedWithSIMass : Bool
inverseLengthSilentlyIdentifiedWithSIMass = false

siDimensionsIntegratedIsTrue : siDimensionsIntegrated ≡ true
siDimensionsIntegratedIsTrue = refl

inverseLengthSilentlyIdentifiedWithSIMassIsFalse :
  inverseLengthSilentlyIdentifiedWithSIMass ≡ false
inverseLengthSilentlyIdentifiedWithSIMassIsFalse = refl

mechanicalToSIDimensionBridgeLevel : ProofLevel
mechanicalToSIDimensionBridgeLevel = machineChecked

yangMillsInverseCorrelationLengthLevel : ProofLevel
yangMillsInverseCorrelationLengthLevel = machineChecked

naturalUnitConversionLevel : ProofLevel
naturalUnitConversionLevel = conditional

siPhysicalGapPositivityAndSchemeIndependenceLevel : ProofLevel
siPhysicalGapPositivityAndSchemeIndependenceLevel = conditional
