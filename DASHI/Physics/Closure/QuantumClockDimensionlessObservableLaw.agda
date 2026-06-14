module DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge as Atomic
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift
import DASHI.Physics.Closure.QuantumClockSIObservableBridge as QuantumSI

------------------------------------------------------------------------
-- Quantum-clock dimensionless observable law.
--
-- This module is a typed dimension-law bridge only.  It imports the atomic
-- SI-second anchor, the quantum-clock SI observable bridge, and the
-- proper-time redshift bridge as provenance, then records the dimension
-- cancellation surfaces needed for
--
--   dim (omega0 * Delta tau) = 1
--   dim (Delta U / c^2)      = 1
--
-- Radians, cycles, phases, and fractional redshifts are treated as
-- dimensionless counting/readout conventions.  No numeric payload,
-- empirical receipt, apparatus receipt, or promotion token is constructed.

data ⊥ : Set where

data SIExponent : Set where
  -2 : SIExponent
  -1 : SIExponent
  0e : SIExponent
  +1 : SIExponent
  +2 : SIExponent

addExponent :
  SIExponent →
  SIExponent →
  SIExponent
addExponent -2 +2 = 0e
addExponent -2 0e = -2
addExponent -1 +1 = 0e
addExponent -1 0e = -1
addExponent 0e e = e
addExponent +1 -1 = 0e
addExponent +1 0e = +1
addExponent +2 -2 = 0e
addExponent +2 0e = +2
addExponent e 0e = e
addExponent e1 e2 = e1

record SIBaseDimensionVector : Set where
  field
    length :
      SIExponent

    mass :
      SIExponent

    time :
      SIExponent

    current :
      SIExponent

    temperature :
      SIExponent

    amount :
      SIExponent

    luminousIntensity :
      SIExponent

open SIBaseDimensionVector public

dimensionlessVector : SIBaseDimensionVector
dimensionlessVector =
  record
    { length = 0e
    ; mass = 0e
    ; time = 0e
    ; current = 0e
    ; temperature = 0e
    ; amount = 0e
    ; luminousIntensity = 0e
    }

siSecondDimension : SIBaseDimensionVector
siSecondDimension =
  record
    { length = 0e
    ; mass = 0e
    ; time = +1
    ; current = 0e
    ; temperature = 0e
    ; amount = 0e
    ; luminousIntensity = 0e
    }

siInverseSecondDimension : SIBaseDimensionVector
siInverseSecondDimension =
  record
    { length = 0e
    ; mass = 0e
    ; time = -1
    ; current = 0e
    ; temperature = 0e
    ; amount = 0e
    ; luminousIntensity = 0e
    }

siPotentialDimension : SIBaseDimensionVector
siPotentialDimension =
  record
    { length = +2
    ; mass = 0e
    ; time = -2
    ; current = 0e
    ; temperature = 0e
    ; amount = 0e
    ; luminousIntensity = 0e
    }

siInversePotentialDimension : SIBaseDimensionVector
siInversePotentialDimension =
  record
    { length = -2
    ; mass = 0e
    ; time = +2
    ; current = 0e
    ; temperature = 0e
    ; amount = 0e
    ; luminousIntensity = 0e
    }

addDimension :
  SIBaseDimensionVector →
  SIBaseDimensionVector →
  SIBaseDimensionVector
addDimension x y =
  record
    { length = addExponent (length x) (length y)
    ; mass = addExponent (mass x) (mass y)
    ; time = addExponent (time x) (time y)
    ; current = addExponent (current x) (current y)
    ; temperature = addExponent (temperature x) (temperature y)
    ; amount = addExponent (amount x) (amount y)
    ; luminousIntensity =
        addExponent (luminousIntensity x) (luminousIntensity y)
    }

record SIExponentCancellationSurface : Set where
  field
    leftExponent :
      SIExponent

    rightExponent :
      SIExponent

    combinedExponent :
      SIExponent

    combinedExponentIsZero :
      combinedExponent ≡ 0e

    cancellationReading :
      String

open SIExponentCancellationSurface public

canonicalInverseSecondSecondCancellation :
  SIExponentCancellationSurface
canonicalInverseSecondSecondCancellation =
  record
    { leftExponent = -1
    ; rightExponent = +1
    ; combinedExponent = addExponent -1 +1
    ; combinedExponentIsZero = refl
    ; cancellationReading =
        "inverse-second plus second exponent cancels to the zero SI time exponent"
    }

canonicalPotentialOverCSquaredCancellation :
  SIExponentCancellationSurface
canonicalPotentialOverCSquaredCancellation =
  record
    { leftExponent = +2
    ; rightExponent = -2
    ; combinedExponent = addExponent +2 -2
    ; combinedExponentIsZero = refl
    ; cancellationReading =
        "m^2 s^-2 plus the inverse c^2 dimension m^-2 s^2 cancels"
    }

phaseProductDimension :
  SIBaseDimensionVector
phaseProductDimension =
  addDimension siInverseSecondDimension siSecondDimension

phaseProductDimensionless :
  phaseProductDimension ≡ dimensionlessVector
phaseProductDimensionless =
  refl

redshiftRatioDimension :
  SIBaseDimensionVector
redshiftRatioDimension =
  addDimension siPotentialDimension siInversePotentialDimension

redshiftRatioDimensionless :
  redshiftRatioDimension ≡ dimensionlessVector
redshiftRatioDimensionless =
  refl

data DimensionlessObservableSurface : Set where
  phaseOmega0DeltaTauSurface :
    DimensionlessObservableSurface

  redshiftDeltaUOverCSquaredSurface :
    DimensionlessObservableSurface

  radianCountSurface :
    DimensionlessObservableSurface

  cycleCountSurface :
    DimensionlessObservableSurface

record DimensionlessObservableLawSurface : Set where
  field
    surface :
      DimensionlessObservableSurface

    lawLabel :
      String

    observableDimension :
      SIBaseDimensionVector

    observableDimensionless :
      observableDimension ≡ dimensionlessVector

    sourceReading :
      String

open DimensionlessObservableLawSurface public

phaseOmega0DeltaTauDimensionlessLaw :
  DimensionlessObservableLawSurface
phaseOmega0DeltaTauDimensionlessLaw =
  record
    { surface = phaseOmega0DeltaTauSurface
    ; lawLabel = "dim(omega0 * Delta tau) = dimensionless"
    ; observableDimension = phaseProductDimension
    ; observableDimensionless = refl
    ; sourceReading =
        "omega0 is angular frequency with inverse-second SI dimension; Delta tau is proper time with second SI dimension"
    }

redshiftDeltaUOverCSquaredDimensionlessLaw :
  DimensionlessObservableLawSurface
redshiftDeltaUOverCSquaredDimensionlessLaw =
  record
    { surface = redshiftDeltaUOverCSquaredSurface
    ; lawLabel = "dim(Delta U / c^2) = dimensionless"
    ; observableDimension = redshiftRatioDimension
    ; observableDimensionless = refl
    ; sourceReading =
        "Delta U and c^2 both carry the specific-energy/potential dimension m^2 s^-2"
    }

radianDimensionlessLaw :
  DimensionlessObservableLawSurface
radianDimensionlessLaw =
  record
    { surface = radianCountSurface
    ; lawLabel = "radian phase readout is dimensionless"
    ; observableDimension = dimensionlessVector
    ; observableDimensionless = refl
    ; sourceReading =
        "radian is recorded as a phase-count convention, not an independent SI base dimension"
    }

cycleDimensionlessLaw :
  DimensionlessObservableLawSurface
cycleDimensionlessLaw =
  record
    { surface = cycleCountSurface
    ; lawLabel = "cycle count is dimensionless"
    ; observableDimension = dimensionlessVector
    ; observableDimensionless = refl
    ; sourceReading =
        "cycle counts the same dimensionless phase observable under a different readout convention"
    }

record AngularReadoutConvention : Set where
  field
    radianLaw :
      DimensionlessObservableLawSurface

    radianLawIsCanonical :
      radianLaw ≡ radianDimensionlessLaw

    cycleLaw :
      DimensionlessObservableLawSurface

    cycleLawIsCanonical :
      cycleLaw ≡ cycleDimensionlessLaw

    radianAndCycleBothDimensionless :
      Bool

    radianAndCycleBothDimensionlessIsTrue :
      radianAndCycleBothDimensionless ≡ true

    note :
      String

open AngularReadoutConvention public

canonicalAngularReadoutConvention :
  AngularReadoutConvention
canonicalAngularReadoutConvention =
  record
    { radianLaw = radianDimensionlessLaw
    ; radianLawIsCanonical = refl
    ; cycleLaw = cycleDimensionlessLaw
    ; cycleLawIsCanonical = refl
    ; radianAndCycleBothDimensionless = true
    ; radianAndCycleBothDimensionlessIsTrue = refl
    ; note =
        "rad and cycle are dimensionless readout conventions; neither unlocks numeric calibration or promotion"
    }

data NumericQuantumClockPayload : Set where

data EmpiricalQuantumClockRedshiftReceipt : Set where

data DimensionlessObservablePromotionToken : Set where

numericQuantumClockPayloadUnavailableHere :
  NumericQuantumClockPayload →
  ⊥
numericQuantumClockPayloadUnavailableHere ()

empiricalQuantumClockRedshiftReceiptUnavailableHere :
  EmpiricalQuantumClockRedshiftReceipt →
  ⊥
empiricalQuantumClockRedshiftReceiptUnavailableHere ()

dimensionlessObservablePromotionTokenUnavailableHere :
  DimensionlessObservablePromotionToken →
  ⊥
dimensionlessObservablePromotionTokenUnavailableHere ()

record DimensionlessLawFailClosedGuards : Set where
  field
    numericPayloadClaimed :
      Bool

    numericPayloadClaimedIsFalse :
      numericPayloadClaimed ≡ false

    empiricalReceiptClaimed :
      Bool

    empiricalReceiptClaimedIsFalse :
      empiricalReceiptClaimed ≡ false

    empiricalPromotionClaimed :
      Bool

    empiricalPromotionClaimedIsFalse :
      empiricalPromotionClaimed ≡ false

    exactNumericPredictionClaimed :
      Bool

    exactNumericPredictionClaimedIsFalse :
      exactNumericPredictionClaimed ≡ false

    externalCalibrationStillRequired :
      Bool

    externalCalibrationStillRequiredIsTrue :
      externalCalibrationStillRequired ≡ true

open DimensionlessLawFailClosedGuards public

canonicalDimensionlessLawFailClosedGuards :
  DimensionlessLawFailClosedGuards
canonicalDimensionlessLawFailClosedGuards =
  record
    { numericPayloadClaimed = false
    ; numericPayloadClaimedIsFalse = refl
    ; empiricalReceiptClaimed = false
    ; empiricalReceiptClaimedIsFalse = refl
    ; empiricalPromotionClaimed = false
    ; empiricalPromotionClaimedIsFalse = refl
    ; exactNumericPredictionClaimed = false
    ; exactNumericPredictionClaimedIsFalse = refl
    ; externalCalibrationStillRequired = true
    ; externalCalibrationStillRequiredIsTrue = refl
    }

record QuantumClockDimensionlessObservableLaw : Set where
  field
    atomicClockBridge :
      Atomic.AtomicClockSISecondCalibrationBridge

    atomicClockBridgeIsCanonical :
      atomicClockBridge
      ≡
      Atomic.canonicalAtomicClockSISecondCalibrationBridge

    quantumSIObservableBridge :
      QuantumSI.QuantumClockSIObservableBridge

    quantumSIObservableBridgeIsCanonical :
      quantumSIObservableBridge
      ≡
      QuantumSI.canonicalQuantumClockSIObservableBridge

    properTimeRedshiftBridge :
      Redshift.QuantumClockProperTimeRedshiftBridge

    properTimeRedshiftBridgeIsCanonical :
      properTimeRedshiftBridge
      ≡
      Redshift.canonicalQuantumClockProperTimeRedshiftBridge

    inverseSecondSecondCancellation :
      SIExponentCancellationSurface

    inverseSecondSecondCancellationIsCanonical :
      inverseSecondSecondCancellation
      ≡
      canonicalInverseSecondSecondCancellation

    potentialOverCSquaredCancellation :
      SIExponentCancellationSurface

    potentialOverCSquaredCancellationIsCanonical :
      potentialOverCSquaredCancellation
      ≡
      canonicalPotentialOverCSquaredCancellation

    phaseLaw :
      DimensionlessObservableLawSurface

    phaseLawIsCanonical :
      phaseLaw ≡ phaseOmega0DeltaTauDimensionlessLaw

    redshiftLaw :
      DimensionlessObservableLawSurface

    redshiftLawIsCanonical :
      redshiftLaw ≡ redshiftDeltaUOverCSquaredDimensionlessLaw

    angularConvention :
      AngularReadoutConvention

    angularConventionIsCanonical :
      angularConvention ≡ canonicalAngularReadoutConvention

    failClosedGuards :
      DimensionlessLawFailClosedGuards

    failClosedGuardsAreCanonical :
      failClosedGuards ≡ canonicalDimensionlessLawFailClosedGuards

    phaseDimensionless :
      observableDimension phaseLaw ≡ dimensionlessVector

    redshiftDimensionless :
      observableDimension redshiftLaw ≡ dimensionlessVector

    noNumericPayload :
      NumericQuantumClockPayload →
      ⊥

    noEmpiricalReceipt :
      EmpiricalQuantumClockRedshiftReceipt →
      ⊥

    noPromotionToken :
      DimensionlessObservablePromotionToken →
      ⊥

    lawReading :
      List String

open QuantumClockDimensionlessObservableLaw public

canonicalQuantumClockDimensionlessObservableLaw :
  QuantumClockDimensionlessObservableLaw
canonicalQuantumClockDimensionlessObservableLaw =
  record
    { atomicClockBridge =
        Atomic.canonicalAtomicClockSISecondCalibrationBridge
    ; atomicClockBridgeIsCanonical =
        refl
    ; quantumSIObservableBridge =
        QuantumSI.canonicalQuantumClockSIObservableBridge
    ; quantumSIObservableBridgeIsCanonical =
        refl
    ; properTimeRedshiftBridge =
        Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    ; properTimeRedshiftBridgeIsCanonical =
        refl
    ; inverseSecondSecondCancellation =
        canonicalInverseSecondSecondCancellation
    ; inverseSecondSecondCancellationIsCanonical =
        refl
    ; potentialOverCSquaredCancellation =
        canonicalPotentialOverCSquaredCancellation
    ; potentialOverCSquaredCancellationIsCanonical =
        refl
    ; phaseLaw =
        phaseOmega0DeltaTauDimensionlessLaw
    ; phaseLawIsCanonical =
        refl
    ; redshiftLaw =
        redshiftDeltaUOverCSquaredDimensionlessLaw
    ; redshiftLawIsCanonical =
        refl
    ; angularConvention =
        canonicalAngularReadoutConvention
    ; angularConventionIsCanonical =
        refl
    ; failClosedGuards =
        canonicalDimensionlessLawFailClosedGuards
    ; failClosedGuardsAreCanonical =
        refl
    ; phaseDimensionless =
        refl
    ; redshiftDimensionless =
        refl
    ; noNumericPayload =
        numericQuantumClockPayloadUnavailableHere
    ; noEmpiricalReceipt =
        empiricalQuantumClockRedshiftReceiptUnavailableHere
    ; noPromotionToken =
        dimensionlessObservablePromotionTokenUnavailableHere
    ; lawReading =
        "Imported provenance: atomic SI-second bridge, quantum SI observable bridge, and proper-time redshift bridge."
        ∷ "SI exponent addition surface: inverse-second plus second cancels for omega0 * Delta tau."
        ∷ "SI exponent cancellation surface: Delta U divided by c^2 cancels m^2 s^-2 against m^2 s^-2."
        ∷ "Phase law: dim(omega0 * Delta tau) is dimensionless."
        ∷ "Redshift law: dim(Delta U / c^2) is dimensionless."
        ∷ "Radian and cycle are dimensionless readout/count conventions."
        ∷ "Fail-closed guards block numeric payload, empirical receipt, exact numeric prediction, and promotion."
        ∷ []
    }

canonicalPhaseObservableDimensionless :
  observableDimension
    (phaseLaw canonicalQuantumClockDimensionlessObservableLaw)
  ≡
  dimensionlessVector
canonicalPhaseObservableDimensionless =
  refl

canonicalRedshiftObservableDimensionless :
  observableDimension
    (redshiftLaw canonicalQuantumClockDimensionlessObservableLaw)
  ≡
  dimensionlessVector
canonicalRedshiftObservableDimensionless =
  refl

canonicalRadianConventionDimensionless :
  observableDimension
    (radianLaw
      (angularConvention canonicalQuantumClockDimensionlessObservableLaw))
  ≡
  dimensionlessVector
canonicalRadianConventionDimensionless =
  refl

canonicalCycleConventionDimensionless :
  observableDimension
    (cycleLaw
      (angularConvention canonicalQuantumClockDimensionlessObservableLaw))
  ≡
  dimensionlessVector
canonicalCycleConventionDimensionless =
  refl

canonicalDimensionlessLawNoNumericPayloadClaim :
  numericPayloadClaimed
    (failClosedGuards canonicalQuantumClockDimensionlessObservableLaw)
  ≡
  false
canonicalDimensionlessLawNoNumericPayloadClaim =
  refl

canonicalDimensionlessLawNoEmpiricalReceiptClaim :
  empiricalReceiptClaimed
    (failClosedGuards canonicalQuantumClockDimensionlessObservableLaw)
  ≡
  false
canonicalDimensionlessLawNoEmpiricalReceiptClaim =
  refl

canonicalDimensionlessLawNoEmpiricalPromotionClaim :
  empiricalPromotionClaimed
    (failClosedGuards canonicalQuantumClockDimensionlessObservableLaw)
  ≡
  false
canonicalDimensionlessLawNoEmpiricalPromotionClaim =
  refl

canonicalDimensionlessLawStillRequiresExternalCalibration :
  externalCalibrationStillRequired
    (failClosedGuards canonicalQuantumClockDimensionlessObservableLaw)
  ≡
  true
canonicalDimensionlessLawStillRequiresExternalCalibration =
  refl
