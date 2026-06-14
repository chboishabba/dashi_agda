module DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockSIObservableBridge as QuantumSI

------------------------------------------------------------------------
-- Quantum-clock / proper-time redshift bridge.
--
-- This module records the observable-law contact point only.  It packages
-- the two leading uniform-field labels
--
--   Delta phi_grav = omega0 * Delta tau_grav
--   Delta tau_grav = (g h / c^2) * Delta t_coord
--
-- together with unit/dimension bookkeeping and dependency guards.  It does
-- not construct an empirical redshift result, local apparatus receipt, SI
-- exact-payload authority, or promotion token.
-- It does not construct Candidate256PhysicalCalibrationExternalReceipt; W4
-- physical calibration remains gated by the external authority receipt.

data ⊥ : Set where

data ProperTimeRedshiftBridgeStatus : Set where
  symbolicProperTimeRedshiftObservableAwaitingApparatus :
    ProperTimeRedshiftBridgeStatus

canonicalSpeedOfLightRegistrySourceRef : String
canonicalSpeedOfLightRegistrySourceRef =
  "DASHI.Constants.Registry.canonicalSIDefiningConstants.c"

leadingUniformFieldRedshiftBoundaryLabel : String
leadingUniformFieldRedshiftBoundaryLabel =
  "Delta f / f = Delta U / c^2; G not needed for leading uniform-field redshift"

properTimeRedshiftPromoted : Bool
properTimeRedshiftPromoted =
  false

properTimeRedshiftPromotedIsFalse :
  properTimeRedshiftPromoted ≡ false
properTimeRedshiftPromotedIsFalse =
  refl

data RedshiftLawSurface : Set where
  gravitationalPhaseFromProperTime :
    RedshiftLawSurface

  leadingUniformFieldProperTimeShift :
    RedshiftLawSurface

  leadingUniformFieldFractionalRate :
    RedshiftLawSurface

record ProperTimeRedshiftLawSurfaces : Set where
  field
    phaseLaw :
      RedshiftLawSurface

    phaseLawLabel :
      String

    phaseLawLabelIsExact :
      phaseLawLabel ≡ "Delta phi_grav = omega0 * Delta tau_grav"

    properTimeLaw :
      RedshiftLawSurface

    properTimeLawLabel :
      String

    properTimeLawLabelIsExact :
      properTimeLawLabel
      ≡
      "Delta tau_grav = (g h / c^2) * Delta t_coord"

    fractionalRateLaw :
      RedshiftLawSurface

    fractionalRateLawLabel :
      String

    fractionalRateLawLabelIsExact :
      fractionalRateLawLabel ≡ "Delta tau_grav / Delta t_coord = g h / c^2"

    uniformFieldApproximationDeclared :
      Bool

    uniformFieldApproximationDeclaredIsTrue :
      uniformFieldApproximationDeclared ≡ true

    observableLawOnly :
      Bool

    observableLawOnlyIsTrue :
      observableLawOnly ≡ true

open ProperTimeRedshiftLawSurfaces public

canonicalProperTimeRedshiftLawSurfaces :
  ProperTimeRedshiftLawSurfaces
canonicalProperTimeRedshiftLawSurfaces =
  record
    { phaseLaw =
        gravitationalPhaseFromProperTime
    ; phaseLawLabel =
        "Delta phi_grav = omega0 * Delta tau_grav"
    ; phaseLawLabelIsExact =
        refl
    ; properTimeLaw =
        leadingUniformFieldProperTimeShift
    ; properTimeLawLabel =
        "Delta tau_grav = (g h / c^2) * Delta t_coord"
    ; properTimeLawLabelIsExact =
        refl
    ; fractionalRateLaw =
        leadingUniformFieldFractionalRate
    ; fractionalRateLawLabel =
        "Delta tau_grav / Delta t_coord = g h / c^2"
    ; fractionalRateLawLabelIsExact =
        refl
    ; uniformFieldApproximationDeclared =
        true
    ; uniformFieldApproximationDeclaredIsTrue =
        refl
    ; observableLawOnly =
        true
    ; observableLawOnlyIsTrue =
        refl
    }

record ProperTimeRedshiftVariables : Set where
  field
    deltaPhiGrav :
      String

    omega0 :
      String

    deltaTauGrav :
      String

    g :
      String

    h :
      String

    c :
      String

    deltaTCoord :
      String

    localPotentialDifference :
      String

    apparatusWorldlinePair :
      String

open ProperTimeRedshiftVariables public

canonicalProperTimeRedshiftVariables :
  ProperTimeRedshiftVariables
canonicalProperTimeRedshiftVariables =
  record
    { deltaPhiGrav =
        "Delta phi_grav"
    ; omega0 =
        "omega0"
    ; deltaTauGrav =
        "Delta tau_grav"
    ; g =
        "g"
    ; h =
        "h"
    ; c =
        "c"
    ; deltaTCoord =
        "Delta t_coord"
    ; localPotentialDifference =
        "Delta Phi_local = g h"
    ; apparatusWorldlinePair =
        "lower/upper clock worldline pair in a local uniform field"
    }

data RedshiftUnit : Set where
  radian :
    RedshiftUnit

  second :
    RedshiftUnit

  meter :
    RedshiftUnit

  meterPerSecondSquared :
    RedshiftUnit

  meterSquaredPerSecondSquared :
    RedshiftUnit

  radianPerSecond :
    RedshiftUnit

  dimensionlessRatio :
    RedshiftUnit

record SIExponent : Set where
  field
    positive :
      Nat

    negative :
      Nat

open SIExponent public

zeroExponent : SIExponent
zeroExponent =
  record
    { positive = zero
    ; negative = zero
    }

positiveOneExponent : SIExponent
positiveOneExponent =
  record
    { positive = suc zero
    ; negative = zero
    }

negativeOneExponent : SIExponent
negativeOneExponent =
  record
    { positive = zero
    ; negative = suc zero
    }

negativeTwoExponent : SIExponent
negativeTwoExponent =
  record
    { positive = zero
    ; negative = suc (suc zero)
    }

positiveTwoExponent : SIExponent
positiveTwoExponent =
  record
    { positive = suc (suc zero)
    ; negative = zero
    }

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
    { length = zeroExponent
    ; mass = zeroExponent
    ; time = zeroExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siSecondDimension : SIBaseDimensionVector
siSecondDimension =
  record
    { length = zeroExponent
    ; mass = zeroExponent
    ; time = positiveOneExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siRadPerSecondDimension : SIBaseDimensionVector
siRadPerSecondDimension =
  record
    { length = zeroExponent
    ; mass = zeroExponent
    ; time = negativeOneExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siMeterDimension : SIBaseDimensionVector
siMeterDimension =
  record
    { length = positiveOneExponent
    ; mass = zeroExponent
    ; time = zeroExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siAccelerationDimension : SIBaseDimensionVector
siAccelerationDimension =
  record
    { length = positiveOneExponent
    ; mass = zeroExponent
    ; time = negativeTwoExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

siPotentialDifferenceDimension : SIBaseDimensionVector
siPotentialDifferenceDimension =
  record
    { length = positiveTwoExponent
    ; mass = zeroExponent
    ; time = negativeTwoExponent
    ; current = zeroExponent
    ; temperature = zeroExponent
    ; amount = zeroExponent
    ; luminousIntensity = zeroExponent
    }

record RedshiftUnitAssignment : Set where
  field
    variableName :
      String

    unit :
      RedshiftUnit

    dimension :
      SIBaseDimensionVector

open RedshiftUnitAssignment public

dimensionlessAssignment :
  String →
  RedshiftUnitAssignment
dimensionlessAssignment name =
  record
    { variableName = name
    ; unit = dimensionlessRatio
    ; dimension = dimensionlessVector
    }

secondAssignment :
  String →
  RedshiftUnitAssignment
secondAssignment name =
  record
    { variableName = name
    ; unit = second
    ; dimension = siSecondDimension
    }

hertzLikeAssignment :
  String →
  RedshiftUnitAssignment
hertzLikeAssignment name =
  record
    { variableName = name
    ; unit = radianPerSecond
    ; dimension = siRadPerSecondDimension
    }

record ProperTimeRedshiftUnitSurface : Set where
  field
    phaseUnit :
      RedshiftUnitAssignment

    omega0Unit :
      RedshiftUnitAssignment

    properTimeUnit :
      RedshiftUnitAssignment

    coordinateTimeUnit :
      RedshiftUnitAssignment

    heightUnit :
      RedshiftUnitAssignment

    accelerationUnit :
      RedshiftUnitAssignment

    potentialDifferenceUnit :
      RedshiftUnitAssignment

    fractionalRedshiftUnit :
      RedshiftUnitAssignment

    phaseDimensionIsDimensionless :
      RedshiftUnitAssignment.dimension phaseUnit
      ≡
      dimensionlessVector

    omegaTimesProperTimeIsDimensionlessNarrative :
      String

    ghOverCSquaredIsDimensionlessNarrative :
      String

    coordinateTimeCarriesSISecondNarrative :
      String

open ProperTimeRedshiftUnitSurface public

canonicalProperTimeRedshiftUnitSurface :
  ProperTimeRedshiftUnitSurface
canonicalProperTimeRedshiftUnitSurface =
  record
    { phaseUnit =
        dimensionlessAssignment "Delta phi_grav"
    ; omega0Unit =
        hertzLikeAssignment "omega0"
    ; properTimeUnit =
        secondAssignment "Delta tau_grav"
    ; coordinateTimeUnit =
        secondAssignment "Delta t_coord"
    ; heightUnit =
        record
          { variableName = "h"
          ; unit = meter
          ; dimension = siMeterDimension
          }
    ; accelerationUnit =
        record
          { variableName = "g"
          ; unit = meterPerSecondSquared
          ; dimension = siAccelerationDimension
          }
    ; potentialDifferenceUnit =
        record
          { variableName = "g h"
          ; unit = meterSquaredPerSecondSquared
          ; dimension = siPotentialDifferenceDimension
          }
    ; fractionalRedshiftUnit =
        dimensionlessAssignment "g h / c^2"
    ; phaseDimensionIsDimensionless =
        refl
    ; omegaTimesProperTimeIsDimensionlessNarrative =
        "omega0 has inverse-second SI dimension and Delta tau_grav has second SI dimension, so their product is a phase/radian count."
    ; ghOverCSquaredIsDimensionlessNarrative =
        "g h and c^2 both carry m^2 s^-2 dimensions in the leading uniform-field approximation."
    ; coordinateTimeCarriesSISecondNarrative =
        "Delta t_coord is not promoted locally; it is recorded as an SI-second coordinate-time carrier required from apparatus context."
    }

record ProperTimeRedshiftExternalDependencies : Set where
  field
    omega0RequiresCs133ExactSIPayload :
      Bool

    omega0RequiresCs133ExactSIPayloadIsTrue :
      omega0RequiresCs133ExactSIPayload ≡ true

    speedOfLightRequiresExactSIPayload :
      Bool

    speedOfLightRequiresExactSIPayloadIsTrue :
      speedOfLightRequiresExactSIPayload ≡ true

    localAccelerationGRequiresApparatusData :
      Bool

    localAccelerationGRequiresApparatusDataIsTrue :
      localAccelerationGRequiresApparatusData ≡ true

    heightSeparationRequiresApparatusData :
      Bool

    heightSeparationRequiresApparatusDataIsTrue :
      heightSeparationRequiresApparatusData ≡ true

    localPotentialModelRequiresApparatusData :
      Bool

    localPotentialModelRequiresApparatusDataIsTrue :
      localPotentialModelRequiresApparatusData ≡ true

    coordinateTimeCarrierRequiresApparatusData :
      Bool

    coordinateTimeCarrierRequiresApparatusDataIsTrue :
      coordinateTimeCarrierRequiresApparatusData ≡ true

    noNewtonGNeededAtLeadingUniformField :
      Bool

    noNewtonGNeededAtLeadingUniformFieldIsTrue :
      noNewtonGNeededAtLeadingUniformField ≡ true

open ProperTimeRedshiftExternalDependencies public

canonicalProperTimeRedshiftExternalDependencies :
  ProperTimeRedshiftExternalDependencies
canonicalProperTimeRedshiftExternalDependencies =
  record
    { omega0RequiresCs133ExactSIPayload =
        true
    ; omega0RequiresCs133ExactSIPayloadIsTrue =
        refl
    ; speedOfLightRequiresExactSIPayload =
        true
    ; speedOfLightRequiresExactSIPayloadIsTrue =
        refl
    ; localAccelerationGRequiresApparatusData =
        true
    ; localAccelerationGRequiresApparatusDataIsTrue =
        refl
    ; heightSeparationRequiresApparatusData =
        true
    ; heightSeparationRequiresApparatusDataIsTrue =
        refl
    ; localPotentialModelRequiresApparatusData =
        true
    ; localPotentialModelRequiresApparatusDataIsTrue =
        refl
    ; coordinateTimeCarrierRequiresApparatusData =
        true
    ; coordinateTimeCarrierRequiresApparatusDataIsTrue =
        refl
    ; noNewtonGNeededAtLeadingUniformField =
        true
    ; noNewtonGNeededAtLeadingUniformFieldIsTrue =
        refl
    }

data CsOmega0ExactSIPayload : Set where

data SpeedOfLightExactSIPayload : Set where

data LocalAccelerationApparatusData : Set where

data HeightSeparationApparatusData : Set where

data LocalPotentialApparatusData : Set where

data CoordinateTimeApparatusData : Set where

data EmpiricalRedshiftReceipt : Set where

data ProperTimeRedshiftPromotionToken : Set where

csOmega0PayloadUnavailableHere :
  CsOmega0ExactSIPayload →
  ⊥
csOmega0PayloadUnavailableHere ()

speedOfLightPayloadUnavailableHere :
  SpeedOfLightExactSIPayload →
  ⊥
speedOfLightPayloadUnavailableHere ()

localAccelerationDataUnavailableHere :
  LocalAccelerationApparatusData →
  ⊥
localAccelerationDataUnavailableHere ()

heightDataUnavailableHere :
  HeightSeparationApparatusData →
  ⊥
heightDataUnavailableHere ()

localPotentialDataUnavailableHere :
  LocalPotentialApparatusData →
  ⊥
localPotentialDataUnavailableHere ()

coordinateTimeDataUnavailableHere :
  CoordinateTimeApparatusData →
  ⊥
coordinateTimeDataUnavailableHere ()

empiricalRedshiftReceiptUnavailableHere :
  EmpiricalRedshiftReceipt →
  ⊥
empiricalRedshiftReceiptUnavailableHere ()

properTimeRedshiftPromotionTokenUnavailableHere :
  ProperTimeRedshiftPromotionToken →
  ⊥
properTimeRedshiftPromotionTokenUnavailableHere ()

record ProperTimeRedshiftFailClosedGuards : Set where
  field
    empiricalReceiptClaimed :
      Bool

    empiricalReceiptClaimedIsFalse :
      empiricalReceiptClaimed ≡ false

    empiricalPromotionClaimed :
      Bool

    empiricalPromotionClaimedIsFalse :
      empiricalPromotionClaimed ≡ false

    grPromotionClaimed :
      Bool

    grPromotionClaimedIsFalse :
      grPromotionClaimed ≡ false

    exactNumericPredictionClaimed :
      Bool

    exactNumericPredictionClaimedIsFalse :
      exactNumericPredictionClaimed ≡ false

    externalApparatusStillRequired :
      Bool

    externalApparatusStillRequiredIsTrue :
      externalApparatusStillRequired ≡ true

open ProperTimeRedshiftFailClosedGuards public

canonicalProperTimeRedshiftFailClosedGuards :
  ProperTimeRedshiftFailClosedGuards
canonicalProperTimeRedshiftFailClosedGuards =
  record
    { empiricalReceiptClaimed =
        false
    ; empiricalReceiptClaimedIsFalse =
        refl
    ; empiricalPromotionClaimed =
        false
    ; empiricalPromotionClaimedIsFalse =
        refl
    ; grPromotionClaimed =
        false
    ; grPromotionClaimedIsFalse =
        refl
    ; exactNumericPredictionClaimed =
        false
    ; exactNumericPredictionClaimedIsFalse =
        refl
    ; externalApparatusStillRequired =
        true
    ; externalApparatusStillRequiredIsTrue =
        refl
    }

record QuantumClockProperTimeRedshiftBridge : Set where
  field
    status :
      ProperTimeRedshiftBridgeStatus

    quantumClockSIObservableBridge :
      QuantumSI.QuantumClockSIObservableBridge

    quantumClockSIObservableBridgeIsCanonical :
      quantumClockSIObservableBridge
      ≡
      QuantumSI.canonicalQuantumClockSIObservableBridge

    atomicClockSISecondCalibrationBridgeReference :
      String

    atomicClockSISecondCalibrationBridgeReferenceIsExact :
      atomicClockSISecondCalibrationBridgeReference
      ≡
      "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.canonicalAtomicClockSISecondCalibrationBridge"

    lawSurfaces :
      ProperTimeRedshiftLawSurfaces

    lawSurfacesAreCanonical :
      lawSurfaces ≡ canonicalProperTimeRedshiftLawSurfaces

    variables :
      ProperTimeRedshiftVariables

    variablesAreCanonical :
      variables ≡ canonicalProperTimeRedshiftVariables

    unitSurface :
      ProperTimeRedshiftUnitSurface

    unitSurfaceIsCanonical :
      unitSurface ≡ canonicalProperTimeRedshiftUnitSurface

    externalDependencies :
      ProperTimeRedshiftExternalDependencies

    externalDependenciesAreCanonical :
      externalDependencies ≡ canonicalProperTimeRedshiftExternalDependencies

    failClosedGuards :
      ProperTimeRedshiftFailClosedGuards

    failClosedGuardsAreCanonical :
      failClosedGuards ≡ canonicalProperTimeRedshiftFailClosedGuards

    phaseLawMatchesQuantumClockSILaw :
      ProperTimeRedshiftLawSurfaces.phaseLawLabel lawSurfaces
      ≡
      "Delta phi_grav = omega0 * Delta tau_grav"

    properTimeLawIsLeadingUniformField :
      ProperTimeRedshiftLawSurfaces.properTimeLawLabel lawSurfaces
      ≡
      "Delta tau_grav = (g h / c^2) * Delta t_coord"

    noLocalCsOmega0ExactSIPayload :
      CsOmega0ExactSIPayload →
      ⊥

    noLocalSpeedOfLightExactSIPayload :
      SpeedOfLightExactSIPayload →
      ⊥

    noLocalAccelerationData :
      LocalAccelerationApparatusData →
      ⊥

    noLocalHeightSeparationData :
      HeightSeparationApparatusData →
      ⊥

    noLocalPotentialData :
      LocalPotentialApparatusData →
      ⊥

    noLocalCoordinateTimeData :
      CoordinateTimeApparatusData →
      ⊥

    noEmpiricalRedshiftReceipt :
      EmpiricalRedshiftReceipt →
      ⊥

    noProperTimeRedshiftPromotionToken :
      ProperTimeRedshiftPromotionToken →
      ⊥

    bridgeReading :
      List String

open QuantumClockProperTimeRedshiftBridge public

canonicalQuantumClockProperTimeRedshiftBridge :
  QuantumClockProperTimeRedshiftBridge
canonicalQuantumClockProperTimeRedshiftBridge =
  record
    { status =
        symbolicProperTimeRedshiftObservableAwaitingApparatus
    ; quantumClockSIObservableBridge =
        QuantumSI.canonicalQuantumClockSIObservableBridge
    ; quantumClockSIObservableBridgeIsCanonical =
        refl
    ; atomicClockSISecondCalibrationBridgeReference =
        "DASHI.Physics.Closure.AtomicClockSISecondCalibrationBridge.canonicalAtomicClockSISecondCalibrationBridge"
    ; atomicClockSISecondCalibrationBridgeReferenceIsExact =
        refl
    ; lawSurfaces =
        canonicalProperTimeRedshiftLawSurfaces
    ; lawSurfacesAreCanonical =
        refl
    ; variables =
        canonicalProperTimeRedshiftVariables
    ; variablesAreCanonical =
        refl
    ; unitSurface =
        canonicalProperTimeRedshiftUnitSurface
    ; unitSurfaceIsCanonical =
        refl
    ; externalDependencies =
        canonicalProperTimeRedshiftExternalDependencies
    ; externalDependenciesAreCanonical =
        refl
    ; failClosedGuards =
        canonicalProperTimeRedshiftFailClosedGuards
    ; failClosedGuardsAreCanonical =
        refl
    ; phaseLawMatchesQuantumClockSILaw =
        refl
    ; properTimeLawIsLeadingUniformField =
        refl
    ; noLocalCsOmega0ExactSIPayload =
        csOmega0PayloadUnavailableHere
    ; noLocalSpeedOfLightExactSIPayload =
        speedOfLightPayloadUnavailableHere
    ; noLocalAccelerationData =
        localAccelerationDataUnavailableHere
    ; noLocalHeightSeparationData =
        heightDataUnavailableHere
    ; noLocalPotentialData =
        localPotentialDataUnavailableHere
    ; noLocalCoordinateTimeData =
        coordinateTimeDataUnavailableHere
    ; noEmpiricalRedshiftReceipt =
        empiricalRedshiftReceiptUnavailableHere
    ; noProperTimeRedshiftPromotionToken =
        properTimeRedshiftPromotionTokenUnavailableHere
    ; bridgeReading =
        "Observable law only: phase shift is carrier angular frequency times gravitational proper-time difference."
        ∷ "Leading uniform field only: proper-time difference is (g h / c^2) times coordinate-time interval."
        ∷ "Dimensional check: omega0 * Delta tau_grav is dimensionless phase."
        ∷ "Dimensional check: g h / c^2 is dimensionless, so multiplying by Delta t_coord returns time."
        ∷ "Exact SI dependencies required: Cs omega0 payload and exact speed-of-light payload."
        ∷ "Apparatus dependencies required: local g, height h, local potential model, and coordinate-time carrier."
        ∷ "No Newtonian G payload is needed for this leading uniform-field law surface."
        ∷ "No empirical redshift receipt, numeric prediction, GR promotion, or empirical promotion is constructed here."
        ∷ []
    }

canonicalRedshiftStatusIsFailClosed :
  status canonicalQuantumClockProperTimeRedshiftBridge
  ≡
  symbolicProperTimeRedshiftObservableAwaitingApparatus
canonicalRedshiftStatusIsFailClosed =
  refl

canonicalRedshiftPhaseLawExact :
  ProperTimeRedshiftLawSurfaces.phaseLawLabel
    (lawSurfaces canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  "Delta phi_grav = omega0 * Delta tau_grav"
canonicalRedshiftPhaseLawExact =
  refl

canonicalRedshiftProperTimeLawExact :
  ProperTimeRedshiftLawSurfaces.properTimeLawLabel
    (lawSurfaces canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  "Delta tau_grav = (g h / c^2) * Delta t_coord"
canonicalRedshiftProperTimeLawExact =
  refl

canonicalRedshiftNoNewtonGRequired :
  noNewtonGNeededAtLeadingUniformField
    (externalDependencies canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  true
canonicalRedshiftNoNewtonGRequired =
  refl

canonicalRedshiftRequiresCsOmega0 :
  omega0RequiresCs133ExactSIPayload
    (externalDependencies canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  true
canonicalRedshiftRequiresCsOmega0 =
  refl

canonicalRedshiftRequiresExactC :
  speedOfLightRequiresExactSIPayload
    (externalDependencies canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  true
canonicalRedshiftRequiresExactC =
  refl

canonicalRedshiftRequiresApparatusG :
  localAccelerationGRequiresApparatusData
    (externalDependencies canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  true
canonicalRedshiftRequiresApparatusG =
  refl

canonicalRedshiftRequiresApparatusHeight :
  heightSeparationRequiresApparatusData
    (externalDependencies canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  true
canonicalRedshiftRequiresApparatusHeight =
  refl

canonicalRedshiftEmpiricalReceiptFalse :
  empiricalReceiptClaimed
    (failClosedGuards canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  false
canonicalRedshiftEmpiricalReceiptFalse =
  refl

canonicalRedshiftEmpiricalPromotionFalse :
  empiricalPromotionClaimed
    (failClosedGuards canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  false
canonicalRedshiftEmpiricalPromotionFalse =
  refl

canonicalRedshiftGRPromotionFalse :
  grPromotionClaimed
    (failClosedGuards canonicalQuantumClockProperTimeRedshiftBridge)
  ≡
  false
canonicalRedshiftGRPromotionFalse =
  refl
