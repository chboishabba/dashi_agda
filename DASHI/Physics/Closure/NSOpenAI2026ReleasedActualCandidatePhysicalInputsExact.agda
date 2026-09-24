module DASHI.Physics.Closure.NSOpenAI2026ReleasedActualCandidatePhysicalInputsExact where

------------------------------------------------------------------------
-- RELEASED ACTUAL-CANDIDATE PHYSICAL INPUT / CONSTRUCTION ATTACHMENT
--
-- Source inspected:
--   openai/NavierStokesAndEuler
--   commit f9e8bc5b38b6e212696e8a30e3e91517af887bbd
--
-- This owner makes the source-fixed construction coordinates explicit before
-- the native Agda port of ActualCandidateConstruction / ActualCandidateAssembly.
-- It also attaches the repository's reproducible NS experimental screen as a
-- SEPARATE validation surface.
--
-- Crucial firewall:
--   released analytic construction inputs != empirical CFD calibration.
-- The experimental screen can falsify/check numerical behaviour, but it cannot
-- inhabit the released candidate theorem or a Clay proposition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Units.MechanicalDimensionExact as Units

------------------------------------------------------------------------
-- 1. Exact released-source coordinates.
------------------------------------------------------------------------

releasedSourceCommit : String
releasedSourceCommit = "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"

actualCandidateConstructionOwner : String
actualCandidateConstructionOwner =
  "NavierStokes/ActualCandidateConstruction.lean"

actualCandidateAssemblyOwner : String
actualCandidateAssemblyOwner =
  "NavierStokes/ActualCandidateAssembly.lean"

r3ActualCandidateOwner : String
r3ActualCandidateOwner =
  "NavierStokes/R3/ActualCandidate.lean"

r3CandidateBreakdownOwner : String
r3CandidateBreakdownOwner =
  "NavierStokes/R3/CandidateBreakdown.lean"

periodicPaperOwner : String
periodicPaperOwner =
  "NavierStokes/PeriodicPaperTheorem.lean"

------------------------------------------------------------------------
-- 2. Dimensionless/rational construction constants copied from the released
--    theorem spine.  Fractions are represented exactly as Nat pairs.
------------------------------------------------------------------------

record PositiveFraction : Set where
  constructor positive-fraction
  field
    numerator denominator : Nat

open PositiveFraction public

selectedBudget : Nat
selectedBudget = zero

firstBandHardFloor : Nat
firstBandHardFloor = 4

residualBandOffset : Nat
residualBandOffset = 1

singularTime : PositiveFraction
singularTime = positive-fraction 1 1

earlyRestRadius : PositiveFraction
earlyRestRadius = positive-fraction 3 8

periodicCompressionHalfWidth : PositiveFraction
periodicCompressionHalfWidth = positive-fraction 1 4

periodicFundamentalHalfWidth : PositiveFraction
periodicFundamentalHalfWidth = positive-fraction 1 2

velocityParabolicExponent : Nat
velocityParabolicExponent = 1

timeParabolicExponent : Nat
timeParabolicExponent = 2

pressureParabolicExponent : Nat
pressureParabolicExponent = 2

forceParabolicExponent : Nat
forceParabolicExponent = 3

record ReleasedSelectedConstructionCoordinates : Set where
  field
    budget : Nat
    budgetIsZero : budget ≡ selectedBudget

    selectedThresholdOrigin : String
    firstBandRule : String
    residualBandRule : String

    singularTimeCoordinate : PositiveFraction
    singularTimeCoordinateIsOne :
      singularTimeCoordinate ≡ singularTime

    earlyRestCoordinate : PositiveFraction
    earlyRestCoordinateIsThreeEighths :
      earlyRestCoordinate ≡ earlyRestRadius

    periodicCompressionCoordinate : PositiveFraction
    periodicCompressionCoordinateIsQuarter :
      periodicCompressionCoordinate ≡ periodicCompressionHalfWidth

    delayedParabolicClock : String
    velocityScaling : String
    pressureScaling : String
    forceScaling : String

open ReleasedSelectedConstructionCoordinates public

canonicalReleasedSelectedConstructionCoordinates :
  ReleasedSelectedConstructionCoordinates
canonicalReleasedSelectedConstructionCoordinates = record
  { budget = selectedBudget
  ; budgetIsZero = refl
  ; selectedThresholdOrigin =
      "ActualCarrierGeometry.startingThreshold 0"
  ; firstBandRule =
      "max 4 (ActualCycleParameters.bandFloor selectedBudget selectedThreshold)"
  ; residualBandRule =
      "firstBand + 1"
  ; singularTimeCoordinate = singularTime
  ; singularTimeCoordinateIsOne = refl
  ; earlyRestCoordinate = earlyRestRadius
  ; earlyRestCoordinateIsThreeEighths = refl
  ; periodicCompressionCoordinate = periodicCompressionHalfWidth
  ; periodicCompressionCoordinateIsQuarter = refl
  ; delayedParabolicClock =
      "clock_l(t) = l^2*(t-1)+1, with l>1"
  ; velocityScaling =
      "u_l(t,x) = l * u(clock_l(t), l*x)"
  ; pressureScaling =
      "p_l(t,x) = l^2 * p(clock_l(t), l*x)"
  ; forceScaling =
      "f_l(t,x) = l^3 * f(clock_l(t), l*x)"
  }

------------------------------------------------------------------------
-- 3. SI / mechanical-dimension attachment.
--
-- The released proof is dimensionless/normalized analytically, but its NS
-- variables have standard mechanical dimensions.  Pressure in the equation
-- is the density-normalized (kinematic) pressure, hence L^2 T^-2.
------------------------------------------------------------------------

record ReleasedNSDimensionAttachment : Set where
  field
    viscosityDimension : Units.MechanicalDimension
    velocityDimension : Units.MechanicalDimension
    timeDimension : Units.MechanicalDimension
    spatialCoordinateDimension : Units.MechanicalDimension
    kinematicPressureDimension : Units.MechanicalDimension
    forcingDimension : Units.MechanicalDimension

    viscosityDimensionExact :
      viscosityDimension ≡ Units.kinematicViscosityDimension
    velocityDimensionExact :
      velocityDimension ≡ Units.velocityDimension
    timeDimensionExact :
      timeDimension ≡ Units.timeDimension
    spatialCoordinateDimensionExact :
      spatialCoordinateDimension ≡ Units.lengthDimension
    kinematicPressureDimensionExact :
      kinematicPressureDimension ≡ Units.speedSquaredDimension
    forcingDimensionExact :
      forcingDimension ≡ Units.accelerationDimension

    viscousTermDimensionLaw :
      Units._⊗ᴰ_
        Units.kinematicViscosityDimension
        Units.laplacianVelocityDimension
      ≡ Units.accelerationDimension

    advectiveTermDimensionLaw :
      Units._⊗ᴰ_
        Units.velocityDimension
        Units.velocityGradientDimension
      ≡ Units.accelerationDimension

open ReleasedNSDimensionAttachment public

canonicalReleasedNSDimensionAttachment :
  ReleasedNSDimensionAttachment
canonicalReleasedNSDimensionAttachment = record
  { viscosityDimension = Units.kinematicViscosityDimension
  ; velocityDimension = Units.velocityDimension
  ; timeDimension = Units.timeDimension
  ; spatialCoordinateDimension = Units.lengthDimension
  ; kinematicPressureDimension = Units.speedSquaredDimension
  ; forcingDimension = Units.accelerationDimension
  ; viscosityDimensionExact = refl
  ; velocityDimensionExact = refl
  ; timeDimensionExact = refl
  ; spatialCoordinateDimensionExact = refl
  ; kinematicPressureDimensionExact = refl
  ; forcingDimensionExact = refl
  ; viscousTermDimensionLaw = Units.viscousLaplacianIsAcceleration
  ; advectiveTermDimensionLaw = Units.advectionIsAcceleration
  }

------------------------------------------------------------------------
-- 4. Construction attachment surface for the native port.
--
-- These are exactly the objects that ActualCandidateConstruction/Assembly
-- produces.  Unlike an atlas row, this record is typed so later native modules
-- can populate the actual fields without changing the public interface.
------------------------------------------------------------------------

record NativeReleasedCandidateConstructionAttachment : Set₁ where
  field
    Index : Set
    CycleState : Set
    VelocityField : Set
    PressureField : Set

    selectedThreshold : Nat
    selectedThresholdMatchesSource : Set

    selectedCycle : Nat → CycleState
    selectedPotentialStages : Nat → VelocityField
    selectedDirectStages : Nat → VelocityField
    selectedPressureStages : Nat → PressureField

    selectedForcing : VelocityField

    selectedCycleLabelsPreserved : Set
    selectedCarrierPreserved : Set
    selectedRepresentationPreserved : Set
    selectedCoefficientBandsControlled : Set
    selectedResidualBandLaw : Set
    selectedBaseErrorPreserved : Set
    selectedAliasErrorSeparated : Set

    selectedPotentialSupport : Set
    selectedDirectSupport : Set
    selectedPressureSupport : Set

    selectedAwayExtensions : Set
    selectedCandidateProperties : Set
    selectedForceSmooth : Set
    selectedForceDerivativeDecay : Set
    selectedBoundaryJetsAttached : Set

open NativeReleasedCandidateConstructionAttachment public

------------------------------------------------------------------------
-- 5. Existing repository empirical screen attachment.
--
-- Source:
--   scripts/ns_phase_locked_packet_staged_screen.py
--
-- Values are encoded as exact decimal integer/scales where appropriate.
-- They are numerical screening parameters, NOT proof parameters of the released
-- construction.
------------------------------------------------------------------------

record DecimalScaledNat : Set where
  constructor decimal-scaled
  field
    significand : Nat
    decimalPlaces : Nat

open DecimalScaledNat public

experimentalGridN : Nat
experimentalGridN = 32

experimentalViscosity : DecimalScaledNat
experimentalViscosity = decimal-scaled 1 3

experimentalDt : DecimalScaledNat
experimentalDt = decimal-scaled 1 3

experimentalTargetShell : Nat
experimentalTargetShell = 2

experimentalCriticalMass : DecimalScaledNat
experimentalCriticalMass = decimal-scaled 1 0

experimentalQuarterWindowC : PositiveFraction
experimentalQuarterWindowC = positive-fraction 1 4

experimentalMovingPacketRadius : Nat
experimentalMovingPacketRadius = 1

experimentalPhaseSamples : Nat
experimentalPhaseSamples = 8

experimentalSeed : Nat
experimentalSeed = 20260716

record RoleAllocation : Set where
  constructor role-allocation
  field
    name : String
    target donor outlet feedback : Nat

open RoleAllocation public

-- Shares are stored in hundredths.
experimentalRoleAllocations : List RoleAllocation
experimentalRoleAllocations =
  role-allocation "balanced"          30 25 25 20
  ∷ role-allocation "donor-heavy"      25 40 15 20
  ∷ role-allocation "feedback-heavy"   25 20 15 40
  ∷ role-allocation "target-heavy"     50 20 15 15
  ∷ role-allocation "outlet-suppressed" 35 30 5 30
  ∷ role-allocation "outlet-enabled"   25 20 35 20
  ∷ []

record NSExperimentalValidationAttachment : Set where
  field
    gridN : Nat
    viscosity : DecimalScaledNat
    dt : DecimalScaledNat
    targetShell : Nat
    criticalMass : DecimalScaledNat
    quarterWindowC : PositiveFraction
    movingPacketRadius : Nat
    phaseSamples : Nat
    seed : Nat
    roleAllocations : List RoleAllocation

    candidateOnly : Bool
    empiricalNonPromoting : Bool
    theoremAuthority : Bool
    clayAuthority : Bool

    gridNExact : gridN ≡ experimentalGridN
    viscosityExact : viscosity ≡ experimentalViscosity
    dtExact : dt ≡ experimentalDt
    targetShellExact : targetShell ≡ experimentalTargetShell
    criticalMassExact : criticalMass ≡ experimentalCriticalMass
    quarterWindowExact : quarterWindowC ≡ experimentalQuarterWindowC
    movingPacketRadiusExact :
      movingPacketRadius ≡ experimentalMovingPacketRadius
    phaseSamplesExact : phaseSamples ≡ experimentalPhaseSamples
    seedExact : seed ≡ experimentalSeed
    roleAllocationsExact : roleAllocations ≡ experimentalRoleAllocations

    candidateOnlyIsTrue : candidateOnly ≡ true
    empiricalNonPromotingIsTrue : empiricalNonPromoting ≡ true
    theoremAuthorityIsFalse : theoremAuthority ≡ false
    clayAuthorityIsFalse : clayAuthority ≡ false

open NSExperimentalValidationAttachment public

canonicalNSExperimentalValidationAttachment :
  NSExperimentalValidationAttachment
canonicalNSExperimentalValidationAttachment = record
  { gridN = experimentalGridN
  ; viscosity = experimentalViscosity
  ; dt = experimentalDt
  ; targetShell = experimentalTargetShell
  ; criticalMass = experimentalCriticalMass
  ; quarterWindowC = experimentalQuarterWindowC
  ; movingPacketRadius = experimentalMovingPacketRadius
  ; phaseSamples = experimentalPhaseSamples
  ; seed = experimentalSeed
  ; roleAllocations = experimentalRoleAllocations
  ; candidateOnly = true
  ; empiricalNonPromoting = true
  ; theoremAuthority = false
  ; clayAuthority = false
  ; gridNExact = refl
  ; viscosityExact = refl
  ; dtExact = refl
  ; targetShellExact = refl
  ; criticalMassExact = refl
  ; quarterWindowExact = refl
  ; movingPacketRadiusExact = refl
  ; phaseSamplesExact = refl
  ; seedExact = refl
  ; roleAllocationsExact = refl
  ; candidateOnlyIsTrue = refl
  ; empiricalNonPromotingIsTrue = refl
  ; theoremAuthorityIsFalse = refl
  ; clayAuthorityIsFalse = refl
  }

------------------------------------------------------------------------
-- 6. Combined attachment: construction coordinates + SI dimensions +
--    empirical validation.  The actual theorem-bearing candidate body remains
--    a separate field so empirical data cannot accidentally inhabit it.
------------------------------------------------------------------------

record ReleasedCandidatePhysicalInputPackage : Set₁ where
  field
    constructionCoordinates : ReleasedSelectedConstructionCoordinates
    dimensions : ReleasedNSDimensionAttachment
    experimentalValidation : NSExperimentalValidationAttachment

    NativeConstruction : Set₁
    nativeConstruction : NativeConstruction

    nativeConstructionProducesReleasedAttachment :
      NativeConstruction → NativeReleasedCandidateConstructionAttachment

    empiricalValidationIsProof : Bool
    empiricalValidationIsProofIsFalse :
      empiricalValidationIsProof ≡ false

open ReleasedCandidatePhysicalInputPackage public

releasedCoordinatesPopulated : Bool
releasedCoordinatesPopulated = true

releasedSIDimensionsPopulated : Bool
releasedSIDimensionsPopulated = true

repositoryExperimentalValidationAttached : Bool
repositoryExperimentalValidationAttached = true

nativeActualCandidateConstructionPopulatedHere : Bool
nativeActualCandidateConstructionPopulatedHere = false

experimentalDataPromotedToProof : Bool
experimentalDataPromotedToProof = false

releasedCoordinatesPopulatedIsTrue :
  releasedCoordinatesPopulated ≡ true
releasedCoordinatesPopulatedIsTrue = refl

releasedSIDimensionsPopulatedIsTrue :
  releasedSIDimensionsPopulated ≡ true
releasedSIDimensionsPopulatedIsTrue = refl

repositoryExperimentalValidationAttachedIsTrue :
  repositoryExperimentalValidationAttached ≡ true
repositoryExperimentalValidationAttachedIsTrue = refl

nativeActualCandidateConstructionPopulatedHereIsFalse :
  nativeActualCandidateConstructionPopulatedHere ≡ false
nativeActualCandidateConstructionPopulatedHereIsFalse = refl

experimentalDataPromotedToProofIsFalse :
  experimentalDataPromotedToProof ≡ false
experimentalDataPromotedToProofIsFalse = refl
