module DASHI.Physics.Closure.YMNSAtomAsymmetryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- YM/NS atom asymmetry receipt.
--
-- This is programme bookkeeping, not a proof of the Yang-Mills Clay
-- problem, not a proof of the Navier-Stokes Clay problem, and not a
-- promotion of either terminal claim.
--
-- The asymmetry recorded here is deliberately local to the atom surface:
-- Navier-Stokes atoms must carry phase, spin/helicity, and a nonlocal
-- pressure channel for Gate 3.  A Yang-Mills atom surface is simpler in this
-- local atom sense because gauge phase is quotient/gauge-invariant and the
-- constraint analogue is Gauss law, not an NS pressure elliptic solve stored
-- as atom pressure.

data AtomAsymmetryStatus : Set where
  ymNsLocalAtomAsymmetryRecorded :
    AtomAsymmetryStatus

data NSAtomGate3Requirement : Set where
  nsAtomPhaseRequired :
    NSAtomGate3Requirement

  nsAtomSpinHelicityRequired :
    NSAtomGate3Requirement

  nsAtomNonlocalPressureRequired :
    NSAtomGate3Requirement

canonicalNSAtomGate3Requirements :
  List NSAtomGate3Requirement
canonicalNSAtomGate3Requirements =
  nsAtomPhaseRequired
  ∷ nsAtomSpinHelicityRequired
  ∷ nsAtomNonlocalPressureRequired
  ∷ []

data YMAtomLocalSurface : Set where
  ymGaugePhaseQuotientInvariant :
    YMAtomLocalSurface

  ymGaussLawIsConstraintAnalogue :
    YMAtomLocalSurface

  ymNoAtomPressureEllipticSolveStored :
    YMAtomLocalSurface

canonicalYMAtomLocalSurface :
  List YMAtomLocalSurface
canonicalYMAtomLocalSurface =
  ymGaugePhaseQuotientInvariant
  ∷ ymGaussLawIsConstraintAnalogue
  ∷ ymNoAtomPressureEllipticSolveStored
  ∷ []

data AtomAsymmetryNonClaim : Set where
  noYangMillsClayProof :
    AtomAsymmetryNonClaim

  noNavierStokesClayProof :
    AtomAsymmetryNonClaim

  noGate3ClosureProof :
    AtomAsymmetryNonClaim

  noPressureRegularityProof :
    AtomAsymmetryNonClaim

  noMassGapProof :
    AtomAsymmetryNonClaim

  noClayPromotion :
    AtomAsymmetryNonClaim

canonicalAtomAsymmetryNonClaims :
  List AtomAsymmetryNonClaim
canonicalAtomAsymmetryNonClaims =
  noYangMillsClayProof
  ∷ noNavierStokesClayProof
  ∷ noGate3ClosureProof
  ∷ noPressureRegularityProof
  ∷ noMassGapProof
  ∷ noClayPromotion
  ∷ []

data AtomAsymmetryPromotion : Set where

atomAsymmetryPromotionImpossibleHere :
  AtomAsymmetryPromotion →
  ⊥
atomAsymmetryPromotionImpossibleHere ()

nsGate3RequirementStatement : String
nsGate3RequirementStatement =
  "NS atoms require phase plus spin/helicity plus nonlocal pressure for Gate 3."

ymLocalAtomSurfaceStatement : String
ymLocalAtomSurfaceStatement =
  "YM atom surface is simpler locally: gauge phase is quotient/gauge-invariant and Gauss law is the constraint analogue."

pressureAsymmetryStatement : String
pressureAsymmetryStatement =
  "The YM local atom record does not store an NS-style pressure elliptic solve as atom pressure."

programmeBookkeepingStatement : String
programmeBookkeepingStatement =
  "This receipt is programme bookkeeping only and proves no Yang-Mills or Navier-Stokes Clay claim."

record YMNSAtomAsymmetryReceipt : Setω where
  field
    status :
      AtomAsymmetryStatus

    statusIsCanonical :
      status ≡ ymNsLocalAtomAsymmetryRecorded

    nsRequirements :
      List NSAtomGate3Requirement

    nsRequirementsAreCanonical :
      nsRequirements ≡ canonicalNSAtomGate3Requirements

    nsRequiresPhase :
      Bool

    nsRequiresPhaseIsTrue :
      nsRequiresPhase ≡ true

    nsRequiresSpinHelicity :
      Bool

    nsRequiresSpinHelicityIsTrue :
      nsRequiresSpinHelicity ≡ true

    nsRequiresNonlocalPressure :
      Bool

    nsRequiresNonlocalPressureIsTrue :
      nsRequiresNonlocalPressure ≡ true

    nsGate3Requirement :
      String

    nsGate3RequirementIsCanonical :
      nsGate3Requirement ≡ nsGate3RequirementStatement

    ymLocalSurface :
      List YMAtomLocalSurface

    ymLocalSurfaceIsCanonical :
      ymLocalSurface ≡ canonicalYMAtomLocalSurface

    ymGaugePhaseQuotientInvariantRecorded :
      Bool

    ymGaugePhaseQuotientInvariantRecordedIsTrue :
      ymGaugePhaseQuotientInvariantRecorded ≡ true

    ymGaussLawConstraintAnalogueRecorded :
      Bool

    ymGaussLawConstraintAnalogueRecordedIsTrue :
      ymGaussLawConstraintAnalogueRecorded ≡ true

    ymStoresNSPressureEllipticSolveAsAtomPressure :
      Bool

    ymStoresNSPressureEllipticSolveAsAtomPressureIsFalse :
      ymStoresNSPressureEllipticSolveAsAtomPressure ≡ false

    ymLocalAtomSurface :
      String

    ymLocalAtomSurfaceIsCanonical :
      ymLocalAtomSurface ≡ ymLocalAtomSurfaceStatement

    pressureAsymmetry :
      String

    pressureAsymmetryIsCanonical :
      pressureAsymmetry ≡ pressureAsymmetryStatement

    programmeBookkeeping :
      String

    programmeBookkeepingIsCanonical :
      programmeBookkeeping ≡ programmeBookkeepingStatement

    nonClaims :
      List AtomAsymmetryNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalAtomAsymmetryNonClaims

    ymClayMassGapPromoted :
      Bool

    ymClayMassGapPromotedIsFalse :
      ymClayMassGapPromoted ≡ false

    nsClayRegularityPromoted :
      Bool

    nsClayRegularityPromotedIsFalse :
      nsClayRegularityPromoted ≡ false

    gate3ClosurePromoted :
      Bool

    gate3ClosurePromotedIsFalse :
      gate3ClosurePromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List AtomAsymmetryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMNSAtomAsymmetryReceipt public

canonicalYMNSAtomAsymmetryReceipt :
  YMNSAtomAsymmetryReceipt
canonicalYMNSAtomAsymmetryReceipt =
  record
    { status =
        ymNsLocalAtomAsymmetryRecorded
    ; statusIsCanonical =
        refl
    ; nsRequirements =
        canonicalNSAtomGate3Requirements
    ; nsRequirementsAreCanonical =
        refl
    ; nsRequiresPhase =
        true
    ; nsRequiresPhaseIsTrue =
        refl
    ; nsRequiresSpinHelicity =
        true
    ; nsRequiresSpinHelicityIsTrue =
        refl
    ; nsRequiresNonlocalPressure =
        true
    ; nsRequiresNonlocalPressureIsTrue =
        refl
    ; nsGate3Requirement =
        nsGate3RequirementStatement
    ; nsGate3RequirementIsCanonical =
        refl
    ; ymLocalSurface =
        canonicalYMAtomLocalSurface
    ; ymLocalSurfaceIsCanonical =
        refl
    ; ymGaugePhaseQuotientInvariantRecorded =
        true
    ; ymGaugePhaseQuotientInvariantRecordedIsTrue =
        refl
    ; ymGaussLawConstraintAnalogueRecorded =
        true
    ; ymGaussLawConstraintAnalogueRecordedIsTrue =
        refl
    ; ymStoresNSPressureEllipticSolveAsAtomPressure =
        false
    ; ymStoresNSPressureEllipticSolveAsAtomPressureIsFalse =
        refl
    ; ymLocalAtomSurface =
        ymLocalAtomSurfaceStatement
    ; ymLocalAtomSurfaceIsCanonical =
        refl
    ; pressureAsymmetry =
        pressureAsymmetryStatement
    ; pressureAsymmetryIsCanonical =
        refl
    ; programmeBookkeeping =
        programmeBookkeepingStatement
    ; programmeBookkeepingIsCanonical =
        refl
    ; nonClaims =
        canonicalAtomAsymmetryNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; ymClayMassGapPromoted =
        false
    ; ymClayMassGapPromotedIsFalse =
        refl
    ; nsClayRegularityPromoted =
        false
    ; nsClayRegularityPromotedIsFalse =
        refl
    ; gate3ClosurePromoted =
        false
    ; gate3ClosurePromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "NS atom Gate 3 bookkeeping keeps phase, spin/helicity, and nonlocal pressure"
        ∷ "YM local atom bookkeeping treats gauge phase as quotient/gauge-invariant"
        ∷ "YM uses Gauss law as the constraint analogue, not an NS atom-pressure elliptic solve"
        ∷ "This is programme bookkeeping only; all Clay promotions remain false"
        ∷ []
    }

canonicalYMNSAtomAsymmetryKeepsYMClayFalse :
  ymClayMassGapPromoted canonicalYMNSAtomAsymmetryReceipt ≡ false
canonicalYMNSAtomAsymmetryKeepsYMClayFalse =
  refl

canonicalYMNSAtomAsymmetryKeepsNSClayFalse :
  nsClayRegularityPromoted canonicalYMNSAtomAsymmetryReceipt ≡ false
canonicalYMNSAtomAsymmetryKeepsNSClayFalse =
  refl

canonicalYMNSAtomAsymmetryKeepsTerminalClayFalse :
  terminalClayClaimPromoted canonicalYMNSAtomAsymmetryReceipt ≡ false
canonicalYMNSAtomAsymmetryKeepsTerminalClayFalse =
  refl

canonicalYMNSAtomAsymmetryNoPromotion :
  AtomAsymmetryPromotion →
  ⊥
canonicalYMNSAtomAsymmetryNoPromotion =
  atomAsymmetryPromotionImpossibleHere
