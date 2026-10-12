{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonLocalHorizonMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.EntropyDensityExact as Density
import DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact as Focusing
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular
import DASHI.Physics.GR.EinsteinTensor as Einstein
import DASHI.Physics.GR.StressEnergyCompatibility as Stress
import DASHI.Quantum.QuantumBirthmarkHolographicLorentz31JacobsonBridgeExact as Prior

------------------------------------------------------------------------
-- JACOBSON LOCAL-HORIZON TERMINAL MAX-CUT
--
-- This module does not claim a new derivation of the Einstein equation.
-- It recuts the older broad `einsteinEquationNotDerivedByThisAdapter` leaf
-- against the strongest already-owned QFT/GR theorem surfaces.
--
-- The important normalization correction is that Jacobson's entropy input is
-- an entropy/AREA variation on a local causal horizon, not a generic volume
-- entropy density.  `EntropyDensityExact` now exposes that distinction.
------------------------------------------------------------------------

record JacobsonLocalHorizonPaymentSurface : Set₁ where
  field
    Horizon : Set
    SurfaceEntropyDensity : Set
    Temperature : Set
    HeatFlux : Set
    StressEnergyFlux : Set
    AreaVariation : Set
    NullExpansion : Set
    RicciNullContraction : Set
    EinsteinEquationTarget : Set

    surfaceEntropyDensity : Horizon → SurfaceEntropyDensity
    localRindlerHorizon : Horizon → Set
    unruhTemperatureNormalization : Horizon → Temperature → Set
    clausiusRelation : Horizon → HeatFlux → Temperature → Set
    raychaudhuriAreaVariation : Horizon → AreaVariation → NullExpansion → RicciNullContraction → Set
    heatFluxStressEnergy : Horizon → HeatFlux → StressEnergyFlux → Set
    allNullDirections : Horizon → Set
    einsteinEquationOfStateTarget : Horizon → EinsteinEquationTarget → Set

------------------------------------------------------------------------
-- What the current repository actually owns.
------------------------------------------------------------------------

record ExistingJacobsonOwnerReuse : Set where
  constructor existingJacobsonOwnerReuse
  field
    surfaceEntropyNormalisationOwned : Bool
    nullRaychaudhuriSourceBoundaryOwned : Bool
    modularKMSRindlerTargetSurfaceOwned : Bool
    localVacuumEinsteinTensorSurfaceOwned : Bool
    stressEnergyCompatibilityFirewallOwned : Bool
    priorLorentz31HorizonAdapterOwned : Bool

canonicalExistingJacobsonOwnerReuse : ExistingJacobsonOwnerReuse
canonicalExistingJacobsonOwnerReuse =
  existingJacobsonOwnerReuse true true true true true true

------------------------------------------------------------------------
-- Irreducible live theorem leaves after owner reuse.
------------------------------------------------------------------------

record JacobsonResidualCutset : Set where
  constructor jacobsonResidualCutset
  field
    unruhRindlerKernelTheorem : Bool
    clausiusEntropyAreaSameObjectReceipt : Bool
    nullRaychaudhuriContinuumKernelTheorem : Bool
    sameObjectMatterStressEnergyReceipt : Bool
    allNullDirectionsTensorRecovery : Bool
    einsteinEquationOfStateKernelDerivation : Bool
    physicalCalibration : Bool

canonicalJacobsonResidualCutset : JacobsonResidualCutset
canonicalJacobsonResidualCutset =
  jacobsonResidualCutset true true true true true true true

------------------------------------------------------------------------
-- Authority boundary.
--
-- Existing files are deliberately mixed-strength:
-- * ModularTheoryReceiptSurface names Rindler/KMS/Unruh targets and missing
--   normalization/analytic-strip payments; it is not a local Unruh theorem.
-- * NullRaychaudhuriSachsFocusingExact carries primary-source equation targets
--   and exact qualitative implications, but explicitly does not internally
--   derive the continuum optical equation.
-- * EinsteinTensor has a concrete local-vacuum surface; that does not pay the
--   sourced matter equation used in the Jacobson route.
-- * StressEnergyCompatibility is explicitly fail-closed at its matter-source
--   receipt interface.
------------------------------------------------------------------------

record JacobsonPromotionFirewall : Set where
  constructor jacobsonPromotionFirewall
  field
    unruhStillTargetNotLocalTheorem : Bool
    raychaudhuriStillAuthorityTarget : Bool
    sourcedStressEnergyStillBlocked : Bool
    localVacuumEinsteinSurfaceDoesNotPaySourcedJacobson : Bool
    entropyPerAreaIsNotEntropyPerVolume : Bool
    birthmarkResidualIsNotHorizonEntropy : Bool
    ryuTakayanagiEntropyIsNotJacobsonHorizonEntropyByDefinition : Bool
    pAdicBoundaryIsNotLocalRindlerHorizon : Bool

canonicalJacobsonPromotionFirewall : JacobsonPromotionFirewall
canonicalJacobsonPromotionFirewall =
  jacobsonPromotionFirewall true true true true true true true true

surfaceEntropyDensity : Bool
surfaceEntropyDensity = true

localRindlerHorizon : Bool
localRindlerHorizon = true

unruhTemperatureNormalization : Bool
unruhTemperatureNormalization = true

clausiusRelation : Bool
clausiusRelation = true

raychaudhuriAreaVariation : Bool
raychaudhuriAreaVariation = true

heatFluxStressEnergy : Bool
heatFluxStressEnergy = true

allNullDirections : Bool
allNullDirections = true

einsteinEquationOfStateTarget : Bool
einsteinEquationOfStateTarget = true

unruhStillTargetNotLocalTheorem : Bool
unruhStillTargetNotLocalTheorem = true

raychaudhuriStillAuthorityTarget : Bool
raychaudhuriStillAuthorityTarget = true

sourcedStressEnergyStillBlocked : Bool
sourcedStressEnergyStillBlocked = true

localVacuumEinsteinSurfaceDoesNotPaySourcedJacobson : Bool
localVacuumEinsteinSurfaceDoesNotPaySourcedJacobson = true

entropyPerAreaIsNotEntropyPerVolume : Bool
entropyPerAreaIsNotEntropyPerVolume = Density.entropyPerAreaIsNotEntropyPerVolume

birthmarkResidualIsNotHorizonEntropy : Bool
birthmarkResidualIsNotHorizonEntropy = true

------------------------------------------------------------------------
-- Status: the *architecture* of the local-horizon payment is now exact, but
-- the continuum/QFT/matter theorems above remain live.  No Boolean is used as
-- a substitute for those proofs.
------------------------------------------------------------------------

jacobsonFrameworkAmbiguityClosed : Bool
jacobsonFrameworkAmbiguityClosed = true

jacobsonPhysicalKernelDerivationStillRequired : Bool
jacobsonPhysicalKernelDerivationStillRequired = true

status : String
status = "JACOBSON-PAYMENT-SURFACE-RECUT / QFT-RAYCHAUDHURI-STRESS-KERNELS-PENDING"
