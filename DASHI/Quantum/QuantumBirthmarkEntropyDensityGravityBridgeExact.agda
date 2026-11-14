{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkEntropyDensityGravityBridgeExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.EntropyDensityExact as Density
import DASHI.Physics.Foundations.EntropicGravitySourceBoundaryExact as Gravity
import DASHI.Quantum.QuantumBirthmarkErgodicityExact as Birthmark
import DASHI.Quantum.QuantumBirthmarkSymmetrySectorExact as Sector
import DASHI.Quantum.TSVF as TSVF

------------------------------------------------------------------------
-- CROSS-LANE BRIDGE
--
-- Quantum birthmarks provide a concrete physical example in which an
-- ergodic-looking / highly mixed coarse description need not erase a
-- history-sensitive fine-state statistic.  The generic entropy-density owner
-- keeps that statement distinct from thermodynamic entropy production and
-- from residual information density.
--
-- The gravity side is deliberately conditional.  Jacobson and Verlinde have
-- different source assumptions and authority.  Nothing here promotes a
-- birthmark, an entropy density, or a residual-information density directly
-- into curvature or stress-energy.
------------------------------------------------------------------------

record BirthmarkEntropyDensityBridge : Set where
  constructor birthmarkEntropyDensityBridge
  field
    highCoarseEntropyDoesNotImplyResidualErasure : Bool
    quantumBirthmarkSuppliesHistorySensitiveResidualExample : Bool
    timeReversalClassChangesUniversalBirthmarkFactor : Bool
    additionalSymmetryNeedsSectorAccounting : Bool
    residualInformationNeedNotBeThermodynamicEntropy : Bool
    entropyProductionNeedNotBeBirthmarkStrength : Bool

canonicalBirthmarkEntropyDensityBridge : BirthmarkEntropyDensityBridge
canonicalBirthmarkEntropyDensityBridge =
  birthmarkEntropyDensityBridge true true true true true true

record BirthmarkGravityPromotionBoundary : Set where
  constructor birthmarkGravityPromotionBoundary
  field
    birthmarkMemoryDoesNotByItselfSourceCurvature : Bool
    entropyDensityDoesNotByItselfSourceCurvature : Bool
    residualInformationDensityDoesNotByItselfSourceCurvature : Bool

    jacobsonBridgeRequiresHorizonHeatTemperatureEntropyAssumptions : Bool
    jacobsonBridgeRequiresLocalCausalHorizonGeometry : Bool
    jacobsonBridgeIsNotGenericBirthmarkToEinsteinMap : Bool

    verlindeBridgeRequiresHolographicScreenAssumptions : Bool
    verlindeBridgeRequiresEntropicForceIdentification : Bool
    verlindeBridgeIsNotGenericEntropyDensityToGravityTheorem : Bool

    tsvfIsOptionalInterpretiveExtensionNotBirthmarkCause : Bool
    selectedLorentzianSpacetimeStillNeedsIndependentPhysicalBridge : Bool

    entropyDensityResidualInformationAndEntropyProductionRemainDistinct : Bool
    interpretation : String

canonicalBirthmarkGravityPromotionBoundary : BirthmarkGravityPromotionBoundary
canonicalBirthmarkGravityPromotionBoundary =
  birthmarkGravityPromotionBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    "The common theorem-shape is persistence of fine history under a coarse observer. Jacobson supplies a conditional horizon-thermodynamic route to Einstein dynamics; Verlinde supplies a distinct holographic entropic-force proposal. Neither is obtained merely by naming birthmark memory or entropy density."

------------------------------------------------------------------------
-- Four-way semantic cut used by future physical adapters.
------------------------------------------------------------------------

data InformationThermodynamicRole : Set where
  coarseEntropyDensity
  residualInformationDensity
  entropyProductionDensity
  birthmarkMemoryObservable
    : InformationThermodynamicRole

rolesRemainDistinctWithoutBridge : Bool
rolesRemainDistinctWithoutBridge = true

------------------------------------------------------------------------
-- Source attribution receipts are imported, rather than duplicated.
------------------------------------------------------------------------

bekensteinSourceReused : Gravity.SourceReceipt
bekensteinSourceReused = Gravity.bekenstein1973

jacobsonSourceReused : Gravity.SourceReceipt
jacobsonSourceReused = Gravity.jacobson1995

verlindeSourceReused : Gravity.SourceReceipt
verlindeSourceReused = Gravity.verlinde2011

entropyDensityAuthorityReused : Density.EntropyDensityAuthorityBoundary
entropyDensityAuthorityReused = Density.canonicalEntropyDensityAuthorityBoundary
