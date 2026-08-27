module DASHI.Biology.NeurodivergentHoldingTensionBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RelationalTensionCompressionExact as Tension
import DASHI.Biology.NeurodivergentHoldingTensionSourceBoundaryExact as Sources

------------------------------------------------------------------------
-- THIN CROSS-BRANCH BRIDGE
--
-- The core owner supplies only a structural retained-coordinate burden proxy.
-- The biology evidence ledger supplies peer-reviewed motivation/correctives.
-- This file deliberately leaves the empirical map from representational burden
-- to physiological/metabolic cost uninhabited until direct evidence is added.
------------------------------------------------------------------------

structuralBurden : Tension.RepresentationMode → Nat
structuralBurden = Tension.retainedCoordinates

data PhysiologicalCostCode : Set where
  lowMeasuredCost highMeasuredCost : PhysiologicalCostCode

record EmpiricalBurdenCostBridge : Set₁ where
  field
    physiologicalCost : Tension.RepresentationMode → PhysiologicalCostCode
    bridgeEvidence : Set
    bridgeReceipt : bridgeEvidence
    bridgeReading : String

------------------------------------------------------------------------
-- No canonical empirical inhabitant is installed.  The absence is explicit,
-- rather than simulated by a guessed energy table.
------------------------------------------------------------------------

data InstalledAutismMetabolicBridge : Set where

noInstalledAutismMetabolicBridge : InstalledAutismMetabolicBridge → ⊥
noInstalledAutismMetabolicBridge ()

------------------------------------------------------------------------
-- Evidence-role map: source roles can motivate candidate coordinates without
-- becoming a deterministic individual-level or energy law.
------------------------------------------------------------------------

data CandidateCoordinate : Set where
  multiscaleDynamics
  precisionAndUpdating
  attentionalPersistence
  crossNeurotypeTransfer
  measurementHeterogeneity
  : CandidateCoordinate

coordinateForRole : Sources.EvidenceRole → CandidateCoordinate
coordinateForRole Sources.dynamicMultiscaleMathematicalFramework = multiscaleDynamics
coordinateForRole Sources.activeInferencePrecisionUpdating = precisionAndUpdating
coordinateForRole Sources.precisionWeightingNullCorrective = measurementHeterogeneity
coordinateForRole Sources.transdiagnosticHyperfocusContextualEffects = attentionalPersistence
coordinateForRole Sources.hyperfocusMeasurementNonConvergence = measurementHeterogeneity
coordinateForRole Sources.stickySpringyAttentionOperationalisation = attentionalPersistence
coordinateForRole Sources.crossNeurotypeInformationTransfer = crossNeurotypeTransfer
coordinateForRole Sources.precisionReviewContext = precisionAndUpdating

adamouMotivatesMultiscaleCoordinate :
  coordinateForRole (Sources.role Sources.adamouEtAl2026) ≡ multiscaleDynamics
adamouMotivatesMultiscaleCoordinate = refl

wardNullConstrainsPrecisionPromotion :
  coordinateForRole (Sources.role Sources.wardBuitelaarHunnius2024)
  ≡ measurementHeterogeneity
wardNullConstrainsPrecisionPromotion = refl

cromptonMotivatesTransferCoordinate :
  coordinateForRole (Sources.role Sources.cromptonEtAl2025)
  ≡ crossNeurotypeTransfer
cromptonMotivatesTransferCoordinate = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record NeurodivergentHoldingTensionBridgeBoundary : Set where
  constructor neurodivergentHoldingTensionBridgeBoundary
  field
    coreStructuralBurdenAvailable : Bool
    coreStructuralBurdenAvailableIsTrue :
      coreStructuralBurdenAvailable ≡ true

    empiricalMetabolicBridgeInstalled : Bool
    empiricalMetabolicBridgeInstalledIsFalse :
      empiricalMetabolicBridgeInstalled ≡ false

    sourceRolesCanMotivateSeparateCoordinates : Bool
    sourceRolesCanMotivateSeparateCoordinatesIsTrue :
      sourceRolesCanMotivateSeparateCoordinates ≡ true

    sourceRolesProveUniversalAutisticMechanism : Bool
    sourceRolesProveUniversalAutisticMechanismIsFalse :
      sourceRolesProveUniversalAutisticMechanism ≡ false

    bridgeReading : String

canonicalNeurodivergentHoldingTensionBridgeBoundary :
  NeurodivergentHoldingTensionBridgeBoundary
canonicalNeurodivergentHoldingTensionBridgeBoundary =
  neurodivergentHoldingTensionBridgeBoundary
    true refl
    false refl
    true refl
    false refl
    "The repo can represent greater retained relational state as a structural burden and can map peer-reviewed findings to candidate explanatory coordinates, but it does not yet equate that burden with measured neural metabolic energy or a universal autistic mechanism."
