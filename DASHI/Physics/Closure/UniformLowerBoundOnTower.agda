module DASHI.Physics.Closure.UniformLowerBoundOnTower where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.LCP.InductiveLimit using (NatColimitWitness)
import DASHI.Geometry.LCP.FiniteSpectralGap as FSG
import DASHI.Physics.Closure.FiniteCoercivityOnSelectedCarrier as SelectedCarrier
import DASHI.Physics.Closure.Gate2SpectralGapMath as Gate2
import DASHI.Physics.Closure.PressureBelow15SpectralNatWitnessSlice as NatSlice
import DASHI.Physics.Closure.SpectralGapRefinementStability as Spectral

------------------------------------------------------------------------
-- Gate 2 uniform lower-bound wrapper on the actual Nat tower.
--
-- This module is deliberately conservative: it records the canonical lower
-- bound unit 1, the upstream Gate 2 canonical gap, the existing tower-wide
-- uniform lower-bound receipt, and the selected-carrier nat-slice transition
-- receipt.  It does not claim the real-carrier analytic theorem.

record UniformLowerBoundOnTowerReceipt : Setω where
  field
    lowerBoundUnit :
      Nat

    lowerBoundUnitIsCanonical :
      lowerBoundUnit ≡ suc zero

    gate2CanonicalGapValue :
      Nat

    gate2CanonicalGapValueIsCanonical :
      gate2CanonicalGapValue ≡ Gate2.gate2CanonicalGap

    selectedCarrierNatSliceTransitionReceipt :
      NatSlice.S8NatToRealPhysicalCarrierTransitionReceipt

    selectedCarrierFiniteCoercivityReceipt :
      SelectedCarrier.FiniteCoercivityOnSelectedCarrierReceipt

    towerRefinementReceipt :
      Spectral.SpectralGapRefinementStabilityReceipt

    towerFiniteSpectralGapToolkit :
      FSG.FiniteSpectralGapToolkit

    towerFiniteSpectralGapToolkitLabel :
      String

    towerWideUniformLowerBoundReceipt :
      Gate2.UniformLowerBound Gate2.gate2CanonicalGap

    towerWideUniformLowerBoundReceiptLabel :
      String

    natColimitWitness :
      NatColimitWitness
        (FSG.diagram towerFiniteSpectralGapToolkit)

    natColimitWitnessLabel :
      String

    receiptBoundary :
      List String

open UniformLowerBoundOnTowerReceipt public

canonicalUniformLowerBoundOnTowerReceipt :
  UniformLowerBoundOnTowerReceipt
canonicalUniformLowerBoundOnTowerReceipt =
  record
    { lowerBoundUnit =
        suc zero
    ; lowerBoundUnitIsCanonical =
        refl
    ; gate2CanonicalGapValue =
        Gate2.gate2CanonicalGap
    ; gate2CanonicalGapValueIsCanonical =
        refl
    ; selectedCarrierNatSliceTransitionReceipt =
        NatSlice.canonicalS8NatToRealPhysicalCarrierTransitionReceipt
    ; selectedCarrierFiniteCoercivityReceipt =
        SelectedCarrier.canonicalFiniteCoercivityOnSelectedCarrierReceipt
    ; towerRefinementReceipt =
        Spectral.canonicalSpectralGapRefinementStabilityReceipt
    ; towerFiniteSpectralGapToolkit =
        Spectral.canonicalSpectralGapFiniteToolkit
    ; towerFiniteSpectralGapToolkitLabel =
        "canonical-spectral-gap-finite-toolkit"
    ; towerWideUniformLowerBoundReceipt =
        Gate2.canonicalUniformLowerBound
    ; towerWideUniformLowerBoundReceiptLabel =
        "canonical-uniform-lower-bound-receipt"
    ; natColimitWitness =
        FSG.limitWitness Spectral.canonicalSpectralGapFiniteToolkit
    ; natColimitWitnessLabel =
        "canonical-Nat-colimit-witness"
    ; receiptBoundary =
        "The lower bound unit is the canonical Nat unit 1"
        ∷ "Gate2.gate2CanonicalGap is recorded directly as the uniform gap value"
        ∷ "Gate2.canonicalUniformLowerBound is reused as the tower-wide witness"
        ∷ "The selected-carrier nat-slice transition receipt is threaded explicitly"
        ∷ "The Nat colimit witness is reused from the canonical spectral-gap refinement receipt"
        ∷ "No real-carrier analytic theorem is claimed here"
        ∷ []
    }
