module DASHI.Physics.Closure.CrossGateHamiltonianCompatibilityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Quantum.SelfAdjointGenerator as SelfAdjoint
import DASHI.Quantum.Stone_Gates as StoneGates
import DASHI.Physics.Closure.Gate2SpectralGapMath as Gate2
import DASHI.Physics.Closure.SelfAdjointYangMillsHamiltonianOnCarrierQuotient as YMH
import DASHI.Physics.Closure.YangMillsGate3DiscreteGeometryReceipt as Gate3
import DASHI.Physics.QFT.DHRSectorDecomposition as DHR

------------------------------------------------------------------------
-- Cross-gate Hamiltonian compatibility receipt.
--
-- This module records the current compatibility frontier among:
--   * Gate 5: the Stone/GNS self-adjoint colimit generator surface,
--   * Gate 2/3: the finite Yang-Mills Hamiltonian/spectral-gap and discrete
--     geometry surfaces,
--   * Gate 6: DHR sector decomposition / representation-frontier data.
--
-- It is intentionally fail-closed.  The repo has finite and carrier-side
-- witnesses, but it does not yet identify one physical Hamiltonian across
-- Stone, Yang-Mills, and DHR sector representations.

data CrossGateHamiltonianCompatibilityBlocker : Set where
  missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification :
    CrossGateHamiltonianCompatibilityBlocker

  missingGate23YMHamiltonianActionOnGate6DHRSectorRepresentations :
    CrossGateHamiltonianCompatibilityBlocker

  missingCommonHamiltonianDomainAcrossStoneYMDHR :
    CrossGateHamiltonianCompatibilityBlocker

  missingDHRRepresentationPreservesYMHamiltonianSpectrum :
    CrossGateHamiltonianCompatibilityBlocker

  missingCrossGateHamiltonianNaturalityLaw :
    CrossGateHamiltonianCompatibilityBlocker

canonicalCrossGateHamiltonianCompatibilityBlockers :
  List CrossGateHamiltonianCompatibilityBlocker
canonicalCrossGateHamiltonianCompatibilityBlockers =
  missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification
  ∷ missingGate23YMHamiltonianActionOnGate6DHRSectorRepresentations
  ∷ missingCommonHamiltonianDomainAcrossStoneYMDHR
  ∷ missingDHRRepresentationPreservesYMHamiltonianSpectrum
  ∷ missingCrossGateHamiltonianNaturalityLaw
  ∷ []

canonicalCrossGateHamiltonianCompatibilityBlockerStrings :
  List String
canonicalCrossGateHamiltonianCompatibilityBlockerStrings =
  "missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification"
  ∷ "missingGate23YMHamiltonianActionOnGate6DHRSectorRepresentations"
  ∷ "missingCommonHamiltonianDomainAcrossStoneYMDHR"
  ∷ "missingDHRRepresentationPreservesYMHamiltonianSpectrum"
  ∷ "missingCrossGateHamiltonianNaturalityLaw"
  ∷ []

record CrossGateHamiltonianCompatibilityReceipt : Setω where
  field
    gate5StoneGatesWitnessBundle :
      StoneGates.StoneGatesWitnessBundle

    gate5SelfAdjointGeneratorWitness :
      SelfAdjoint.SelfAdjointColimitGeneratorWitness

    gate23YMHamiltonianBridgeReceipt :
      YMH.Gate8Term4StoneYMHamiltonianGapBridgeReceipt

    gate2SpectralGapMathReceipt :
      Gate2.Gate2SpectralGapMathReceipt

    gate3DiscreteGeometryReceipt :
      Gate3.Gate3DiscreteGeometryReceipt

    gate6DHRSectorDecomposition :
      DHR.DHRSectorDecomposition

    gate5SelfAdjointGeneratorRecorded :
      Bool

    gate5SelfAdjointGeneratorRecordedIsTrue :
      gate5SelfAdjointGeneratorRecorded ≡ true

    gate23YMHamiltonianCarrierRecorded :
      Bool

    gate23YMHamiltonianCarrierRecordedIsTrue :
      gate23YMHamiltonianCarrierRecorded ≡ true

    gate6DHRSectorRepresentationFrontierRecorded :
      Bool

    gate6DHRSectorRepresentationFrontierRecordedIsTrue :
      gate6DHRSectorRepresentationFrontierRecorded ≡ true

    gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromoted :
      Bool

    gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromotedIsFalse :
      gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromoted
      ≡
      false

    gate23YMHamiltonianGate6DHRSectorRepresentationCompatibilityPromoted :
      Bool

    gate23YMHamiltonianGate6DHRSectorRepresentationCompatibilityPromotedIsFalse :
      gate23YMHamiltonianGate6DHRSectorRepresentationCompatibilityPromoted
      ≡
      false

    gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromoted :
      Bool

    gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromotedIsFalse :
      gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromoted
      ≡
      false

    inheritedStoneGeneratorIsNotPhysicalYMHamiltonian :
      YMH.stoneGeneratorIsPhysicalYMHamiltonian
        gate23YMHamiltonianBridgeReceipt
      ≡
      false

    inheritedGate3StrictPromotionIsFalse :
      Gate3.gate3Promoted gate3DiscreteGeometryReceipt
      ≡
      false

    inheritedDHRSectorDecompositionPromotionIsFalse :
      DHR.sectorDecompositionPromoted gate6DHRSectorDecomposition
      ≡
      false

    blockers :
      List CrossGateHamiltonianCompatibilityBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCrossGateHamiltonianCompatibilityBlockers

    blockerStrings :
      List String

    blockerStringsAreCanonical :
      blockerStrings
      ≡
      canonicalCrossGateHamiltonianCompatibilityBlockerStrings

    firstBlocker :
      CrossGateHamiltonianCompatibilityBlocker

    firstBlockerIsGate5ToGate23Identification :
      firstBlocker
      ≡
      missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification

    compatibilityBoundary :
      List String

open CrossGateHamiltonianCompatibilityReceipt public

canonicalCrossGateHamiltonianCompatibilityReceipt :
  CrossGateHamiltonianCompatibilityReceipt
canonicalCrossGateHamiltonianCompatibilityReceipt =
  record
    { gate5StoneGatesWitnessBundle =
        StoneGates.canonicalStoneGatesWitnessBundle
    ; gate5SelfAdjointGeneratorWitness =
        SelfAdjoint.canonicalSelfAdjointColimitGeneratorWitness
    ; gate23YMHamiltonianBridgeReceipt =
        YMH.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; gate2SpectralGapMathReceipt =
        Gate2.canonicalGate2SpectralGapMathReceipt
    ; gate3DiscreteGeometryReceipt =
        Gate3.canonicalGate3DiscreteGeometryReceipt
    ; gate6DHRSectorDecomposition =
        DHR.canonicalDHRSectorDecomposition
    ; gate5SelfAdjointGeneratorRecorded =
        true
    ; gate5SelfAdjointGeneratorRecordedIsTrue =
        refl
    ; gate23YMHamiltonianCarrierRecorded =
        true
    ; gate23YMHamiltonianCarrierRecordedIsTrue =
        refl
    ; gate6DHRSectorRepresentationFrontierRecorded =
        true
    ; gate6DHRSectorRepresentationFrontierRecordedIsTrue =
        refl
    ; gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromoted =
        false
    ; gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromotedIsFalse =
        refl
    ; gate23YMHamiltonianGate6DHRSectorRepresentationCompatibilityPromoted =
        false
    ; gate23YMHamiltonianGate6DHRSectorRepresentationCompatibilityPromotedIsFalse =
        refl
    ; gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromoted =
        false
    ; gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromotedIsFalse =
        refl
    ; inheritedStoneGeneratorIsNotPhysicalYMHamiltonian =
        YMH.stoneGeneratorIsPhysicalYMHamiltonianIsFalse
          YMH.canonicalGate8Term4StoneYMHamiltonianGapBridgeReceipt
    ; inheritedGate3StrictPromotionIsFalse =
        Gate3.gate3PromotedIsFalse
          Gate3.canonicalGate3DiscreteGeometryReceipt
    ; inheritedDHRSectorDecompositionPromotionIsFalse =
        DHR.sectorDecompositionPromotedIsFalse
          DHR.canonicalDHRSectorDecomposition
    ; blockers =
        canonicalCrossGateHamiltonianCompatibilityBlockers
    ; blockersAreCanonical =
        refl
    ; blockerStrings =
        canonicalCrossGateHamiltonianCompatibilityBlockerStrings
    ; blockerStringsAreCanonical =
        refl
    ; firstBlocker =
        missingGate5SelfAdjointGeneratorToGate23YMHamiltonianIdentification
    ; firstBlockerIsGate5ToGate23Identification =
        refl
    ; compatibilityBoundary =
        "Gate 5 supplies a finite Stone/GNS self-adjoint colimit generator witness"
        ∷ "Gate 2/3 supply finite Yang-Mills spectral-gap and discrete-geometry carrier receipts"
        ∷ "Gate 6 supplies DHR sector decomposition and representation-frontier data"
        ∷ "The Stone generator is not identified with the physical Yang-Mills Hamiltonian"
        ∷ "The Yang-Mills Hamiltonian action on DHR sector representations is not constructed"
        ∷ "No common domain, spectrum-preservation law, or cross-gate naturality law is inhabited"
        ∷ "All cross-gate Hamiltonian compatibility promotion fields are fixed false"
        ∷ []
    }

crossGateGate5ToGate23HamiltonianCompatibilityNotPromoted :
  gate5SelfAdjointGeneratorGate23YMHamiltonianCompatibilityPromoted
    canonicalCrossGateHamiltonianCompatibilityReceipt
  ≡
  false
crossGateGate5ToGate23HamiltonianCompatibilityNotPromoted =
  refl

crossGateGate23ToGate6HamiltonianCompatibilityNotPromoted :
  gate23YMHamiltonianGate6DHRSectorRepresentationCompatibilityPromoted
    canonicalCrossGateHamiltonianCompatibilityReceipt
  ≡
  false
crossGateGate23ToGate6HamiltonianCompatibilityNotPromoted =
  refl

crossGateHamiltonianCompatibilityNotPromoted :
  gate5Gate23Gate6CrossGateHamiltonianCompatibilityPromoted
    canonicalCrossGateHamiltonianCompatibilityReceipt
  ≡
  false
crossGateHamiltonianCompatibilityNotPromoted =
  refl
