module DASHI.Biology.Levin.MitochondrialCristaOscillatorBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Candidate-only boundary for treating a mitochondrial crista as an
-- oscillator-bearing bioenergetic compartment.
--
-- The known structural carriers and the proposed engineering equivalences
-- are separated.  ATP synthase rotation does not by itself prove a voltage-
-- controlled oscillator, and crista geometry does not by itself prove a
-- resonant cavity or phase-locked loop.

record CristaArchitecture : Set where
  field
    innerMembraneFolded : Bool
    cristaJunctionPresent : Bool
    atpSynthaseRowsPresent : Bool
    electronTransportPresent : Bool

record OscillatorInterpretation : Set where
  field
    referenceOscillatorProposed : Bool
    phaseDetectorProposed : Bool
    loopFilterProposed : Bool
    voltageControlledOscillatorProposed : Bool
    resonantCavityProposed : Bool

record CristaOscillatorBoundary : Set where
  field
    architecture : CristaArchitecture
    interpretation : OscillatorInterpretation

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    rotationIsNotYetVCOProof : Bool
    rotationIsNotYetVCOProofIsFalse : rotationIsNotYetVCOProof ≡ false

    geometryIsNotYetResonatorProof : Bool
    geometryIsNotYetResonatorProofIsFalse : geometryIsNotYetResonatorProof ≡ false

    noClockFunctionPromotion : Bool
    noClockFunctionPromotionIsFalse : noClockFunctionPromotion ≡ false

    reading : String

open CristaOscillatorBoundary public

canonicalCristaOscillatorBoundary : CristaOscillatorBoundary
canonicalCristaOscillatorBoundary = record
  { architecture = record
      { innerMembraneFolded = true
      ; cristaJunctionPresent = true
      ; atpSynthaseRowsPresent = true
      ; electronTransportPresent = true
      }
  ; interpretation = record
      { referenceOscillatorProposed = true
      ; phaseDetectorProposed = true
      ; loopFilterProposed = true
      ; voltageControlledOscillatorProposed = true
      ; resonantCavityProposed = true
      }
  ; candidateOnly = true
  ; candidateOnlyIsTrue = refl
  ; rotationIsNotYetVCOProof = false
  ; rotationIsNotYetVCOProofIsFalse = refl
  ; geometryIsNotYetResonatorProof = false
  ; geometryIsNotYetResonatorProofIsFalse = refl
  ; noClockFunctionPromotion = false
  ; noClockFunctionPromotionIsFalse = refl
  ; reading = "Crista architecture is empirical; PLL, VCO, resonator, and clock readings are candidate engineering models requiring independent dynamical evidence"
  }
