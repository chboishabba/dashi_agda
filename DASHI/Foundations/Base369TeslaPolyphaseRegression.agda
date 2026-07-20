module DASHI.Foundations.Base369TeslaPolyphaseRegression where

open import Agda.Builtin.Equality using (_≡_)

open import Base369 using
  ( TriTruth
  ; tri-mid
  ; tri-high
  ; hex-4
  )
open import DASHI.Foundations.Base369CirclePhase using
  ( triToHex
  ; triToNonary
  ; hexTo18
  ; nonaryTo18
  )
open import DASHI.Foundations.Base369BinaryTernaryRefinement
open import DASHI.Foundations.Base369PolyphaseCharacters
open import DASHI.Foundations.Base369EngineeringMDL
open import DASHI.Foundations.Base369TriadicPhaseTower
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( hexTruthToFactor
  ; hexFactorToTruth
  ; hexTruthToFactor-decodingRoundTrip
  )
open import DASHI.Physics.Closure.Base369PolyphaseKernelBoundary
open import DASHI.Physics.Closure.Base369AutomorphicSpectralGate
open import DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary
open import DASHI.Geometry.Base369SectorUnrollingFinite

------------------------------------------------------------------------
-- Focused checked examples.

midPhaseRefinementDiamond :
  hexTo18 (triToHex tri-mid) ≡
  nonaryTo18 (triToNonary tri-mid)
midPhaseRefinementDiamond = circlePhaseRefinementDiamond tri-mid

positiveSequenceMidExponent :
  characterExponent3 positiveSequence tri-mid ≡ tri-mid
positiveSequenceMidExponent = positiveSequence-at-mid

negativeSequenceHighExponent :
  characterExponent3 negativeSequence tri-high ≡ tri-mid
negativeSequenceHighExponent = negativeSequence-at-high

triadicTowerHighSection :
  phase27ToTriSector (triTo27 tri-high) ≡ tri-high
triadicTowerHighSection = triTo27-section tri-high

hex4FactorRoundTrip :
  hexFactorToTruth
    (DASHI.Core.Prelude.proj₁ (hexTruthToFactor hex-4))
    (DASHI.Core.Prelude.proj₂ (hexTruthToFactor hex-4))
  ≡ hex-4
hex4FactorRoundTrip = hexTruthToFactor-decodingRoundTrip hex-4

------------------------------------------------------------------------
-- Compact aggregate receipt.

record Base369TeslaPolyphaseReceipt : Set where
  field
    refinementReceipt : BinaryTernaryRefinementReceipt
    characterReceipt : C3CharacterReceipt
    characterBoundary : PolyphaseCharacterAnalyticBoundary
    kernelReceipt : C3KernelModeReceipt
    spectralBoundary : PolyphaseSpectralBoundary
    engineeringBoundary : EngineeringMDLBoundary
    triadicTowerReceipt : TriadicPhaseTowerFragmentReceipt
    finiteUnrollingReceipt : FiniteSectorUnrollingReceipt
    automorphicGate : AutomorphicSpectralGate
    historicalBoundary : TeslaPolyphaseHistoricalBoundary

base369TeslaPolyphaseReceipt : Base369TeslaPolyphaseReceipt
base369TeslaPolyphaseReceipt =
  record
    { refinementReceipt = base369BinaryTernaryRefinementReceipt
    ; characterReceipt = positiveSequenceReceipt
    ; characterBoundary = polyphaseCharacterAnalyticBoundary
    ; kernelReceipt = positiveSequenceKernelReceipt
    ; spectralBoundary = polyphaseSpectralBoundary
    ; engineeringBoundary = base369EngineeringMDLBoundary
    ; triadicTowerReceipt = base369TriadicPhaseTowerFragmentReceipt
    ; finiteUnrollingReceipt = canonicalThreeRingUnrollingReceipt
    ; automorphicGate = base369AutomorphicSpectralGate
    ; historicalBoundary = teslaPolyphaseBoundary
    }
