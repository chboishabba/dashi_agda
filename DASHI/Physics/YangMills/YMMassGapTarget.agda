module DASHI.Physics.YangMills.YMMassGapTarget where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives

data YMMassGapTargetObligation : Set where
  needsQuantumMeasureConstruction : YMMassGapTargetObligation
  needsOSAxiomVerification        : YMMassGapTargetObligation
  needsWightmanReconstruction     : YMMassGapTargetObligation
  needsSpectralGapProof           : YMMassGapTargetObligation

canonicalYMMassGapTargetObligations : List YMMassGapTargetObligation
canonicalYMMassGapTargetObligations =
  needsQuantumMeasureConstruction
  ∷ needsOSAxiomVerification
  ∷ needsWightmanReconstruction
  ∷ needsSpectralGapProof
  ∷ []

record YMMassGapTarget (N : Nat) : Set₁ where
  field
    gaugeGroupIsSUN : Bool
    baseSpaceIsR4Euclidean : Bool
    actionIsPureYM : Bool
    gaugeGroupIsSUNIsTrue : gaugeGroupIsSUN ≡ true
    baseSpaceIsR4EuclideanIsTrue : baseSpaceIsR4Euclidean ≡ true
    actionIsPureYMIsTrue : actionIsPureYM ≡ true
    quantumMeasureExists : Bool
    osAxiomsSatisfied : Bool
    wightmanReconstructed : Bool
    spectralGapProved : Bool
    clayTargetMet : Bool
    quantumMeasureExistsIsFalse : quantumMeasureExists ≡ false
    osAxiomsSatisfiedIsFalse : osAxiomsSatisfied ≡ false
    wightmanReconstructedIsFalse : wightmanReconstructed ≡ false
    spectralGapProvedIsFalse : spectralGapProved ≡ false
    clayTargetMetIsFalse : clayTargetMet ≡ false
    openObligations : List YMMassGapTargetObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalYMMassGapTargetObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

canonicalYMMassGapTarget : (N : Nat) → YMMassGapTarget N
canonicalYMMassGapTarget N = record
  { gaugeGroupIsSUN = true
  ; baseSpaceIsR4Euclidean = true
  ; actionIsPureYM = true
  ; gaugeGroupIsSUNIsTrue = refl
  ; baseSpaceIsR4EuclideanIsTrue = refl
  ; actionIsPureYMIsTrue = refl
  ; quantumMeasureExists = false
  ; osAxiomsSatisfied = false
  ; wightmanReconstructed = false
  ; spectralGapProved = false
  ; clayTargetMet = false
  ; quantumMeasureExistsIsFalse = refl
  ; osAxiomsSatisfiedIsFalse = refl
  ; wightmanReconstructedIsFalse = refl
  ; spectralGapProvedIsFalse = refl
  ; clayTargetMetIsFalse = refl
  ; openObligations = canonicalYMMassGapTargetObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
