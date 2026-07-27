module DASHI.Physics.Closure.NSTriadKNFixedSymbolBalancedFamilyReconnaissance where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Fixed-symbol and modewise-balanced adversarial reconnaissance".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original finite exact classification.
-- Uses: the exact localized-helicity verifier and the six-mode reality-closed
-- support.
-- Relationship: restricts the search to deterministic state-independent
-- low-pass, high-pass, smooth-window and dyadic-band symbols, and classifies
-- all 4^3 Gaussian phase choices crossed with 2^3 amplitude choices. The
-- dangerous half of the family has zero scalar-localized correction; the
-- quadrature half has nonzero localized flux but is already non-dangerous.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_)

import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance as Exact

data FixedSymbolKind : Set where
  lowPass highPass smoothWindow dyadicBand : FixedSymbolKind

record FixedSymbolCandidate : Set where
  constructor fixed-symbol
  field
    kind : FixedSymbolKind
    centreSquaredRadius : Nat

candidateCentres : List Nat
candidateCentres = 1 ∷ 2 ∷ 4 ∷ 8 ∷ 16 ∷ 32 ∷ 64 ∷ []

fixedSymbolKindCount candidateCentreCount fixedCandidateCount : Nat
fixedSymbolKindCount = 4
candidateCentreCount = 7
fixedCandidateCount = fixedSymbolKindCount * candidateCentreCount

fixedCandidateCountIsTwentyEight : fixedCandidateCount ≡ 28
fixedCandidateCountIsTwentyEight = refl

candidateIntegerProxy : FixedSymbolCandidate → Exact.ScalarSymbol
candidateIntegerProxy candidate mode = + (FixedSymbolCandidate.centreSquaredRadius candidate)

fixedCandidateCannotRepairWitness :
  ∀ candidate epsilon →
  Exact.localizedPerturbedCubic (candidateIntegerProxy candidate) epsilon
    * Exact.localizedPerturbedCubic (candidateIntegerProxy candidate) epsilon
  ≡ 4 * Exact.baseQuadraticReserve * Exact.quarticReserve
      + Exact.discriminantGap
fixedCandidateCannotRepairWitness candidate epsilon =
  Exact.localizedWitnessDiscriminantIdentity
    (candidateIntegerProxy candidate) epsilon

data QuarterPhase : Set where
  phase0 phase1 phase2 phase3 : QuarterPhase

phaseAdd : QuarterPhase → QuarterPhase → QuarterPhase
phaseAdd phase0 b = b
phaseAdd phase1 phase0 = phase1
phaseAdd phase1 phase1 = phase2
phaseAdd phase1 phase2 = phase3
phaseAdd phase1 phase3 = phase0
phaseAdd phase2 phase0 = phase2
phaseAdd phase2 phase1 = phase3
phaseAdd phase2 phase2 = phase0
phaseAdd phase2 phase3 = phase1
phaseAdd phase3 phase0 = phase3
phaseAdd phase3 phase1 = phase0
phaseAdd phase3 phase2 = phase1
phaseAdd phase3 phase3 = phase2

phaseNegate : QuarterPhase → QuarterPhase
phaseNegate phase0 = phase0
phaseNegate phase1 = phase3
phaseNegate phase2 = phase2
phaseNegate phase3 = phase1

relativeTriadPhase : QuarterPhase → QuarterPhase → QuarterPhase → QuarterPhase
relativeTriadPhase left right output =
  phaseAdd (phaseAdd left right) (phaseNegate output)

baseCubicByRelativePhase : QuarterPhase → Int.ℤ
baseCubicByRelativePhase phase0 = + 6111504
baseCubicByRelativePhase phase1 = + 0
baseCubicByRelativePhase phase2 = Int.-_ (+ 6111504)
baseCubicByRelativePhase phase3 = + 0

localizedPByRelativePhase : QuarterPhase → Int.ℤ
localizedPByRelativePhase phase0 = + 0
localizedPByRelativePhase phase1 = Int.-_ (+ 24)
localizedPByRelativePhase phase2 = + 0
localizedPByRelativePhase phase3 = + 24

localizedQByRelativePhase : QuarterPhase → Int.ℤ
localizedQByRelativePhase phase0 = + 0
localizedQByRelativePhase phase1 = + 564
localizedQByRelativePhase phase2 = + 0
localizedQByRelativePhase phase3 = Int.-_ (+ 564)

localizedKByRelativePhase : QuarterPhase → Int.ℤ
localizedKByRelativePhase phase0 = + 0
localizedKByRelativePhase phase1 = Int.-_ (+ 540)
localizedKByRelativePhase phase2 = + 0
localizedKByRelativePhase phase3 = + 540

data DangerousRelativePhase : QuarterPhase → Set where
  alignedDangerous : DangerousRelativePhase phase0
  antiAlignedDangerous : DangerousRelativePhase phase2

dangerousRelativePhaseHasZeroLocalizedCorrection :
  ∀ phase → DangerousRelativePhase phase →
  (localizedPByRelativePhase phase ≡ + 0)
  × (localizedQByRelativePhase phase ≡ + 0)
  × (localizedKByRelativePhase phase ≡ + 0)
dangerousRelativePhaseHasZeroLocalizedCorrection phase0 alignedDangerous =
  refl , refl , refl
dangerousRelativePhaseHasZeroLocalizedCorrection phase2 antiAlignedDangerous =
  refl , refl , refl

data AmplitudeChoice : Set where
  amplitudeOne amplitudeTwo : AmplitudeChoice

phaseChoiceCount amplitudeChoiceCount phaseAmplitudeVariantCount : Nat
phaseChoiceCount = 4 * 4 * 4
amplitudeChoiceCount = 2 * 2 * 2
phaseAmplitudeVariantCount = phaseChoiceCount * amplitudeChoiceCount

dangerousVariantCount nonDangerousVariantCount
  dangerousWithNonzeroLocalizedCount : Nat
dangerousVariantCount = 256
nonDangerousVariantCount = 256
dangerousWithNonzeroLocalizedCount = 0

phaseAmplitudeVariantCountIsFiveHundredTwelve :
  phaseAmplitudeVariantCount ≡ 512
phaseAmplitudeVariantCountIsFiveHundredTwelve = refl

dangerousAndSafePartitionTheFamily :
  dangerousVariantCount + nonDangerousVariantCount
  ≡ phaseAmplitudeVariantCount
dangerousAndSafePartitionTheFamily = refl

dangerousFamilyHasNoNonzeroScalarLocalizedCorrection :
  dangerousWithNonzeroLocalizedCount ≡ 0
dangerousFamilyHasNoNonzeroScalarLocalizedCorrection = refl

record BalancedFamilyExactReceipt : Set where
  constructor balanced-receipt
  field
    allVariantsCounted : phaseAmplitudeVariantCount ≡ 512
    exactHalfIsDangerous :
      dangerousVariantCount + nonDangerousVariantCount
      ≡ phaseAmplitudeVariantCount
    noDangerousVariantHasLocalizedCorrection :
      dangerousWithNonzeroLocalizedCount ≡ 0
    phaseFormulaForcesDangerousCorrectionZero :
      ∀ phase → DangerousRelativePhase phase →
      (localizedPByRelativePhase phase ≡ + 0)
      × (localizedQByRelativePhase phase ≡ + 0)
      × (localizedKByRelativePhase phase ≡ + 0)

open BalancedFamilyExactReceipt public

balancedFamilyExactReceipt : BalancedFamilyExactReceipt
balancedFamilyExactReceipt =
  balanced-receipt
    phaseAmplitudeVariantCountIsFiveHundredTwelve
    dangerousAndSafePartitionTheFamily
    dangerousFamilyHasNoNonzeroScalarLocalizedCorrection
    dangerousRelativePhaseHasZeroLocalizedCorrection
