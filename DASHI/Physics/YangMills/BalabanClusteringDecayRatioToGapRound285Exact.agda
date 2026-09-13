{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClusteringDecayRatioToGapRound285Exact where

------------------------------------------------------------------------
-- ROUND285 / B2 IS RATE-TO-SPECTRUM IDENTIFICATION, NOT A POSITIVITY TOKEN
--
-- R275 correctly keeps positivity of the selected gap candidate independent
-- from the clustering upper.  But on every exponential/geometric clustering
-- producer, the candidate is not meant to be an arbitrary positive energy: it
-- is the spectral energy corresponding to the proved decay rate.
--
-- This owner therefore factors B2 into the exact physical statement:
--
--   0 <= q < 1
--   + decayRatioToEnergy(q)
--   + theorem that a strict decay ratio maps to positive reconstructed energy
--   + SAME-OBJECT identification
--       gapCandidate == decayRatioToEnergy(q)
--
-- -> PositiveEnergy(gapCandidate).
--
-- No logarithm, transfer-matrix convention, or units are invented here.  The
-- application must supply the correct rate-to-energy semantics for the exact
-- reconstructed spectrum.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record DecayRatioGapIdentification
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    decayRatio : ℚ
    decayRatioNonnegative : 0ℚ ≤ decayRatio
    decayRatioStrictlyBelowOne : decayRatio < 1ℚ

    decayRatioToEnergy : ℚ → Energy

    strictDecayMapsToPositiveEnergy : ∀ ratio →
      0ℚ ≤ ratio → ratio < 1ℚ →
      Gap.PositiveEnergy spectrum (decayRatioToEnergy ratio)

    gapCandidateIsDecayEnergy :
      Gap.gapCandidate spectrum ≡ decayRatioToEnergy decayRatio

open DecayRatioGapIdentification public

candidateGapPositiveFromDecayRate :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  DecayRatioGapIdentification spectrum →
  Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)
candidateGapPositiveFromDecayRate identification =
  subst
    (Gap.PositiveEnergy _)
    (sym (gapCandidateIsDecayEnergy identification))
    (strictDecayMapsToPositiveEnergy identification
      (decayRatio identification)
      (decayRatioNonnegative identification)
      (decayRatioStrictlyBelowOne identification))

record Round285Boundary : Set where
  constructor round285-boundary
  field
    arbitraryStoredGapPositivityRequired : Bool
    arbitraryStoredGapPositivityRequiredIsFalse :
      arbitraryStoredGapPositivityRequired ≡ false

    exactRateToSpectrumIdentificationRequired : Bool
    exactRateToSpectrumIdentificationRequiredIsTrue :
      exactRateToSpectrumIdentificationRequired ≡ true

    positivityAfterRateIdentificationCompilerOwned : Bool
    positivityAfterRateIdentificationCompilerOwnedIsTrue :
      positivityAfterRateIdentificationCompilerOwned ≡ true

    logarithmConventionInventedHere : Bool
    logarithmConventionInventedHereIsFalse : logarithmConventionInventedHere ≡ false

canonicalRound285Boundary : Round285Boundary
canonicalRound285Boundary =
  round285-boundary false refl true refl true refl false refl

round285RateToPositiveCandidateCompilerLevel : ProofLevel
round285RateToPositiveCandidateCompilerLevel = machineChecked

-- Physical/spectral theorem: identify the exact clustering rate parameter with
-- the exact reconstructed transfer-energy candidate under the correct OS/
-- semigroup convention, and prove strict decay maps to positive energy.
round285PhysicalRateToSpectrumIdentificationLevel : ProofLevel
round285PhysicalRateToSpectrumIdentificationLevel = conditional
