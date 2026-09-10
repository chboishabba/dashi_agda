{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanGeometricRateGapCandidateRound286Exact where

------------------------------------------------------------------------
-- ROUND286 / POSITIVE GAP CANDIDATE IS NOT AN INDEPENDENT YM ESTIMATE
--
-- R284 fixes the direct clustering ratio q = 1/2.  On a physical transfer
-- semigroup energy coordinate, the corresponding exponential rate is
-- m(q) = -log q.  Positivity of m(q) for 0 < q < 1 is standard real analysis.
--
-- The physical theorem is the SAME-ENERGY normalization: the reconstructed
-- spectrum's selected gap candidate must be the transfer-energy value
-- corresponding to that exact clustering rate.  This module deliberately does
-- not choose a fake Energy carrier or manufacture the normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record GeometricDecayRateAuthority (Ratio Energy : Set) : Set₁ where
  field
    PositiveRatio : Ratio → Set
    StrictlyBelowOne : Ratio → Set
    PositiveEnergy : Energy → Set

    rateEnergy : Ratio → Energy

    ratePositiveBelowOne : ∀ ratio →
      PositiveRatio ratio →
      StrictlyBelowOne ratio →
      PositiveEnergy (rateEnergy ratio)

open GeometricDecayRateAuthority public

record SameRateGapCandidate
    {Observable Energy Bound Ratio : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    (rateAuthority : GeometricDecayRateAuthority Ratio Energy)
    (ratio : Ratio) : Set₁ where
  field
    ratioPositive : PositiveRatio rateAuthority ratio
    ratioStrictlyBelowOne : StrictlyBelowOne rateAuthority ratio

    spectrumPositiveEnergyIsRatePositive : ∀ energy →
      Gap.PositiveEnergy spectrum energy ≡ PositiveEnergy rateAuthority energy

    gapCandidateIsRateEnergy :
      Gap.gapCandidate spectrum ≡ rateEnergy rateAuthority ratio

open SameRateGapCandidate public

candidateGapPositiveFromSameRate :
  ∀ {Observable Energy Bound Ratio}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    {rateAuthority : GeometricDecayRateAuthority Ratio Energy}
    {ratio : Ratio} →
  SameRateGapCandidate spectrum rateAuthority ratio →
  Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)
candidateGapPositiveFromSameRate
    {spectrum = spectrum} {rateAuthority = rateAuthority} {ratio = ratio}
    payment =
  let
    ratePositive : PositiveEnergy rateAuthority (rateEnergy rateAuthority ratio)
    ratePositive = ratePositiveBelowOne rateAuthority ratio
      (ratioPositive payment)
      (ratioStrictlyBelowOne payment)

    spectrumRatePositive :
      Gap.PositiveEnergy spectrum (rateEnergy rateAuthority ratio)
    spectrumRatePositive rewrite
      spectrumPositiveEnergyIsRatePositive payment (rateEnergy rateAuthority ratio) =
        ratePositive
  in
  transportGapCandidate payment spectrumRatePositive
  where
  transportGapCandidate :
    ∀ {Observable Energy Bound Ratio}
      {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
      {authority : GeometricDecayRateAuthority Ratio Energy}
      {selectedRatio : Ratio}
      (sameRate : SameRateGapCandidate spectrum authority selectedRatio) →
      Gap.PositiveEnergy spectrum (rateEnergy authority selectedRatio) →
      Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)
  transportGapCandidate sameRate proof rewrite
    gapCandidateIsRateEnergy sameRate = proof

record Round286Boundary : Set where
  constructor round286-boundary
  field
    candidateGapPositivityIndependentYMEstimate : Bool
    candidateGapPositivityIndependentYMEstimateIsFalse :
      candidateGapPositivityIndependentYMEstimate ≡ false

    sameTransferEnergyRateNormalizationRequired : Bool
    sameTransferEnergyRateNormalizationRequiredIsTrue :
      sameTransferEnergyRateNormalizationRequired ≡ true

    fakeConvenientEnergyCarrierPermitted : Bool
    fakeConvenientEnergyCarrierPermittedIsFalse :
      fakeConvenientEnergyCarrierPermitted ≡ false

canonicalRound286Boundary : Round286Boundary
canonicalRound286Boundary =
  round286-boundary false refl true refl false refl

round286RatePositivityBelowUnitRatioLevel : ProofLevel
round286RatePositivityBelowUnitRatioLevel = standardImported

round286GapPositivityCompilerLevel : ProofLevel
round286GapPositivityCompilerLevel = machineChecked

round286SameTransferEnergyRateNormalizationLevel : ProofLevel
round286SameTransferEnergyRateNormalizationLevel = conditional
