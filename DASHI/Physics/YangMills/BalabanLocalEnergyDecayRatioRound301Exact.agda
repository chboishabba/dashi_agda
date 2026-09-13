{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLocalEnergyDecayRatioRound301Exact where

------------------------------------------------------------------------
-- ROUND301 / CONSUMER-LOCAL ENERGY <-> DECAY-RATIO SEMANTICS
--
-- R285 asks for a global map `decayRatioToEnergy : Q -> Energy`.  Canonical B
-- does not consume such a global inverse.  It uses only:
--
--   * the ratio of the selected candidate gap;
--   * the ratio of a hypothetical positive subgap energy;
--   * strict energy order -> reversed decay-rate order;
--   * strict ratio below one -> positive candidate energy.
--
-- This is the spectral analogue of the fold-local bridge used elsewhere in the
-- repo: keep only the coordinates observed by the terminal consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274

record LocalEnergyDecayRatioSemantics
    {Observable Energy Bound : Set}
    (spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound)
    : Set₁ where
  field
    ratioOfEnergy : Energy → ℚ

    candidateRatioIsHalf :
      ratioOfEnergy (Gap.gapCandidate spectrum) ≡ Geo.half

    ratioNonnegativeForPositiveEnergy : ∀ energy →
      Gap.PositiveEnergy spectrum energy →
      0ℚ ≤ ratioOfEnergy energy

    positiveEnergyFromStrictDecay : ∀ energy →
      0ℚ ≤ ratioOfEnergy energy →
      ratioOfEnergy energy < 1ℚ →
      Gap.PositiveEnergy spectrum energy

    positiveEnergyHasStrictDecay : ∀ energy →
      Gap.PositiveEnergy spectrum energy →
      ratioOfEnergy energy < 1ℚ

    positiveSubgapHasSlowerDecay : ∀ energy →
      Gap.PositiveEnergy spectrum energy →
      Gap.StrictlyBelow spectrum energy (Gap.gapCandidate spectrum) →
      Geo.half < ratioOfEnergy energy

open LocalEnergyDecayRatioSemantics public

candidateRatioNonnegative :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    (semantics : LocalEnergyDecayRatioSemantics spectrum) →
  0ℚ ≤ ratioOfEnergy semantics (Gap.gapCandidate spectrum)
candidateRatioNonnegative semantics =
  subst
    (λ ratio → 0ℚ ≤ ratio)
    (sym (candidateRatioIsHalf semantics))
    Geo.halfNonnegative

candidateRatioStrictlyBelowOne :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound}
    (semantics : LocalEnergyDecayRatioSemantics spectrum) →
  ratioOfEnergy semantics (Gap.gapCandidate spectrum) < 1ℚ
candidateRatioStrictlyBelowOne semantics =
  subst
    (λ ratio → ratio < 1ℚ)
    (sym (candidateRatioIsHalf semantics))
    R274.halfStrictlyBelowOne

candidateGapPositiveFromLocalRate :
  ∀ {Observable Energy Bound}
    {spectrum : Gap.ReconstructedClusteringSpectrum Observable Energy Bound} →
  LocalEnergyDecayRatioSemantics spectrum →
  Gap.PositiveEnergy spectrum (Gap.gapCandidate spectrum)
candidateGapPositiveFromLocalRate semantics =
  positiveEnergyFromStrictDecay semantics
    (Gap.gapCandidate _)
    (candidateRatioNonnegative semantics)
    (candidateRatioStrictlyBelowOne semantics)

record Round301Boundary : Set where
  constructor round301-boundary
  field
    globalRatioToEnergyFunctionRequired : Bool
    globalRatioToEnergyFunctionRequiredIsFalse :
      globalRatioToEnergyFunctionRequired ≡ false

    arbitraryPositiveGapTokenRequired : Bool
    arbitraryPositiveGapTokenRequiredIsFalse :
      arbitraryPositiveGapTokenRequired ≡ false

    candidateHalfRateAndSubgapRateOrderSuffice : Bool
    candidateHalfRateAndSubgapRateOrderSufficeIsTrue :
      candidateHalfRateAndSubgapRateOrderSuffice ≡ true

canonicalRound301Boundary : Round301Boundary
canonicalRound301Boundary =
  round301-boundary false refl false refl true refl

round301LocalRateToCandidatePositiveCompilerLevel : ProofLevel
round301LocalRateToCandidatePositiveCompilerLevel = machineChecked

-- Same reconstructed semigroup/Hamiltonian source realization: identify the
-- decay ratio of the actual energy coordinates, prove positive energies have
-- ratios in [0,1), and strict subgap energy order reverses to a slower ratio.
round301PhysicalLocalEnergyRateSemanticsLevel : ProofLevel
round301PhysicalLocalEnergyRateSemanticsLevel = conditional
