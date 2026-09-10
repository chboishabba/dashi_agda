{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound294Exact where

------------------------------------------------------------------------
-- ROUND294 / DIRECT B MIN-CUT AFTER TWO R293 COMPILER REDUCTIONS
--
-- R292 still charged two compiler-owned statements as physical coordinates:
--   * D^2 log Z = connected covariance inside D1a;
--   * an opaque separating-time theorem inside D3.
--
-- `BalabanCMP116StateFamilyTwoJNormalizationRound293Exact` compiles the first
-- pointwise over the whole finite state family using Scalar = State -> Q.
-- `BalabanSubgapGeometricSeparationRound293Exact` compiles the second once the
-- physical spectral envelopes are given their explicit amplitudes/rates.
--
-- Surviving direct-route theorem/source coordinates are therefore:
--
--   E1. literal selected physical observables instantiate the CMP116/CMP119 J
--       directions to which the published differentiated localization applies;
--   E2. that source covariance is the SAME selected finite T5 covariance;
--   E3. OS spectral representation gives the positive lower envelope from the
--       actual cyclic overlap on the SAME continuum covariance carrier;
--   E4. physical subgap-rate semantics: an alleged positive energy below the
--       candidate has positive overlap amplitude and a strictly slower ratio;
--   E5. the direct clustering ratio q=1/2 is the SAME reconstructed candidate
--       energy under the physical OS/semigroup convention.
--
-- The log-cumulant algebra, covariance transport, observable/overlap choice,
-- geometric separating time, slow/fast contradiction and final positive-gap
-- assembly are compiler consequences.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound292Exact as R292
import DASHI.Physics.YangMills.BalabanCMP116StateFamilyTwoJNormalizationRound293Exact as Source293
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as Spectral293


data DirectBSearchObject294 : Set where
  literalPhysicalJDirectionLocalization : DirectBSearchObject294
  sourceCovarianceSelectedT5SameObject : DirectBSearchObject294
  physicalSpectralLowerFromOverlap : DirectBSearchObject294
  physicalSubgapRateSemantics : DirectBSearchObject294
  clusteringRateToSpectrumEnergy : DirectBSearchObject294

  secondLogDerivativeCovarianceIdentity : DirectBSearchObject294
  opaqueSeparatingTime : DirectBSearchObject294
  covarianceAlgebraAndLimit : DirectBSearchObject294
  continuumCovarianceSpectrumIdentity : DirectBSearchObject294
  subgapObservableAndOverlapChoice : DirectBSearchObject294
  fullSlowFastContradiction : DirectBSearchObject294
  positiveTransferGap : DirectBSearchObject294

searchRole294 : DirectBSearchObject294 → Introspective.ProofSearchTargetRole
searchRole294 literalPhysicalJDirectionLocalization =
  Introspective.canonicalConsumerResidual
searchRole294 sourceCovarianceSelectedT5SameObject =
  Introspective.canonicalConsumerResidual
searchRole294 physicalSpectralLowerFromOverlap =
  Introspective.canonicalConsumerResidual
searchRole294 physicalSubgapRateSemantics =
  Introspective.canonicalConsumerResidual
searchRole294 clusteringRateToSpectrumEnergy =
  Introspective.canonicalConsumerResidual

searchRole294 secondLogDerivativeCovarianceIdentity = Introspective.compilerConsequence
searchRole294 opaqueSeparatingTime = Introspective.compilerConsequence
searchRole294 covarianceAlgebraAndLimit = Introspective.compilerConsequence
searchRole294 continuumCovarianceSpectrumIdentity = Introspective.compilerConsequence
searchRole294 subgapObservableAndOverlapChoice = Introspective.compilerConsequence
searchRole294 fullSlowFastContradiction = Introspective.compilerConsequence
searchRole294 positiveTransferGap = Introspective.compilerConsequence

record Round294Boundary : Set where
  constructor round294-boundary
  field
    r292SecondLogCovarianceIdentityStillPhysical : Bool
    r292SecondLogCovarianceIdentityStillPhysicalIsFalse :
      r292SecondLogCovarianceIdentityStillPhysical ≡ false

    r292OpaqueSeparatingTimeStillPhysical : Bool
    r292OpaqueSeparatingTimeStillPhysicalIsFalse :
      r292OpaqueSeparatingTimeStillPhysical ≡ false

    directPhysicalCutHasFiveCoordinates : Bool
    directPhysicalCutHasFiveCoordinatesIsTrue :
      directPhysicalCutHasFiveCoordinates ≡ true

    sourceDerivativeLocalizationReproved : Bool
    sourceDerivativeLocalizationReprovedIsFalse :
      sourceDerivativeLocalizationReproved ≡ false

    geometricDominanceNewYMAnalysis : Bool
    geometricDominanceNewYMAnalysisIsFalse :
      geometricDominanceNewYMAnalysis ≡ false

canonicalRound294Boundary : Round294Boundary
canonicalRound294Boundary =
  round294-boundary false refl false refl true refl false refl false refl

round294StateFamilyLogCovarianceCompilerLevel : ProofLevel
round294StateFamilyLogCovarianceCompilerLevel =
  Source293.round293SecondLogDerivativeCovarianceMeaningLevel

round294SeparatingTimeCompilerLevel : ProofLevel
round294SeparatingTimeCompilerLevel = Spectral293.round293SeparatingTimeCompilerLevel

round294LiteralPhysicalJDirectionLocalizationLevel : ProofLevel
round294LiteralPhysicalJDirectionLocalizationLevel =
  Source293.round293LiteralPhysicalJDirectionLocalizationLevel

round294SourceCovarianceSelectedT5SameObjectLevel : ProofLevel
round294SourceCovarianceSelectedT5SameObjectLevel =
  R292.round292SourceCovarianceSelectedT5SameObjectLevel

round294PhysicalSpectralLowerFromOverlapLevel : ProofLevel
round294PhysicalSpectralLowerFromOverlapLevel =
  R292.round292PhysicalSpectralLowerFromOverlapLevel

round294PhysicalSubgapRateSemanticsLevel : ProofLevel
round294PhysicalSubgapRateSemanticsLevel =
  Spectral293.round293PhysicalSubgapRateSemanticsLevel

round294ClusteringRateToSpectrumEnergyLevel : ProofLevel
round294ClusteringRateToSpectrumEnergyLevel =
  R292.round292ClusteringRateToSpectrumEnergyLevel
