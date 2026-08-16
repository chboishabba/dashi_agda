module DASHI.Physics.YangMills.BalabanCMP99CovarianceLocalityToRGStateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DIRECT SOURCE PROFILE
--
-- Theorems 3.1--3.3 give local/global bounds and exponential kernel decay for
-- the background-dependent scalar/gauge propagators and constrained inverse,
-- with constants uniform in the admissible domain sequence.  Theorem 3.4
-- extends the estimates analytically to a complex regular-background tube.
-- The generalized random-walk expansion of Theorem 3.7 / Corollary 3.8 gives
-- the corresponding localization mechanism.
--
-- DASHI CONTRIBUTION
--
-- The covariance/locality field in the lightweight YM invariant region should
-- not ask for another proof of exponential decay.  Once the actual next-step
-- background is identified as CMP99-regular and the repository covariance is
-- identified with the source constrained/gauge propagator in the same norm,
-- source decay transports directly to the RG coordinate.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record CMP99ToRGNextCovariance
    (Background Site : Set)
    (parameters : RG.YM4RGRegionParameters)
    (next : RG.YM4RGState) : Set₁ where
  field
    nextBackground : Background
    RegularBackground : Background → Set
    nextBackgroundRegular : RegularBackground nextBackground

    sourceCovarianceNorm : Background → ℚ
    sourceDecayExponent : Background → ℚ

    sourceNormBound :
      sourceCovarianceNorm nextBackground ≤ RG.covarianceCap parameters

    repositoryCovarianceBelowSource :
      RG.conditionalCovarianceNorm next
      ≤ sourceCovarianceNorm nextBackground

    repositoryDecayAtLeastSource :
      sourceDecayExponent nextBackground
      ≤ RG.latticeDecayExponent next

open CMP99ToRGNextCovariance public

cmp99CovarianceCapForNextState :
  ∀ {Background Site parameters next} →
  CMP99ToRGNextCovariance Background Site parameters next →
  RG.conditionalCovarianceNorm next ≤ RG.covarianceCap parameters
cmp99CovarianceCapForNextState dataSet =
  ℚP.≤-trans
    (repositoryCovarianceBelowSource dataSet)
    (sourceNormBound dataSet)

cmp99BackgroundPropagatorDecayAuthorityLevel : ProofLevel
cmp99BackgroundPropagatorDecayAuthorityLevel = standardImported

cmp99NextStateCovarianceTransportLevel : ProofLevel
cmp99NextStateCovarianceTransportLevel = machineChecked

cmp99NextBackgroundRegularityLevel : ProofLevel
cmp99NextBackgroundRegularityLevel = conditional

cmp99RepositoryCovarianceDictionaryLevel : ProofLevel
cmp99RepositoryCovarianceDictionaryLevel = conditional
