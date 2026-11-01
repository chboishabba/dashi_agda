module DASHI.Empirical.DarkDimensionBedroyaNormalizationAxisJoinExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as AxisJoin
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Empirical.DarkDimensionBedroyaParameterManifestBoundaryExact as Manifest

------------------------------------------------------------------------
-- BEDROYA NORMALIZATION DEPENDENCY AXIS JOIN
--
-- This is a declared dependency model, not a claim that the finite states below
-- are empirical cosmological worlds.  It records that the source-paid paper DM
-- normalization coordinate is distinct from two further inputs required by the
-- executable reconstruction: sampled-density correspondence and V0
-- normalization.
------------------------------------------------------------------------

data NormalizationDependencyState : Set where
  paperDMOnly : NormalizationDependencyState
  paperDMWithSampledDensity : NormalizationDependencyState
  paperDMWithV0 : NormalizationDependencyState
  fullNormalization : NormalizationDependencyState

data PaperDMPayment : Set where
  paperDMPaid : PaperDMPayment

data SampledDensityAxis : Set where
  sampledDensityMissing sampledDensityPaid : SampledDensityAxis

data V0NormalizationAxis : Set where
  v0NormalizationMissing v0NormalizationPaid : V0NormalizationAxis

paperDMObserver : NormalizationDependencyState → PaperDMPayment
paperDMObserver _ = paperDMPaid

sampledDensityAxis : NormalizationDependencyState → SampledDensityAxis
sampledDensityAxis paperDMOnly = sampledDensityMissing
sampledDensityAxis paperDMWithSampledDensity = sampledDensityPaid
sampledDensityAxis paperDMWithV0 = sampledDensityMissing
sampledDensityAxis fullNormalization = sampledDensityPaid

v0NormalizationAxis : NormalizationDependencyState → V0NormalizationAxis
v0NormalizationAxis paperDMOnly = v0NormalizationMissing
v0NormalizationAxis paperDMWithSampledDensity = v0NormalizationMissing
v0NormalizationAxis paperDMWithV0 = v0NormalizationPaid
v0NormalizationAxis fullNormalization = v0NormalizationPaid

sampledDensityStatesDiffer :
  sampledDensityAxis paperDMOnly ≡
  sampledDensityAxis paperDMWithSampledDensity → ⊥
sampledDensityStatesDiffer ()

v0StatesDiffer :
  v0NormalizationAxis paperDMOnly ≡
  v0NormalizationAxis paperDMWithV0 → ⊥
v0StatesDiffer ()

sampledDensityMissingWitness :
  NonFactor.NonFactorabilityWitness paperDMObserver sampledDensityAxis
sampledDensityMissingWitness =
  NonFactor.nonFactorabilityWitness
    paperDMOnly
    paperDMWithSampledDensity
    refl
    sampledDensityStatesDiffer

v0NormalizationMissingWitness :
  NonFactor.NonFactorabilityWitness paperDMObserver v0NormalizationAxis
v0NormalizationMissingWitness =
  NonFactor.nonFactorabilityWitness
    paperDMOnly
    paperDMWithV0
    refl
    v0StatesDiffer

paperDMObserverCannotRetainSampledDensityAxis :
  AxisJoin.RetainsAxis paperDMObserver sampledDensityAxis → ⊥
paperDMObserverCannotRetainSampledDensityAxis =
  NonFactor.witnessRulesOutEveryFlatFactorisation sampledDensityMissingWitness

paperDMObserverCannotRetainV0Axis :
  AxisJoin.RetainsAxis paperDMObserver v0NormalizationAxis → ⊥
paperDMObserverCannotRetainV0Axis =
  NonFactor.witnessRulesOutEveryFlatFactorisation v0NormalizationMissingWitness

paperDMObserverCannotRetainBothMissingAxes :
  AxisJoin.RetainsBothRequiredAxes
    paperDMObserver
    sampledDensityAxis
    v0NormalizationAxis →
  ⊥
paperDMObserverCannotRetainBothMissingAxes =
  AxisJoin.leftAxisDefectBlocksRetainingBoth sampledDensityMissingWitness

requiredNormalizationJoin :
  NormalizationDependencyState → SampledDensityAxis × V0NormalizationAxis
requiredNormalizationJoin =
  AxisJoin.jointAxis sampledDensityAxis v0NormalizationAxis

paperDMIdentitySourcePaid :
  Manifest.m0n0ToRhoDM0PaperIdentityLocated
    Manifest.canonicalBedroyaParameterManifestStatus
  ≡ true
paperDMIdentitySourcePaid = Manifest.paperDMNormalizationIdentityPaid

sampledDensitySourceStillOpen :
  Manifest.rhoDM0ToSampledOmegaFDMMappingLocated
    Manifest.canonicalBedroyaParameterManifestStatus
  ≡ false
sampledDensitySourceStillOpen = Manifest.sampledOmegaFDMMappingStillOpen

v0NormalizationSourceStillOpen :
  Manifest.v0ToSampledDarkEnergyNormalizationLocated
    Manifest.canonicalBedroyaParameterManifestStatus
  ≡ false
v0NormalizationSourceStillOpen = Manifest.v0NormalizationStillOpen

data PaidDMAxisCompensatesMissingSampledOrV0Axis : Set where

paidDMAxisDoesNotCompensateMissingSampledOrV0Axis :
  PaidDMAxisCompensatesMissingSampledOrV0Axis → ⊥
paidDMAxisDoesNotCompensateMissingSampledOrV0Axis ()
