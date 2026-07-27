module DASHI.Physics.YangMills.BalabanClayT3WardIdentityLiteratureExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3SchurWardBetaExact as Ward

------------------------------------------------------------------------
-- Literature normalization.
--
-- J. C. Ward,
-- "An Identity in Quantum Electrodynamics",
-- Physical Review 78 (1950), 182.
-- DOI: 10.1103/PhysRev.78.182
--
-- Y. Takahashi,
-- "On the generalized Ward identity",
-- Il Nuovo Cimento 6 (1957), 371--375.
-- DOI: 10.1007/BF02832514
--
-- The present lattice statement is not obtained by importing a perturbative
-- continuum identity.  It is produced from exact reindexing of the constrained
-- gauge-invariant integral, and localization is required to be equivariant.
-- These classic references fix the terminology and the continuum normalization;
-- the Agda theorem remains the exact finite-lattice argument below.
------------------------------------------------------------------------

fluctuationIntegralWardIdentityFromReindexing :
  ∀ {Gauge Fine Coarse Weight Scalar}
    (dataSet : Ward.ExactGaugeReindexedIntegral
      Gauge Fine Coarse Weight Scalar)
    gauge coarse →
  Ward.constrainedIntegral dataSet (Ward.boltzmannWeight dataSet)
    (Ward.transformCoarse dataSet gauge coarse)
  ≡ Ward.constrainedIntegral dataSet (Ward.boltzmannWeight dataSet) coarse
fluctuationIntegralWardIdentityFromReindexing =
  Ward.fluctuationIntegralGaugeInvariant

localizedWardIdentityFromEquivariance :
  ∀ {Gauge EffectiveAction LocalTerm}
    (dataSet : Ward.WardPreservingLocalization
      Gauge EffectiveAction LocalTerm)
    gauge action →
  Ward.localize dataSet (Ward.transformAction dataSet gauge action)
  ≡ Ward.transformLocal dataSet gauge (Ward.localize dataSet action)
localizedWardIdentityFromEquivariance =
  Ward.localizationPreservesWardIdentity

wardReindexingLiteratureNormalizationLevel : ProofLevel
wardReindexingLiteratureNormalizationLevel = machineChecked

wardLocalizationEquivarianceLevel : ProofLevel
wardLocalizationEquivarianceLevel = machineChecked

-- The physical leaf remains the proof that the literal Haar conditional measure,
-- block map and localization operator instantiate these exact reindexing and
-- equivariance hypotheses at every scale.
physicalWardReindexingInstantiationLevel : ProofLevel
physicalWardReindexingInstantiationLevel = conditional
