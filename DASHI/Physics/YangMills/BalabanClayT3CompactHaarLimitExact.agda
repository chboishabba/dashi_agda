module DASHI.Physics.YangMills.BalabanClayT3CompactHaarLimitExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- T3: exact passage from finite quadrature to the constrained compact-Haar
-- transformation.
--
-- The Haar integral is definitionally the limit of a refinement sequence.  The
-- small/large partition and gauge invariance are transported through the limit
-- by its algebraic laws; neither is installed on the limiting action by hand.
------------------------------------------------------------------------

record CompactHaarQuadratureLimit
    (Gauge Coarse Scalar EffectiveAction : Set) : Set₁ where
  field
    transformCoarse : Gauge → Coarse → Coarse

    add multiply : Scalar → Scalar → Scalar
    vacuumNormalization : Scalar

    finiteIntegral finiteSmall finiteLarge : Nat → Coarse → Scalar

    finitePartitionExact : ∀ refinement coarse →
      finiteIntegral refinement coarse
      ≡ add (finiteSmall refinement coarse) (finiteLarge refinement coarse)

    finiteGaugeInvariant : ∀ refinement gauge coarse →
      finiteIntegral refinement (transformCoarse gauge coarse)
      ≡ finiteIntegral refinement coarse

    limit : (Nat → Scalar) → Scalar
    limitCongruent : ∀ left right →
      (∀ refinement → left refinement ≡ right refinement) →
      limit left ≡ limit right
    limitAdditive : ∀ left right →
      limit (λ refinement → add (left refinement) (right refinement))
      ≡ add (limit left) (limit right)

    negativeLog : Scalar → EffectiveAction
    exponentialOfNegativeAction : EffectiveAction → Scalar
    exponentialNegativeLog : ∀ scalar →
      exponentialOfNegativeAction (negativeLog scalar) ≡ scalar

open CompactHaarQuadratureLimit public

constrainedHaarIntegral :
  ∀ {Gauge Coarse Scalar EffectiveAction} →
  CompactHaarQuadratureLimit Gauge Coarse Scalar EffectiveAction →
  Coarse → Scalar
constrainedHaarIntegral dataSet coarse =
  limit dataSet (λ refinement → finiteIntegral dataSet refinement coarse)

smallHaarContribution :
  ∀ {Gauge Coarse Scalar EffectiveAction} →
  CompactHaarQuadratureLimit Gauge Coarse Scalar EffectiveAction →
  Coarse → Scalar
smallHaarContribution dataSet coarse =
  limit dataSet (λ refinement → finiteSmall dataSet refinement coarse)

largeHaarContribution :
  ∀ {Gauge Coarse Scalar EffectiveAction} →
  CompactHaarQuadratureLimit Gauge Coarse Scalar EffectiveAction →
  Coarse → Scalar
largeHaarContribution dataSet coarse =
  limit dataSet (λ refinement → finiteLarge dataSet refinement coarse)

smallLargeHaarPartitionExact :
  ∀ {Gauge Coarse Scalar EffectiveAction}
    (dataSet : CompactHaarQuadratureLimit
      Gauge Coarse Scalar EffectiveAction)
    coarse →
  constrainedHaarIntegral dataSet coarse
  ≡ add dataSet
      (smallHaarContribution dataSet coarse)
      (largeHaarContribution dataSet coarse)
smallLargeHaarPartitionExact dataSet coarse =
  trans
    (limitCongruent dataSet
      (λ refinement → finiteIntegral dataSet refinement coarse)
      (λ refinement → add dataSet
        (finiteSmall dataSet refinement coarse)
        (finiteLarge dataSet refinement coarse))
      (λ refinement → finitePartitionExact dataSet refinement coarse))
    (limitAdditive dataSet
      (λ refinement → finiteSmall dataSet refinement coarse)
      (λ refinement → finiteLarge dataSet refinement coarse))

constrainedHaarGaugeInvariant :
  ∀ {Gauge Coarse Scalar EffectiveAction}
    (dataSet : CompactHaarQuadratureLimit
      Gauge Coarse Scalar EffectiveAction)
    gauge coarse →
  constrainedHaarIntegral dataSet (transformCoarse dataSet gauge coarse)
  ≡ constrainedHaarIntegral dataSet coarse
constrainedHaarGaugeInvariant dataSet gauge coarse =
  limitCongruent dataSet
    (λ refinement → finiteIntegral dataSet refinement
      (transformCoarse dataSet gauge coarse))
    (λ refinement → finiteIntegral dataSet refinement coarse)
    (λ refinement → finiteGaugeInvariant dataSet refinement gauge coarse)

haarEffectiveAction :
  ∀ {Gauge Coarse Scalar EffectiveAction} →
  CompactHaarQuadratureLimit Gauge Coarse Scalar EffectiveAction →
  Coarse → EffectiveAction
haarEffectiveAction dataSet coarse =
  negativeLog dataSet
    (multiply dataSet (vacuumNormalization dataSet)
      (constrainedHaarIntegral dataSet coarse))

haarEffectiveActionDefinesIntegral :
  ∀ {Gauge Coarse Scalar EffectiveAction}
    (dataSet : CompactHaarQuadratureLimit
      Gauge Coarse Scalar EffectiveAction)
    coarse →
  exponentialOfNegativeAction dataSet (haarEffectiveAction dataSet coarse)
  ≡ multiply dataSet (vacuumNormalization dataSet)
      (constrainedHaarIntegral dataSet coarse)
haarEffectiveActionDefinesIntegral dataSet coarse =
  exponentialNegativeLog dataSet _

compactHaarLimitConstructionLevel : ProofLevel
compactHaarLimitConstructionLevel = machineChecked

compactHaarSmallLargePartitionLevel : ProofLevel
compactHaarSmallLargePartitionLevel = machineChecked

compactHaarGaugeInvarianceLevel : ProofLevel
compactHaarGaugeInvarianceLevel = machineChecked

-- The remaining analytic input is the actual equidistributed product-SU(N)
-- quadrature theorem, including domination uniform in volume, scale and coarse
-- field, so that this limit is identified with product Haar disintegration.
productHaarQuadratureIdentificationLevel : ProofLevel
productHaarQuadratureIdentificationLevel = conditional
