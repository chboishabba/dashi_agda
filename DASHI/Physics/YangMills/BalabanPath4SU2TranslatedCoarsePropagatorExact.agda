module DASHI.Physics.YangMills.BalabanPath4SU2TranslatedCoarsePropagatorExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (periodicTorus4Definition)
open import DASHI.Physics.YangMills.BalabanConfiguredSideTranslatedBlockExact
  using
    ( TranslatedPhysicalSU2Tangent4
    ; translatedTangentToLocal
    ; localTangentToTranslated
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
  using
    ( CoarseSU2Bond4
    ; literalBlockAverageQ
    ; literalBlockAverageAdjointQStar
    ; concreteGaugeFixedHessianData
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact
  using
    ( ConfiguredPropagatorAuthority
    ; configuredGaugeFixedMatrix
    ; configuredPropagator
    )
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessian
  using (gaugeFixedHessian)
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
  using (hessianData)

translatedBlockAverage :
  ∀ {latticeSide : Nat}
    {origin : periodicTorus4Definition latticeSide} →
  TranslatedPhysicalSU2Tangent4 origin → CoarseSU2Bond4
translatedBlockAverage tangent =
  literalBlockAverageQ (translatedTangentToLocal tangent)

translatedBlockAdjoint :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide) →
  CoarseSU2Bond4 → TranslatedPhysicalSU2Tangent4 origin
translatedBlockAdjoint origin coarse =
  localTangentToTranslated origin (literalBlockAverageAdjointQStar coarse)

translatedGaugeFixedOperator :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide) →
  TranslatedPhysicalSU2Tangent4 origin →
  TranslatedPhysicalSU2Tangent4 origin
translatedGaugeFixedOperator origin tangent =
  localTangentToTranslated origin
    (configuredGaugeFixedMatrix (translatedTangentToLocal tangent))

translatedPropagator :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide) →
  ConfiguredPropagatorAuthority →
  TranslatedPhysicalSU2Tangent4 origin →
  TranslatedPhysicalSU2Tangent4 origin
translatedPropagator origin authority source =
  localTangentToTranslated origin
    (configuredPropagator authority (translatedTangentToLocal source))

translatedBlockAverageCommutes :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide) tangent →
  translatedBlockAverage (localTangentToTranslated origin tangent)
  ≡ literalBlockAverageQ tangent
translatedBlockAverageCommutes origin tangent = refl

translatedBlockAdjointCommutes :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide) coarse →
  translatedTangentToLocal (translatedBlockAdjoint origin coarse)
  ≡ literalBlockAverageAdjointQStar coarse
translatedBlockAdjointCommutes origin coarse = refl

translatedGaugeFixedOperatorCommutes :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide) tangent →
  translatedTangentToLocal
    (translatedGaugeFixedOperator origin
      (localTangentToTranslated origin tangent))
  ≡ configuredGaugeFixedMatrix tangent
translatedGaugeFixedOperatorCommutes origin tangent = refl

translatedPropagatorCommutes :
  ∀ {latticeSide : Nat}
    (origin : periodicTorus4Definition latticeSide)
    (authority : ConfiguredPropagatorAuthority) source →
  translatedTangentToLocal
    (translatedPropagator origin authority
      (localTangentToTranslated origin source))
  ≡ configuredPropagator authority source
translatedPropagatorCommutes origin authority source = refl

translatedCoarseAverageCompatibilityLevel : ProofLevel
translatedCoarseAverageCompatibilityLevel = machineChecked

translatedGaugeFixedOperatorCompatibilityLevel : ProofLevel
translatedGaugeFixedOperatorCompatibilityLevel = machineChecked

translatedPropagatorCompatibilityLevel : ProofLevel
translatedPropagatorCompatibilityLevel = machineChecked
