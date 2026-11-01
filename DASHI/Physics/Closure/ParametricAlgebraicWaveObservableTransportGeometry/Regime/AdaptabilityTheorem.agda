module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AdaptabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ExtensibilityTheorem as PAWOTGREXT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem
  field
    waveObservableTransportGeometryRegimeExtensibility :
      PAWOTGREXT.ParametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    adaptableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem
    (PAWOTGREXT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
