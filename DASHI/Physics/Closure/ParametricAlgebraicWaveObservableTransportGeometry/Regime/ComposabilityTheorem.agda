module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ComposabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.InteroperabilityTheorem as PAWOTGRINTER
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem
  field
    waveObservableTransportGeometryRegimeInteroperability :
      PAWOTGRINTER.ParametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    composableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem
    (PAWOTGRINTER.buildParametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
