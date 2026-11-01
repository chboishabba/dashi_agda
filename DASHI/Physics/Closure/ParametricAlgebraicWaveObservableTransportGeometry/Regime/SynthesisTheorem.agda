module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SynthesisTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.IntegrationTheorem as PAWOTGRINTG
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem
  field
    waveObservableTransportGeometryRegimeIntegration :
      PAWOTGRINTG.ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrationTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    synthesizedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem
    (PAWOTGRINTG.buildParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrationTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
