module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.PortabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ReproducibilityTheorem as PAWOTGRREPR
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem
  field
    waveObservableTransportGeometryRegimeReproducibility :
      PAWOTGRREPR.ParametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    portableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem
    (PAWOTGRREPR.buildParametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
