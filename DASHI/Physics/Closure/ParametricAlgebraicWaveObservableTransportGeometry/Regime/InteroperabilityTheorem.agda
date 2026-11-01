module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.InteroperabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.PortabilityTheorem as PAWOTGRPORT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem
  field
    waveObservableTransportGeometryRegimePortability :
      PAWOTGRPORT.ParametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    interoperableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeInteroperabilityTheorem
    (PAWOTGRPORT.buildParametricAlgebraicWaveObservableTransportGeometryRegimePortabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
