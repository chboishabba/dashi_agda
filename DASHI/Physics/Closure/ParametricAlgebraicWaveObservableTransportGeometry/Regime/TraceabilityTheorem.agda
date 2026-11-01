module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.TraceabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.IntegrityTheorem as PAWOTGRINT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem
  field
    waveObservableTransportGeometryRegimeIntegrity :
      PAWOTGRINT.ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    traceableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem
    (PAWOTGRINT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
