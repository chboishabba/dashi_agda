module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AuditabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.TraceabilityTheorem as PAWOTGRTRC
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem
  field
    waveObservableTransportGeometryRegimeTraceability :
      PAWOTGRTRC.ParametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    auditableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem
    (PAWOTGRTRC.buildParametricAlgebraicWaveObservableTransportGeometryRegimeTraceabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
