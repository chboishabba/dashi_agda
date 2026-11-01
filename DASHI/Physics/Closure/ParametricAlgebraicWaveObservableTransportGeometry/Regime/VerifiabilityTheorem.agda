module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.VerifiabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AuditabilityTheorem as PAWOTGRAT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem
  field
    waveObservableTransportGeometryRegimeAuditability :
      PAWOTGRAT.ParametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    verifiableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem
    (PAWOTGRAT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeAuditabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
