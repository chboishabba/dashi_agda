module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.IntegrityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ResilienceTheorem as PAWOTGRRES
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
  field
    waveObservableTransportGeometryRegimeResilience :
      PAWOTGRRES.ParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    integralOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
    (PAWOTGRRES.buildParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
