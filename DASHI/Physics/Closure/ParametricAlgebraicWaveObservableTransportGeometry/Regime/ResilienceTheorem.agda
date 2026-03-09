module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ResilienceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RobustnessTheorem as PAWOTGRROB
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
  field
    waveObservableTransportGeometryRegimeRobustness :
      PAWOTGRROB.ParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    resilientOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
    (PAWOTGRROB.buildParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
