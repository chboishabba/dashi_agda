module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ReproducibilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RepeatabilityTheorem as PAWOTGRREP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem
  field
    waveObservableTransportGeometryRegimeRepeatability :
      PAWOTGRREP.ParametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    reproducibleOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeReproducibilityTheorem
    (PAWOTGRREP.buildParametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
