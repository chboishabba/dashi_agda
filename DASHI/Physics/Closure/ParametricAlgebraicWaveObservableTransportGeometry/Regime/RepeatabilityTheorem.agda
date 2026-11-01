module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RepeatabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ReliabilityTheorem as PAWOTGRREL
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem
  field
    waveObservableTransportGeometryRegimeReliability :
      PAWOTGRREL.ParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    repeatableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeRepeatabilityTheorem
    (PAWOTGRREL.buildParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
