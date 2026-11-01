module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.UsabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ReliabilityTheorem as PAWOTGRREL
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem
  field
    waveObservableTransportGeometryRegimeReliability :
      PAWOTGRREL.ParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    usableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem
    (PAWOTGRREL.buildParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
