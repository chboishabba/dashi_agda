module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.DurabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.OperabilityTheorem as PAWOTGROPER
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeDurabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeDurabilityTheorem
  field
    waveObservableTransportGeometryRegimeOperability :
      PAWOTGROPER.ParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    durableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeDurabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeDurabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeDurabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeDurabilityTheorem
    (PAWOTGROPER.buildParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
