module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.OperabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.UsabilityTheorem as PAWOTGRUSA
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem
  field
    waveObservableTransportGeometryRegimeUsability :
      PAWOTGRUSA.ParametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    operableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem
    (PAWOTGRUSA.buildParametricAlgebraicWaveObservableTransportGeometryRegimeUsabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
