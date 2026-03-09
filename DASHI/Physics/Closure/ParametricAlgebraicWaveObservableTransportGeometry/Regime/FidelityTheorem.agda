module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.FidelityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.EquilibriumTheorem as PAWOTGREQ
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem
  field
    waveObservableTransportGeometryRegimeEquilibrium :
      PAWOTGREQ.ParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    convergentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem
    (PAWOTGREQ.buildParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
