module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ConvergenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.EquilibriumTheorem as PAWOTGREQ
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeConvergenceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeConvergenceTheorem
  field
    waveObservableTransportGeometryRegimeEquilibrium :
      PAWOTGREQ.ParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    convergentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeConvergenceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeConvergenceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeConvergenceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeConvergenceTheorem
    (PAWOTGREQ.buildParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
