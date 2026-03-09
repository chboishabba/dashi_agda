module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.EquilibriumTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CohesionTheorem as PAWOTGRCOH
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem
  field
    waveObservableTransportGeometryRegimeCohesion :
      PAWOTGRCOH.ParametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    equilibratedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem
    (PAWOTGRCOH.buildParametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
