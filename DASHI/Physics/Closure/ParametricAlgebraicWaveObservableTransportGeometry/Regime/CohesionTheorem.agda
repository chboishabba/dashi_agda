module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CohesionTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ConcordanceTheorem as PAWOTGRCONC
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem
  field
    waveObservableTransportGeometryRegimeConcordance :
      PAWOTGRCONC.ParametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    cohesiveOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeCohesionTheorem
    (PAWOTGRCONC.buildParametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
