module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.FusionTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SynthesisTheorem as PAWOTGRSYN
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeFusionTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeFusionTheorem
  field
    waveObservableTransportGeometryRegimeSynthesis :
      PAWOTGRSYN.ParametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    fusedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeFusionTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeFusionTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeFusionTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeFusionTheorem
    (PAWOTGRSYN.buildParametricAlgebraicWaveObservableTransportGeometryRegimeSynthesisTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
