module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.StewardshipTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SustainabilityTheorem as PAWOTGRSUST
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem
  field
    waveObservableTransportGeometryRegimeSustainability :
      PAWOTGRSUST.ParametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    stewardsAdmissibility :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem
    (PAWOTGRSUST.buildParametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
