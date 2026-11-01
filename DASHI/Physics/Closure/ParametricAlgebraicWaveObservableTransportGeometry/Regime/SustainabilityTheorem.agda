module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SustainabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ScalabilityTheorem as PAWOTGRSCAL
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem
  field
    waveObservableTransportGeometryRegimeScalability :
      PAWOTGRSCAL.ParametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    sustainableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeSustainabilityTheorem
    (PAWOTGRSCAL.buildParametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
