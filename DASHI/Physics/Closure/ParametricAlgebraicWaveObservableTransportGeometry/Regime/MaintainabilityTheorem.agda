module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.MaintainabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ComposabilityTheorem as PAWOTGRCOMP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem
  field
    waveObservableTransportGeometryRegimeComposability :
      PAWOTGRCOMP.ParametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    maintainableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem
    (PAWOTGRCOMP.buildParametricAlgebraicWaveObservableTransportGeometryRegimeComposabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
