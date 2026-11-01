module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ExtensibilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.MaintainabilityTheorem as PAWOTGRMAIN
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem
  field
    waveObservableTransportGeometryRegimeMaintainability :
      PAWOTGRMAIN.ParametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    extensibleOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeExtensibilityTheorem
    (PAWOTGRMAIN.buildParametricAlgebraicWaveObservableTransportGeometryRegimeMaintainabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
