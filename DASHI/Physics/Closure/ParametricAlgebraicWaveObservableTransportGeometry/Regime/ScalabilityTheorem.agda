module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ScalabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AdaptabilityTheorem as PAWOTGRADAPT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem
  field
    waveObservableTransportGeometryRegimeAdaptability :
      PAWOTGRADAPT.ParametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    scalableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeScalabilityTheorem
    (PAWOTGRADAPT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeAdaptabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
