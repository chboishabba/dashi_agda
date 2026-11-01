module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ManageabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.OperabilityTheorem as PAWOTGROPER
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeManageabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeManageabilityTheorem
  field
    waveObservableTransportGeometryRegimeOperability :
      PAWOTGROPER.ParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    manageableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeManageabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeManageabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeManageabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeManageabilityTheorem
    (PAWOTGROPER.buildParametricAlgebraicWaveObservableTransportGeometryRegimeOperabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
