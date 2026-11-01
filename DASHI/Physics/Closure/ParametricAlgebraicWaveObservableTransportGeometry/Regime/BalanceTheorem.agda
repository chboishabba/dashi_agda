module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.BalanceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.HarmonyTheorem as PAWOTGRHAR
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem
  field
    waveObservableTransportGeometryRegimeHarmony :
      PAWOTGRHAR.ParametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    balancedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem
    (PAWOTGRHAR.buildParametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
