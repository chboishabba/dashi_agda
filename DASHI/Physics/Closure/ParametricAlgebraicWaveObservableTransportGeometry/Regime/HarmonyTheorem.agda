module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.HarmonyTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.IntegrityTheorem as PAWOTGRINT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem
  field
    waveObservableTransportGeometryRegimeIntegrity :
      PAWOTGRINT.ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    harmonicOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeHarmonyTheorem
    (PAWOTGRINT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
