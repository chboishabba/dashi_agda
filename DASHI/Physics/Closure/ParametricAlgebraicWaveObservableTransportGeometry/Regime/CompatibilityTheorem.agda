module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CompatibilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ContinuityTheorem as PAWOTGRCONT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem
  field
    waveObservableTransportGeometryRegimeContinuity :
      PAWOTGRCONT.ParametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    compatibleOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem
    (PAWOTGRCONT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
