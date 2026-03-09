module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ConcordanceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CompatibilityTheorem as PAWOTGRCOMP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem
  field
    waveObservableTransportGeometryRegimeCompatibility :
      PAWOTGRCOMP.ParametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    concordantOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeConcordanceTheorem
    (PAWOTGRCOMP.buildParametricAlgebraicWaveObservableTransportGeometryRegimeCompatibilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
