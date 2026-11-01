module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.LegibilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.FidelityTheorem as PAWOTGRFID
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeLegibilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeLegibilityTheorem
  field
    waveObservableTransportGeometryRegimeFidelity :
      PAWOTGRFID.ParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    legibleOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeLegibilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeLegibilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeLegibilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeLegibilityTheorem
    (PAWOTGRFID.buildParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
