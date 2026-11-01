module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ReliabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.VerifiabilityTheorem as PAWOTGRVT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem
  field
    waveObservableTransportGeometryRegimeVerifiability :
      PAWOTGRVT.ParametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    reliableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeReliabilityTheorem
    (PAWOTGRVT.buildParametricAlgebraicWaveObservableTransportGeometryRegimeVerifiabilityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
