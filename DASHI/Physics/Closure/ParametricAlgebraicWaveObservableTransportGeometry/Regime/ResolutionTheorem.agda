module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ResolutionTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.PrecisionTheorem as PAWOTGRPREC
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem
  field
    waveObservableTransportGeometryRegimePrecision :
      PAWOTGRPREC.ParametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    resolvedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem
    (PAWOTGRPREC.buildParametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
