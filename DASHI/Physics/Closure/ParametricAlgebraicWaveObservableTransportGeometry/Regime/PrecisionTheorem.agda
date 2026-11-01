module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.PrecisionTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RefinementTheorem as PAWOTGRREF
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem
  field
    waveObservableTransportGeometryRegimeRefinement :
      PAWOTGRREF.ParametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    preciseOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimePrecisionTheorem
    (PAWOTGRREF.buildParametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
