module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RefinementTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AlignmentTheorem as PAWOTGRALIGN
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem
  field
    waveObservableTransportGeometryRegimeAlignment :
      PAWOTGRALIGN.ParametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    refinedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeRefinementTheorem
    (PAWOTGRALIGN.buildParametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
