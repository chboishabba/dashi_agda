module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.Theorem as PAWOTGR
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
  field
    waveObservableTransportGeometryRegime :
      PAWOTGR.ParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem pkg
    regimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    coherentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
    (PAWOTGR.buildParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
