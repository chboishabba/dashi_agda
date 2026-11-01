module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.Theorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem as PAWOTGC
open import DASHI.Physics.Closure.ParametricAlgebraicRegimePersistenceTheorem as PARP

record ParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
  field
    waveObservableTransportGeometryCoherence :
      PAWOTGC.ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem pkg
    regimePersistence : PARP.ParametricAlgebraicRegimePersistenceTheorem pkg
    stableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
    (PAWOTGC.buildParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem pkg)
    (PARP.parametricAlgebraicRegimePersistenceTheorem pkg)
    (λ _ pf → pf)
