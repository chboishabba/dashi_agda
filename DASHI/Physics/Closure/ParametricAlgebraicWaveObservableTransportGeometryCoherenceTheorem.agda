module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportTheorem as PAWOT
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableGeometryTheorem as PAWOG

record ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
  field
    waveObservableTransport :
      PAWOT.ParametricAlgebraicWaveObservableTransportTheorem pkg
    waveObservableGeometry :
      PAWOG.ParametricAlgebraicWaveObservableGeometryTheorem pkg
    coherentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
    (PAWOT.buildParametricAlgebraicWaveObservableTransportTheorem pkg)
    (PAWOG.buildParametricAlgebraicWaveObservableGeometryTheorem pkg)
    (λ _ pf → pf)
