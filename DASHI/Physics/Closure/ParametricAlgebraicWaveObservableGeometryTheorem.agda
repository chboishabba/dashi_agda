module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableGeometryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportTheorem as PAWOT
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableGeometryTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableGeometryTheorem
  field
    waveObservableTransport :
      PAWOT.ParametricAlgebraicWaveObservableTransportTheorem pkg
    regimeCoherence : PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    waveObservableGeometryStable :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableGeometryTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableGeometryTheorem pkg
buildParametricAlgebraicWaveObservableGeometryTheorem pkg =
  parametricAlgebraicWaveObservableGeometryTheorem
    (PAWOT.buildParametricAlgebraicWaveObservableTransportTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
