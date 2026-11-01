module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC
open import DASHI.Physics.Closure.ParametricAlgebraicTransportInvarianceTheorem as PATI

record ParametricAlgebraicWaveObservableTransportTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportTheorem
  field
    regimeCoherence : PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    transportInvariance : PATI.ParametricAlgebraicTransportInvarianceTheorem pkg
    waveObservableStable :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportTheorem pkg
buildParametricAlgebraicWaveObservableTransportTheorem pkg =
  parametricAlgebraicWaveObservableTransportTheorem
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (PATI.parametricAlgebraicTransportInvarianceTheorem pkg)
    (λ _ pf → pf)
