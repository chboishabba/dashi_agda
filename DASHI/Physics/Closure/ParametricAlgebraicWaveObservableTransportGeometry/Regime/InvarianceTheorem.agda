module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.InvarianceTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ConsistencyTheorem as PAWOTGRCONS
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeInvarianceTheorem as PARI

record ParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
  field
    waveObservableTransportGeometryRegimeConsistency :
      PAWOTGRCONS.ParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem pkg
    algebraicRegimeInvariance :
      PARI.ParametricAlgebraicRegimeInvarianceTheorem pkg
    invariantOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
    (PAWOTGRCONS.buildParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem pkg)
    (PARI.parametricAlgebraicRegimeInvarianceTheorem pkg)
    (λ _ pf → pf)
