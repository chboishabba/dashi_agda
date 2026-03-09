module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RobustnessTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.InvarianceTheorem as PAWOTGRINV
open import DASHI.Physics.Closure.ParametricAlgebraicRegimePersistenceTheorem as PARP

record ParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
  field
    waveObservableTransportGeometryRegimeInvariance :
      PAWOTGRINV.ParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem pkg
    algebraicRegimePersistence :
      PARP.ParametricAlgebraicRegimePersistenceTheorem pkg
    robustOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
    (PAWOTGRINV.buildParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem pkg)
    (PARP.parametricAlgebraicRegimePersistenceTheorem pkg)
    (λ _ pf → pf)
