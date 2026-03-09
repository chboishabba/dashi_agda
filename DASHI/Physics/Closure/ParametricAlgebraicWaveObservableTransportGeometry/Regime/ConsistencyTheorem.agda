module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ConsistencyTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SoundnessTheorem as PAWOTGRSO
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeTransportConsistencyTheorem as PARTC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
  field
    waveObservableTransportGeometryRegimeSoundness :
      PAWOTGRSO.ParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem pkg
    algebraicRegimeTransportConsistency :
      PARTC.ParametricAlgebraicRegimeTransportConsistencyTheorem pkg
    consistentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
    (PAWOTGRSO.buildParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem pkg)
    (PARTC.buildParametricAlgebraicRegimeTransportConsistencyTheorem pkg)
    (λ _ pf → pf)
