module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SymmetryTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.BalanceTheorem as PAWOTGRBAL
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem
  field
    waveObservableTransportGeometryRegimeBalance :
      PAWOTGRBAL.ParametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    symmetricOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem
    (PAWOTGRBAL.buildParametricAlgebraicWaveObservableTransportGeometryRegimeBalanceTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
