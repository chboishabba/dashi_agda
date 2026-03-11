module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AccountabilityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.StewardshipTheorem as PAWOTGRSTEW
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeAccountabilityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeAccountabilityTheorem
  field
    waveObservableTransportGeometryRegimeStewardship :
      PAWOTGRSTEW.ParametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    accountableOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeAccountabilityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeAccountabilityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeAccountabilityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeAccountabilityTheorem
    (PAWOTGRSTEW.buildParametricAlgebraicWaveObservableTransportGeometryRegimeStewardshipTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)

