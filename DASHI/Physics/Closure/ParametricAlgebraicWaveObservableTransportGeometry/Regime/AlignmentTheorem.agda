module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.AlignmentTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.EquilibriumTheorem as PAWOTGREQ
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem
  field
    waveObservableTransportGeometryRegimeEquilibrium :
      PAWOTGREQ.ParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    alignmentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeAlignmentTheorem
    (PAWOTGREQ.buildParametricAlgebraicWaveObservableTransportGeometryRegimeEquilibriumTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
