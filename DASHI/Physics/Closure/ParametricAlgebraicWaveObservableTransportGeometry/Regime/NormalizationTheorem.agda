module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.NormalizationTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CalibrationTheorem as PAWOTGRCAL
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeNormalizationTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeNormalizationTheorem
  field
    waveObservableTransportGeometryRegimeCalibration :
      PAWOTGRCAL.ParametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    normalizedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeNormalizationTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeNormalizationTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeNormalizationTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeNormalizationTheorem
    (PAWOTGRCAL.buildParametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
