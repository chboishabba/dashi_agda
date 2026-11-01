module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CalibrationTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ResolutionTheorem as PAWOTGRRSL
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem
  field
    waveObservableTransportGeometryRegimeResolution :
      PAWOTGRRSL.ParametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    calibratedOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeCalibrationTheorem
    (PAWOTGRRSL.buildParametricAlgebraicWaveObservableTransportGeometryRegimeResolutionTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
