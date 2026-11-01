module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ContinuityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SymmetryTheorem as PAWOTGRSYM
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem
  field
    waveObservableTransportGeometryRegimeSymmetry :
      PAWOTGRSYM.ParametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    continuousOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeContinuityTheorem
    (PAWOTGRSYM.buildParametricAlgebraicWaveObservableTransportGeometryRegimeSymmetryTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
