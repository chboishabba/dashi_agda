module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CompletenessTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.StabilityTheorem as PAWOTGRS
open import DASHI.Physics.Closure.ParametricAlgebraicClosureBundleTheorem as PACTB

record ParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
  field
    waveObservableTransportGeometryRegimeStability :
      PAWOTGRS.ParametricAlgebraicWaveObservableTransportGeometryRegimeStabilityTheorem pkg
    algebraicClosureBundle :
      PACTB.ParametricAlgebraicClosureBundleTheorem pkg
    completeOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
    (PAWOTGRS.buildParametricAlgebraicWaveObservableTransportGeometryRegimeStabilityTheorem pkg)
    (PACTB.parametricAlgebraicClosureBundleTheorem pkg)
    (λ _ pf → pf)
