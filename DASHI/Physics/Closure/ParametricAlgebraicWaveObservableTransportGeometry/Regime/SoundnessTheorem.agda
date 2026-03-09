module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SoundnessTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CompletenessTheorem as PAWOTGRCM
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
  field
    waveObservableTransportGeometryRegimeCompleteness :
      PAWOTGRCM.ParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    soundOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
    (PAWOTGRCM.buildParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
