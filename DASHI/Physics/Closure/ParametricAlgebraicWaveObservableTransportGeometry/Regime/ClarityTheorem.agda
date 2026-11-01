module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ClarityTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.TransparencyTheorem as PAWOTGRTRN
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeClarityTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeClarityTheorem
  field
    waveObservableTransportGeometryRegimeTransparency :
      PAWOTGRTRN.ParametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    clearOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeClarityTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeClarityTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeClarityTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeClarityTheorem
    (PAWOTGRTRN.buildParametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
