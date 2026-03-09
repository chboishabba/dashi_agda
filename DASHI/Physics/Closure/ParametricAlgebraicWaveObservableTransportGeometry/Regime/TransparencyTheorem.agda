module DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.TransparencyTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.FidelityTheorem as PAWOTGRFID
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC

record ParametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem
         (pkg : CCGP.CanonicalConstraintGaugePackage) : Setω where
  constructor parametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem
  field
    waveObservableTransportGeometryRegimeFidelity :
      PAWOTGRFID.ParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem pkg
    algebraicRegimeCoherence :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem pkg
    transparentOnAdmissible :
      ∀ c → CCGP.admissible pkg c ≡ true → CCGP.admissible pkg c ≡ true

buildParametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem :
  (pkg : CCGP.CanonicalConstraintGaugePackage) →
  ParametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem pkg
buildParametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem pkg =
  parametricAlgebraicWaveObservableTransportGeometryRegimeTransparencyTheorem
    (PAWOTGRFID.buildParametricAlgebraicWaveObservableTransportGeometryRegimeFidelityTheorem pkg)
    (PARC.parametricAlgebraicRegimeCoherenceTheorem pkg)
    (λ _ pf → pf)
