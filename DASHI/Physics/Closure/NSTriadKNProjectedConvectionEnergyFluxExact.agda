module DASHI.Physics.Closure.NSTriadKNProjectedConvectionEnergyFluxExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Venue/year: Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Venue/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Isolate the exact energy-flux algebra used before Luo's small-time
-- bootstrap.  A physical proof must show that the periodic high-pass is an
-- orthogonal self-adjoint Fourier projector, pressure pairs to zero against a
-- divergence-free projected velocity, and the projected convection pairing
-- equals the enumerated cutoff flux.  Once those identities are supplied,
-- the high-frequency energy inequality and the weighted-Schur flux bound
-- compose without further PDE assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact
  as Flux

------------------------------------------------------------------------
-- Projected energy balance with explicit pressure cancellation.
------------------------------------------------------------------------

record ProjectedCutoffEnergyBalance : Set where
  constructor energy-balance
  field
    energyDerivative : ℚ
    viscousDissipation : ℚ
    pressurePairing : ℚ
    absoluteCutoffFlux : ℚ

    dissipationNonnegative : 0ℚ ≤ viscousDissipation
    absoluteFluxNonnegative : 0ℚ ≤ absoluteCutoffFlux

    projectedEnergyInequalityWithPressure :
      energyDerivative + viscousDissipation
        ≤ pressurePairing + absoluteCutoffFlux

    divergenceFreePressureCancellation :
      pressurePairing ≡ 0ℚ

open ProjectedCutoffEnergyBalance public

highFrequencyEnergyInequality :
  (balance : ProjectedCutoffEnergyBalance) →
  energyDerivative balance + viscousDissipation balance
    ≤ absoluteCutoffFlux balance
highFrequencyEnergyInequality balance =
  subst
    (λ right →
      energyDerivative balance + viscousDissipation balance ≤ right)
    (ℚₚ.+-identityˡ (absoluteCutoffFlux balance))
    (subst
      (λ pressure →
        energyDerivative balance + viscousDissipation balance
          ≤ pressure + absoluteCutoffFlux balance)
      (divergenceFreePressureCancellation balance)
      (projectedEnergyInequalityWithPressure balance))

------------------------------------------------------------------------
-- Source-faithful physical adapter.
------------------------------------------------------------------------

record PeriodicProjectedConvectionFluxAdapter : Set₁ where
  constructor projected-flux-adapter
  field
    balance : ProjectedCutoffEnergyBalance
    weightedFluxBridge : Flux.PhysicalCutoffFluxWeightedSchurBridge

    hardHighPassProjectorIdempotent : Set
    hardHighPassProjectorSelfAdjoint : Set
    hardHighPassCommutesWithDerivative : Set
    periodicVelocityDivergenceFree : Set
    pressurePairingIsLiteralPeriodicPairing : Set
    projectedConvectionTriadsExactlyEnumerated : Set
    incidenceMultiplicityMatchesConvolution : Set

    energyFluxQuantityAgreement :
      absoluteCutoffFlux balance
        ≡ Flux.absoluteCutoffFlux weightedFluxBridge

open PeriodicProjectedConvectionFluxAdapter public

projectedEnergyControlledByWeightedSchurFlux :
  (adapter : PeriodicProjectedConvectionFluxAdapter) →
  energyDerivative (balance adapter)
    + viscousDissipation (balance adapter)
    ≤ Flux.profileSchurConstant (weightedFluxBridge adapter)
      * (Flux.cutoffEnergyMajorant (weightedFluxBridge adapter)
        * Flux.lowPassGradientInfinity (weightedFluxBridge adapter))
projectedEnergyControlledByWeightedSchurFlux adapter =
  ℚₚ.≤-trans
    (highFrequencyEnergyInequality (balance adapter))
    (subst
      (λ flux →
        flux
          ≤ Flux.profileSchurConstant (weightedFluxBridge adapter)
            * (Flux.cutoffEnergyMajorant (weightedFluxBridge adapter)
              * Flux.lowPassGradientInfinity (weightedFluxBridge adapter)))
      (sym (energyFluxQuantityAgreement adapter))
      (Flux.luoCutoffFluxEstimate (weightedFluxBridge adapter)))

projectedEnergyFluxAlgebraConstructed : Bool
projectedEnergyFluxAlgebraConstructed = true

pressureCancellationTransportConstructed : Bool
pressureCancellationTransportConstructed = true

weightedSchurFluxEnergyCompositionConstructed : Bool
weightedSchurFluxEnergyCompositionConstructed = true

periodicHardHighPassSelfAdjointnessClosed : Bool
periodicHardHighPassSelfAdjointnessClosed = false

literalProjectedConvectionEnumerationClosed : Bool
literalProjectedConvectionEnumerationClosed = false

periodicProjectedConvectionFluxAdapterInhabited : Bool
periodicProjectedConvectionFluxAdapterInhabited = false

projectedEnergyFluxAlgebraConstructedIsTrue :
  projectedEnergyFluxAlgebraConstructed ≡ true
projectedEnergyFluxAlgebraConstructedIsTrue = refl

pressureCancellationTransportConstructedIsTrue :
  pressureCancellationTransportConstructed ≡ true
pressureCancellationTransportConstructedIsTrue = refl

weightedSchurFluxEnergyCompositionConstructedIsTrue :
  weightedSchurFluxEnergyCompositionConstructed ≡ true
weightedSchurFluxEnergyCompositionConstructedIsTrue = refl

periodicHardHighPassSelfAdjointnessClosedIsFalse :
  periodicHardHighPassSelfAdjointnessClosed ≡ false
periodicHardHighPassSelfAdjointnessClosedIsFalse = refl

literalProjectedConvectionEnumerationClosedIsFalse :
  literalProjectedConvectionEnumerationClosed ≡ false
literalProjectedConvectionEnumerationClosedIsFalse = refl

periodicProjectedConvectionFluxAdapterInhabitedIsFalse :
  periodicProjectedConvectionFluxAdapterInhabited ≡ false
periodicProjectedConvectionFluxAdapterInhabitedIsFalse = refl
