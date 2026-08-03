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
-- bootstrap.  The hard high-pass is now known to be idempotent and Hermitian
-- self-adjoint under the repository's coefficient-unitary Parseval convention,
-- and its hard high-output triad selector is exact.  The remaining physical
-- adapter must identify pressure cancellation, signed coefficients, incidence
-- multiplicity and the literal energy/flux quantities on one common carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact
  as Flux
import DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact
  as Orthogonal
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalEnumerationReuseExact
  as PhysicalReuse

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

record PeriodicProjectedConvectionFluxAdapter : Set₁ where
  constructor projected-flux-adapter
  field
    balance : ProjectedCutoffEnergyBalance
    weightedFluxBridge : Flux.PhysicalCutoffFluxWeightedSchurBridge

    HardHighPassProjectorIdempotent : Set
    hardHighPassProjectorIdempotent : HardHighPassProjectorIdempotent

    HardHighPassProjectorSelfAdjoint : Set
    hardHighPassProjectorSelfAdjoint : HardHighPassProjectorSelfAdjoint

    HardHighPassCommutesWithDerivative : Set
    hardHighPassCommutesWithDerivative : HardHighPassCommutesWithDerivative

    PeriodicVelocityDivergenceFree : Set
    periodicVelocityDivergenceFree : PeriodicVelocityDivergenceFree

    PressurePairingIsLiteralPeriodicPairing : Set
    pressurePairingIsLiteralPeriodicPairing :
      PressurePairingIsLiteralPeriodicPairing

    ProjectedConvectionTriadsExactlyEnumerated : Set
    projectedConvectionTriadsExactlyEnumerated :
      ProjectedConvectionTriadsExactlyEnumerated

    IncidenceMultiplicityMatchesConvolution : Set
    incidenceMultiplicityMatchesConvolution :
      IncidenceMultiplicityMatchesConvolution

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
periodicHardHighPassSelfAdjointnessClosed =
  Orthogonal.hardProjectorOrthogonalCertificateConstructed

literalProjectedConvectionEnumerationClosed : Bool
literalProjectedConvectionEnumerationClosed =
  PhysicalReuse.hardProjectedHighFrequencySelectionConstructed

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

periodicHardHighPassSelfAdjointnessClosedIsTrue :
  periodicHardHighPassSelfAdjointnessClosed ≡ true
periodicHardHighPassSelfAdjointnessClosedIsTrue =
  Orthogonal.hardProjectorOrthogonalCertificateConstructedIsTrue

literalProjectedConvectionEnumerationClosedIsTrue :
  literalProjectedConvectionEnumerationClosed ≡ true
literalProjectedConvectionEnumerationClosedIsTrue =
  PhysicalReuse.hardProjectedHighFrequencySelectionConstructedIsTrue

periodicProjectedConvectionFluxAdapterInhabitedIsFalse :
  periodicProjectedConvectionFluxAdapterInhabited ≡ false
periodicProjectedConvectionFluxAdapterInhabitedIsFalse = refl
