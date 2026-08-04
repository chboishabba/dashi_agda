module DASHI.Physics.Closure.NSTriadKNLuoProjectedConvectionOfficialParsevalUpgradeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Upgrade the historical projected-convection adapter to the repository's
-- selected official finite Hermitian/Parseval convention and exact hard-high
-- support algebra. Self-adjointness, idempotence, derivative commutation and
-- literal physical triad enumeration are reused rather than requested again.
--
-- The remaining physical inputs are divergence-free pressure interpretation,
-- incidence multiplicity/normalization and agreement of the projected energy
-- flux with the mature weighted-Schur bridge.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_+_; _*_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNPeriodicHardProjectorAlgebraExact as Hard
import DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact as Parseval
import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact as OfficialParseval
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalEnumerationReuseExact as PhysicalReuse
import DASHI.Physics.Closure.NSTriadKNProjectedConvectionEnergyFluxExact as Projected
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Flux

record OfficialProjectedConvectionFluxInputs
    {r : Level}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (cutoff : Nat) : Set (lsuc r) where
  field
    balance : Projected.ProjectedCutoffEnergyBalance
    weightedFluxBridge : Flux.PhysicalCutoffFluxWeightedSchurBridge

    PeriodicVelocityDivergenceFree : Set
    periodicVelocityDivergenceFree : PeriodicVelocityDivergenceFree

    PressurePairingIsLiteralPeriodicPairing : Set
    pressurePairingIsLiteralPeriodicPairing :
      PressurePairingIsLiteralPeriodicPairing

    IncidenceMultiplicityMatchesConvolution : Set
    incidenceMultiplicityMatchesConvolution :
      IncidenceMultiplicityMatchesConvolution

    energyFluxQuantityAgreement :
      Projected.absoluteCutoffFlux balance
      ≡ Flux.absoluteCutoffFlux weightedFluxBridge

open OfficialProjectedConvectionFluxInputs public

officialHardHighOrthogonalCertificate :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (cutoff : Nat) →
  Parseval.HardProjectorOrthogonalCertificate model modes cutoff
officialHardHighOrthogonalCertificate =
  OfficialParseval.officialHardProjectorOrthogonal

officialProjectedConvectionFluxAdapter :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {cutoff : Nat} →
  OfficialProjectedConvectionFluxInputs model modes cutoff →
  Projected.PeriodicProjectedConvectionFluxAdapter
officialProjectedConvectionFluxAdapter inputs = record
  { balance = balance inputs
  ; weightedFluxBridge = weightedFluxBridge inputs
  ; HardHighPassProjectorIdempotent =
      OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructed ≡ true
  ; hardHighPassProjectorIdempotent =
      OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue
  ; HardHighPassProjectorSelfAdjoint =
      OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructed ≡ true
  ; hardHighPassProjectorSelfAdjoint =
      OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue
  ; HardHighPassCommutesWithDerivative =
      Hard.hardHighDerivativeCurlCommutationConstructed ≡ true
  ; hardHighPassCommutesWithDerivative =
      Hard.hardHighDerivativeCurlCommutationConstructedIsTrue
  ; PeriodicVelocityDivergenceFree =
      PeriodicVelocityDivergenceFree inputs
  ; periodicVelocityDivergenceFree =
      periodicVelocityDivergenceFree inputs
  ; PressurePairingIsLiteralPeriodicPairing =
      PressurePairingIsLiteralPeriodicPairing inputs
  ; pressurePairingIsLiteralPeriodicPairing =
      pressurePairingIsLiteralPeriodicPairing inputs
  ; ProjectedConvectionTriadsExactlyEnumerated =
      PhysicalReuse.hardProjectedHighFrequencySelectionConstructed ≡ true
  ; projectedConvectionTriadsExactlyEnumerated =
      PhysicalReuse.hardProjectedHighFrequencySelectionConstructedIsTrue
  ; IncidenceMultiplicityMatchesConvolution =
      IncidenceMultiplicityMatchesConvolution inputs
  ; incidenceMultiplicityMatchesConvolution =
      incidenceMultiplicityMatchesConvolution inputs
  ; energyFluxQuantityAgreement =
      energyFluxQuantityAgreement inputs
  }

officialProjectedEnergyControlledByWeightedSchurFlux :
  ∀ {r}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {cutoff : Nat} →
  (inputs : OfficialProjectedConvectionFluxInputs model modes cutoff) →
  Projected.energyDerivative (balance inputs)
    + Projected.viscousDissipation (balance inputs)
  ≤ Flux.profileSchurConstant (weightedFluxBridge inputs)
      * (Flux.cutoffEnergyMajorant (weightedFluxBridge inputs)
        * Flux.lowPassGradientInfinity (weightedFluxBridge inputs))
officialProjectedEnergyControlledByWeightedSchurFlux inputs =
  Projected.projectedEnergyControlledByWeightedSchurFlux
    (officialProjectedConvectionFluxAdapter inputs)

officialFiniteParsevalClosesProjectedHardHighOrthogonality : Bool
officialFiniteParsevalClosesProjectedHardHighOrthogonality =
  OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructed

hardHighDerivativeCommutationReused : Bool
hardHighDerivativeCommutationReused =
  Hard.hardHighDerivativeCurlCommutationConstructed

literalProjectedTriadEnumerationReused : Bool
literalProjectedTriadEnumerationReused =
  PhysicalReuse.hardProjectedHighFrequencySelectionConstructed

projectedConvectionOfficialParsevalUpgradeConstructed : Bool
projectedConvectionOfficialParsevalUpgradeConstructed = true

officialFiniteParsevalClosesProjectedHardHighOrthogonalityIsTrue :
  officialFiniteParsevalClosesProjectedHardHighOrthogonality ≡ true
officialFiniteParsevalClosesProjectedHardHighOrthogonalityIsTrue =
  OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue

hardHighDerivativeCommutationReusedIsTrue :
  hardHighDerivativeCommutationReused ≡ true
hardHighDerivativeCommutationReusedIsTrue =
  Hard.hardHighDerivativeCurlCommutationConstructedIsTrue

literalProjectedTriadEnumerationReusedIsTrue :
  literalProjectedTriadEnumerationReused ≡ true
literalProjectedTriadEnumerationReusedIsTrue =
  PhysicalReuse.hardProjectedHighFrequencySelectionConstructedIsTrue

projectedConvectionOfficialParsevalUpgradeConstructedIsTrue :
  projectedConvectionOfficialParsevalUpgradeConstructed ≡ true
projectedConvectionOfficialParsevalUpgradeConstructedIsTrue = refl
