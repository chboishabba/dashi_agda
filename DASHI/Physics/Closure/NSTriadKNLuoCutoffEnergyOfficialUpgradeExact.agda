module DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyOfficialUpgradeExact where

------------------------------------------------------------------------
-- PROVENANCE
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
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Upgrade the historical cutoff-bootstrap adapter using the official finite
-- Parseval and official physical energy/time identifications that were added
-- later in the dependency graph.  This avoids reopening the older module and
-- avoids a dependency cycle: the older bootstrap algebra remains below the
-- official physical realization, while this adapter lives above both.
--
-- The hard-high orthogonal projection and energy/dissipation identification
-- are therefore reused, not requested again.  The genuinely open inputs are
-- the final bootstrap certificate and the source-specific low-pass, flux,
-- threshold and regularity meanings.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPhysicalEnergyTimeExact as OfficialEnergy
import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact as OfficialParseval

record OfficialLuoPhysicalEnergyBootstrapInputs
    {r d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat}
    (identification :
      OfficialEnergy.OfficialLuoPhysicalEnergyTimeIdentification
        model modes lerayHopf terminalTime regular shell)
    : Set (lsuc (r ⊔ d ⊔ s ⊔ t)) where
  field
    bootstrap :
      Bootstrap.LuoCutoffBootstrapCertificate
        (OfficialEnergy.officialCutoffData identification)

    HardLowPassEqualsSourceLowPass : Set
    hardLowPassEqualsSourceLowPass : HardLowPassEqualsSourceLowPass

    DivergenceFreePressureCancellation : Set
    divergenceFreePressureCancellation : DivergenceFreePressureCancellation

    PhysicalFluxMatchesIntegratedAbsoluteCutoffFlux : Set
    physicalFluxMatchesIntegratedAbsoluteCutoffFlux :
      PhysicalFluxMatchesIntegratedAbsoluteCutoffFlux

    UniversalThresholdMatchesLuoDeltaBKMAtUnitViscosity : Set
    universalThresholdMatchesLuoDeltaBKMAtUnitViscosity :
      UniversalThresholdMatchesLuoDeltaBKMAtUnitViscosity

    BootstrapDecayImpliesRegularity : Set
    bootstrapDecayImpliesRegularity : BootstrapDecayImpliesRegularity

open OfficialLuoPhysicalEnergyBootstrapInputs public

officialPhysicalEnergyBootstrapAdapter :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat}
    {identification :
      OfficialEnergy.OfficialLuoPhysicalEnergyTimeIdentification
        model modes lerayHopf terminalTime regular shell} →
  OfficialLuoPhysicalEnergyBootstrapInputs identification →
  Bootstrap.LuoPhysicalEnergyBootstrapAdapter
officialPhysicalEnergyBootstrapAdapter
  {identification = identification} inputs = record
  { timeCutoff = OfficialEnergy.timeCutoff identification
  ; cutoffData = OfficialEnergy.officialCutoffData identification
  ; bootstrap = bootstrap inputs
  ; HardLowPassEqualsSourceLowPass =
      HardLowPassEqualsSourceLowPass inputs
  ; hardLowPassEqualsSourceLowPass =
      hardLowPassEqualsSourceLowPass inputs
  ; HardHighPassIsOrthogonalSelfAdjointProjection =
      OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructed ≡ true
  ; hardHighPassIsOrthogonalSelfAdjointProjection =
      OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue
  ; DivergenceFreePressureCancellation =
      DivergenceFreePressureCancellation inputs
  ; divergenceFreePressureCancellation =
      divergenceFreePressureCancellation inputs
  ; PhysicalEnergyIdentityMatchesCutoffData =
      OfficialEnergy.officialEnergyDissipationIdentitiesClosed ≡ true
  ; physicalEnergyIdentityMatchesCutoffData =
      OfficialEnergy.officialEnergyDissipationIdentitiesClosedIsTrue
  ; PhysicalDissipationMatchesCutoffData =
      OfficialEnergy.officialEnergyDissipationIdentitiesClosed ≡ true
  ; physicalDissipationMatchesCutoffData =
      OfficialEnergy.officialEnergyDissipationIdentitiesClosedIsTrue
  ; PhysicalFluxMatchesIntegratedAbsoluteCutoffFlux =
      PhysicalFluxMatchesIntegratedAbsoluteCutoffFlux inputs
  ; physicalFluxMatchesIntegratedAbsoluteCutoffFlux =
      physicalFluxMatchesIntegratedAbsoluteCutoffFlux inputs
  ; UniversalThresholdMatchesLuoDeltaBKMAtUnitViscosity =
      UniversalThresholdMatchesLuoDeltaBKMAtUnitViscosity inputs
  ; universalThresholdMatchesLuoDeltaBKMAtUnitViscosity =
      universalThresholdMatchesLuoDeltaBKMAtUnitViscosity inputs
  ; BootstrapDecayImpliesRegularity =
      BootstrapDecayImpliesRegularity inputs
  ; bootstrapDecayImpliesRegularity =
      bootstrapDecayImpliesRegularity inputs
  }

officialCutoffHardHighOrthogonalityClosed : Bool
officialCutoffHardHighOrthogonalityClosed =
  OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructed

officialCutoffEnergyDissipationIdentificationClosed : Bool
officialCutoffEnergyDissipationIdentificationClosed =
  OfficialEnergy.officialEnergyDissipationIdentitiesClosed

officialCutoffEnergyUpgradeConstructed : Bool
officialCutoffEnergyUpgradeConstructed = true

officialCutoffHardHighOrthogonalityClosedIsTrue :
  officialCutoffHardHighOrthogonalityClosed ≡ true
officialCutoffHardHighOrthogonalityClosedIsTrue =
  OfficialParseval.officialPhysicalHardProjectorOrthogonalConstructedIsTrue

officialCutoffEnergyDissipationIdentificationClosedIsTrue :
  officialCutoffEnergyDissipationIdentificationClosed ≡ true
officialCutoffEnergyDissipationIdentificationClosedIsTrue =
  OfficialEnergy.officialEnergyDissipationIdentitiesClosedIsTrue

officialCutoffEnergyUpgradeConstructedIsTrue :
  officialCutoffEnergyUpgradeConstructed ≡ true
officialCutoffEnergyUpgradeConstructedIsTrue = refl
