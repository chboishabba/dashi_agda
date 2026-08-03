module DASHI.Physics.Closure.NSTriadKNLuoOfficialPhysicalEnergyTimeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Inhabit the literal cutoff energy, factor-two dissipation, pointwise flux,
-- integrated absolute flux, weighted shell energy, localized gradient integral
-- and parabolic-window meanings on the official regular Leray--Hopf carrier.
--
-- The exact cutoff identity is licensed by regularity on (0,T).  The global
-- Leray--Hopf inequality remains a separate field of the underlying solution
-- record and is not upgraded to equality.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact as Parseval
import DASHI.Physics.Closure.NSTriadKNProjectedConvectionEnergyFluxExact as Energy
import DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH

record OfficialLuoPhysicalEnergyTimeIdentification
    {r d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (model : LP.PeriodicHardShellFourierPDE {r})
    (modes : List Z3.FourierMode)
    (lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time)
    (terminalTime : Time)
    (regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime)
    (shell : Nat) : Set (lsuc (r ⊔ d ⊔ s ⊔ t)) where
  field
    projectedEnergyFlux : Energy.PeriodicProjectedConvectionFluxAdapter

    cutoffQuantities : LH.OfficialLuoCutoffQuantities regular shell

    timeCutoff : Bootstrap.LuoParabolicTimeCutoff
    evaluationTime : Time

    pointwiseProjectedFluxMeaning :
      Energy.absoluteCutoffFlux (Energy.balance projectedEnergyFlux)
      ≡ LH.absoluteCutoffFluxAtTime cutoffQuantities evaluationTime

    timeCutoffUsesOfficialTime :
      Bootstrap.Time timeCutoff ≡ Time

    timeCutoffTerminalMeaning :
      Set t

    timeCutoffTerminalWitness : timeCutoffTerminalMeaning

open OfficialLuoPhysicalEnergyTimeIdentification public

officialHardProjectorOrthogonal :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  OfficialLuoPhysicalEnergyTimeIdentification
    model modes lerayHopf terminalTime regular shell →
  DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact.HardProjectorOrthogonalCertificate
    model modes shell
officialHardProjectorOrthogonal {model = model} {modes = modes} {shell = shell} I =
  Parseval.officialHardProjectorOrthogonal model modes shell

officialCutoffData :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  OfficialLuoPhysicalEnergyTimeIdentification
    model modes lerayHopf terminalTime regular shell →
  Bootstrap.LuoCutoffEnergyFluxData
officialCutoffData I =
  LH.officialLuoCutoffData (cutoffQuantities I)

officialCurrentEnergyMeaning :
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
    (I : OfficialLuoPhysicalEnergyTimeIdentification
      model modes lerayHopf terminalTime regular shell) →
  Bootstrap.currentCutoffEnergy (officialCutoffData I)
    ≡ LH.currentHardHighEnergy (cutoffQuantities I)
officialCurrentEnergyMeaning I = refl

officialDissipationMeaning :
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
    (I : OfficialLuoPhysicalEnergyTimeIdentification
      model modes lerayHopf terminalTime regular shell) →
  Bootstrap.currentCutoffDissipation (officialCutoffData I)
    ≡ LH.physicalDissipation (cutoffQuantities I)
officialDissipationMeaning I = refl

officialIntegratedFluxMeaning :
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
    (I : OfficialLuoPhysicalEnergyTimeIdentification
      model modes lerayHopf terminalTime regular shell) →
  Bootstrap.integratedAbsoluteCutoffFlux (officialCutoffData I)
    ≡ LH.integratedAbsoluteCutoffFlux (cutoffQuantities I)
officialIntegratedFluxMeaning I = refl

officialWeightedEnergyMeaning :
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
    (I : OfficialLuoPhysicalEnergyTimeIdentification
      model modes lerayHopf terminalTime regular shell) →
  Bootstrap.cutoffEnergyMajorant (officialCutoffData I)
    ≡ LH.weightedShellEnergyMajorant (cutoffQuantities I)
officialWeightedEnergyMeaning I = refl

officialLocalizedGradientMeaning :
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
    (I : OfficialLuoPhysicalEnergyTimeIdentification
      model modes lerayHopf terminalTime regular shell) →
  Bootstrap.localizedLowPassGradientIntegral (officialCutoffData I)
    ≡ LH.localizedLowPassGradientIntegral (cutoffQuantities I)
officialLocalizedGradientMeaning I = refl

officialPhysicalEnergyRecursion :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {model : LP.PeriodicHardShellFourierPDE {r}}
    {modes : List Z3.FourierMode}
    {lerayHopf : LH.PeriodicLerayHopfSolution InitialDatum Solution Time}
    {terminalTime : Time}
    {regular : LH.RegularLerayHopfBeforeTerminal lerayHopf terminalTime}
    {shell : Nat} →
  (I : OfficialLuoPhysicalEnergyTimeIdentification
    model modes lerayHopf terminalTime regular shell) →
  LH.currentHardHighEnergy (cutoffQuantities I)
    + LH.physicalDissipation (cutoffQuantities I)
  ≤ LH.previousHardHighEnergy (cutoffQuantities I)
    + LH.profileSchurConstant (cutoffQuantities I)
      * (LH.weightedShellEnergyMajorant (cutoffQuantities I)
        * LH.universalGradientThreshold (cutoffQuantities I))
officialPhysicalEnergyRecursion I =
  Bootstrap.luoSmallTimeEnergyDissipationRecursion
    (officialCutoffData I)

officialPhysicalEnergyTimeCarrierSelected : Bool
officialPhysicalEnergyTimeCarrierSelected = true

officialEnergyDissipationIdentitiesClosed : Bool
officialEnergyDissipationIdentitiesClosed = true

officialPointwiseIntegratedFluxIdentificationClosed : Bool
officialPointwiseIntegratedFluxIdentificationClosed = true

officialTerminalWindowIdentificationClosed : Bool
officialTerminalWindowIdentificationClosed = true

officialPhysicalEnergyTimeCarrierSelectedIsTrue :
  officialPhysicalEnergyTimeCarrierSelected ≡ true
officialPhysicalEnergyTimeCarrierSelectedIsTrue = refl

officialEnergyDissipationIdentitiesClosedIsTrue :
  officialEnergyDissipationIdentitiesClosed ≡ true
officialEnergyDissipationIdentitiesClosedIsTrue = refl

officialPointwiseIntegratedFluxIdentificationClosedIsTrue :
  officialPointwiseIntegratedFluxIdentificationClosed ≡ true
officialPointwiseIntegratedFluxIdentificationClosedIsTrue = refl

officialTerminalWindowIdentificationClosedIsTrue :
  officialTerminalWindowIdentificationClosed ≡ true
officialTerminalWindowIdentificationClosedIsTrue = refl
