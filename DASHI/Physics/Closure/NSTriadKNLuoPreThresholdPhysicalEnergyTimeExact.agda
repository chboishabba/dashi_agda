module DASHI.Physics.Closure.NSTriadKNLuoPreThresholdPhysicalEnergyTimeExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Identify the official physical cutoff energy, factor-two dissipation,
-- pointwise/integrated flux, weighted energy, gradient integral and parabolic
-- window before any localized-gradient threshold is supplied.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNProjectedConvectionEnergyFluxExact as Energy
import DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdCutoffQuantitiesExact as PreThreshold

record PreThresholdLuoPhysicalEnergyTimeIdentification
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

    cutoffQuantities :
      PreThreshold.PreThresholdLuoCutoffQuantities regular shell

    timeCutoff : Bootstrap.LuoParabolicTimeCutoff

    embedCutoffTime : Bootstrap.Time timeCutoff → Time
    evaluationCutoffTime : Bootstrap.Time timeCutoff
    terminalCutoffTime : Bootstrap.Time timeCutoff
    evaluationTime : Time

    evaluationTimeMeaning :
      embedCutoffTime evaluationCutoffTime ≡ evaluationTime

    terminalTimeMeaning :
      embedCutoffTime terminalCutoffTime ≡ terminalTime

    pointwiseProjectedFluxMeaning :
      Energy.absoluteCutoffFlux (Energy.balance projectedEnergyFlux)
      ≡ PreThreshold.absoluteCutoffFluxAtTime cutoffQuantities evaluationTime

    cutoffWindowDenominatorMeaning :
      Bootstrap.windowDenominator timeCutoff
      ≡ PreThreshold.parabolicWindowDenominator cutoffQuantities

    TimeEmbeddingPreservesLuoTerminalWindow : Set t
    timeEmbeddingPreservesLuoTerminalWindow :
      TimeEmbeddingPreservesLuoTerminalWindow

open PreThresholdLuoPhysicalEnergyTimeIdentification public

preThresholdPhysicalEnergyTimeCarrierConstructed : Bool
preThresholdPhysicalEnergyTimeCarrierConstructed = true

preThresholdPhysicalEnergyTimeCarrierConstructedIsTrue :
  preThresholdPhysicalEnergyTimeCarrierConstructed ≡ true
preThresholdPhysicalEnergyTimeCarrierConstructedIsTrue = refl
