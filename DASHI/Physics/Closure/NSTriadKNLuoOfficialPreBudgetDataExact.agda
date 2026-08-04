module DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Remove a circularity from the official continuation architecture. The
-- previous aggregate owned terminalBudgetAt, which is already Luo's localized
-- hypothesis. This module separates:
--
--   1. pre-budget physical data and exact carrier identifications;
--   2. a derived hard-terminal-window budget family;
--   3. completion of the existing official continuation closure.
--
-- Thus a canonical NS route must construct the budget from its flux/bootstrap
-- estimates; it cannot receive the desired continuation criterion as part of
-- the physical-data input.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSZ3CutoffUniformIntegerShellSchur as Z3Shell
import DASHI.Physics.Closure.NSTriadKNHardHighPhysicalZ3PairEncodingExact as Encoding
import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellPhysicalIdentificationExact as ProgramIdentification
import DASHI.Physics.Closure.NSTriadKNLuoCrossCarrierRationalIdentificationExact as Cross
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Flux
import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPhysicalEnergyTimeExact as EnergyTime
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as MultiplierAbstract
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as OfficialLuo
import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Completed

record OfficialLuoPreBudgetData
    {d s t : Level}
    (InitialDatum : Set d)
    (Solution : Set s)
    (Time : Set t) : Setω where
  field
    program : Closure.CompactGammaAnalyticClosure
    KAt NAt cubeCutoffAt : Nat → Nat

    z3FullShellFamily :
      FullShell.FullShellFourierFamily
        Z3Shell.Z3ResonantPair Z3.FourierMode ℚ

    hardHighPairIdentificationAt :
      (shell : Nat) →
      Encoding.HardHighPhysicalZ3FullShellPairIdentification
        z3FullShellFamily
        (KAt shell) (NAt shell) shell (cubeCutoffAt shell)

    hardHighProgramPairIdentificationAt :
      (shell : Nat) →
      ProgramIdentification.HardHighPhysicalFullShellIdentification
        program (KAt shell) (NAt shell) shell (cubeCutoffAt shell)

    crossCarrierAt :
      (shell : Nat) →
      Cross.RationalizedFullShellPhysicalBridgeInputs
        program (KAt shell) (NAt shell)

    sourceCarrier :
      OfficialLuo.OfficialPeriodicLuoSourceCarrier
        InitialDatum Solution Time

    initial : InitialDatum
    solution : Solution
    terminal : Time

    sourceSelection :
      OfficialLuo.OfficialLuoSolutionSelection
        sourceCarrier initial solution terminal

    realLevel : Level
    projectorModel : LP.PeriodicHardShellFourierPDE {r = realLevel}
    physicalModes : List Z3.FourierMode

    physicalEnergyTimeAt :
      (shell : Nat) →
      EnergyTime.OfficialLuoPhysicalEnergyTimeIdentification
        projectorModel
        physicalModes
        (OfficialLuo.lerayHopfSolutionAt sourceCarrier initial solution)
        terminal
        (OfficialLuo.regularBeforeTerminal sourceSelection)
        shell

    TorusPoint : Set s

    multiplierRealization :
      Multiplier.CanonicalLuoMultiplierRealization Solution TorusPoint

    hardIntegralMatchesOfficialGradient :
      (shell : Nat) →
      MultiplierAbstract.hardTerminalWindowIntegral
        (Multiplier.canonicalLuoMultiplierAuthority multiplierRealization)
        shell solution
      ≡
      LH.localizedLowPassGradientIntegral
        (EnergyTime.cutoffQuantities (physicalEnergyTimeAt shell))

    smoothIntegralMatchesSource :
      (shell : Nat) →
      MultiplierAbstract.smoothTerminalWindowIntegral
        (Multiplier.canonicalLuoMultiplierAuthority multiplierRealization)
        shell solution
      ≡
      OfficialLuo.localizedGradientIntegral
        sourceCarrier solution terminal shell

open OfficialLuoPreBudgetData public

preBudgetPhysicalBridge :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  OfficialLuoPreBudgetData InitialDatum Solution Time →
  Nat → Flux.PhysicalCutoffFluxWeightedSchurBridge
preBudgetPhysicalBridge data shell =
  Cross.physicalBridgeFromFullShell
    (program data) (KAt data shell) (NAt data shell)
    (crossCarrierAt data shell)

record DerivedLuoTerminalBudgetFamily
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : OfficialLuoPreBudgetData InitialDatum Solution Time) : Setω where
  field
    hardBudgetAt : Nat → ℚ

    hardBudgetNonnegative :
      (shell : Nat) → 0ℚ ≤ hardBudgetAt shell

    universalDeltaNonnegative :
      0ℚ ≤ OfficialLuo.universalDeltaBKM (sourceCarrier data)

    hardIntegralBelowBudget :
      (shell : Nat) →
      MultiplierAbstract.hardTerminalWindowIntegral
        (Multiplier.canonicalLuoMultiplierAuthority
          (multiplierRealization data))
        shell (solution data)
      ≤ hardBudgetAt shell

    scaledBudgetBelowLuoDelta :
      (shell : Nat) →
      MultiplierAbstract.hardSmoothMultiplierLInfinityConstant
        (Multiplier.canonicalLuoMultiplierAuthority
          (multiplierRealization data))
        * hardBudgetAt shell
      ≤ OfficialLuo.universalDeltaBKM (sourceCarrier data)

open DerivedLuoTerminalBudgetFamily public

derivedTerminalBudgetAt :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : OfficialLuoPreBudgetData InitialDatum Solution Time} →
  DerivedLuoTerminalBudgetFamily data →
  (shell : Nat) →
  MultiplierAbstract.LuoTerminalWindowBudget
    (Multiplier.canonicalLuoMultiplierAuthority
      (multiplierRealization data))
    shell (solution data)
derivedTerminalBudgetAt {data = data} budgets shell = record
  { hardBudget = hardBudgetAt budgets shell
  ; universalThreshold = OfficialLuo.universalDeltaBKM (sourceCarrier data)
  ; hardBudgetNonnegative = hardBudgetNonnegative budgets shell
  ; universalThresholdNonnegative = universalDeltaNonnegative budgets
  ; hardIntegralBelowBudget = hardIntegralBelowBudget budgets shell
  ; scaledBudgetBelowThreshold = scaledBudgetBelowLuoDelta budgets shell
  }

completeOfficialLuoClosure :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (data : OfficialLuoPreBudgetData InitialDatum Solution Time) →
  DerivedLuoTerminalBudgetFamily data →
  Completed.OfficialLuoContinuationClosure InitialDatum Solution Time
completeOfficialLuoClosure data budgets = record
  { program = program data
  ; KAt = KAt data
  ; NAt = NAt data
  ; cubeCutoffAt = cubeCutoffAt data
  ; z3FullShellFamily = z3FullShellFamily data
  ; hardHighPairIdentificationAt = hardHighPairIdentificationAt data
  ; hardHighProgramPairIdentificationAt =
      hardHighProgramPairIdentificationAt data
  ; crossCarrierAt = crossCarrierAt data
  ; sourceCarrier = sourceCarrier data
  ; initial = initial data
  ; solution = solution data
  ; terminal = terminal data
  ; sourceSelection = sourceSelection data
  ; realLevel = realLevel data
  ; projectorModel = projectorModel data
  ; physicalModes = physicalModes data
  ; physicalEnergyTimeAt = physicalEnergyTimeAt data
  ; TorusPoint = TorusPoint data
  ; multiplierRealization = multiplierRealization data
  ; terminalBudgetAt = derivedTerminalBudgetAt budgets
  ; hardIntegralMatchesOfficialGradient =
      hardIntegralMatchesOfficialGradient data
  ; smoothIntegralMatchesSource = smoothIntegralMatchesSource data
  ; thresholdMatchesLuoDelta = λ shell → refl
  }

preBudgetArchitectureConstructed : Bool
preBudgetArchitectureConstructed = true

terminalBudgetNoLongerPhysicalDataInput : Bool
terminalBudgetNoLongerPhysicalDataInput = true

preBudgetArchitectureConstructedIsTrue :
  preBudgetArchitectureConstructed ≡ true
preBudgetArchitectureConstructedIsTrue = refl

terminalBudgetNoLongerPhysicalDataInputIsTrue :
  terminalBudgetNoLongerPhysicalDataInput ≡ true
terminalBudgetNoLongerPhysicalDataInputIsTrue = refl
