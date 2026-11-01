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
-- Remove both localized-criterion circularities from the official continuation
-- architecture. Pre-budget physical data owns energy, dissipation, flux,
-- weighted energy, gradient integral, multiplier and source mappings, but owns
-- neither terminalBudgetAt nor localizedGradientThresholdSmallness.
--
-- A derived budget family subsequently supplies the hard-window estimate. It
-- is then used to complete the historical cutoff quantities, physical
-- energy/time record and official continuation closure.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (sym)

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
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdCutoffQuantitiesExact as PreQ
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdPhysicalEnergyTimeExact as PreTime
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

    preThresholdEnergyTimeAt :
      (shell : Nat) →
      PreTime.PreThresholdLuoPhysicalEnergyTimeIdentification
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
      PreQ.localizedLowPassGradientIntegral
        (PreTime.cutoffQuantities (preThresholdEnergyTimeAt shell))

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

localizedGradientBelowHardBudget :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : OfficialLuoPreBudgetData InitialDatum Solution Time} →
  (budgets : DerivedLuoTerminalBudgetFamily data) →
  (shell : Nat) →
  PreQ.localizedLowPassGradientIntegral
    (PreTime.cutoffQuantities (preThresholdEnergyTimeAt data shell))
  ≤ hardBudgetAt budgets shell
localizedGradientBelowHardBudget {data = data} budgets shell
  rewrite sym (hardIntegralMatchesOfficialGradient data shell) =
  hardIntegralBelowBudget budgets shell

completedCutoffQuantities :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : OfficialLuoPreBudgetData InitialDatum Solution Time} →
  (budgets : DerivedLuoTerminalBudgetFamily data) →
  (shell : Nat) →
  LH.OfficialLuoCutoffQuantities
    (OfficialLuo.regularBeforeTerminal (sourceSelection data)) shell
completedCutoffQuantities {data = data} budgets shell =
  let Q = PreTime.cutoffQuantities (preThresholdEnergyTimeAt data shell)
  in record
    { previousHardHighEnergy = PreQ.previousHardHighEnergy Q
    ; currentHardHighEnergy = PreQ.currentHardHighEnergy Q
    ; integratedHardHighGradientL2Squared =
        PreQ.integratedHardHighGradientL2Squared Q
    ; physicalDissipation = PreQ.physicalDissipation Q
    ; signedIntegratedProjectedFlux =
        PreQ.signedIntegratedProjectedFlux Q
    ; absoluteCutoffFluxAtTime = PreQ.absoluteCutoffFluxAtTime Q
    ; integratedAbsoluteCutoffFlux =
        PreQ.integratedAbsoluteCutoffFlux Q
    ; weightedShellEnergyMajorant =
        PreQ.weightedShellEnergyMajorant Q
    ; localizedLowPassGradientIntegral =
        PreQ.localizedLowPassGradientIntegral Q
    ; profileSchurConstant = PreQ.profileSchurConstant Q
    ; universalGradientThreshold = hardBudgetAt budgets shell
    ; previousEnergyNonnegative = PreQ.previousEnergyNonnegative Q
    ; currentEnergyNonnegative = PreQ.currentEnergyNonnegative Q
    ; integratedGradientNonnegative =
        PreQ.integratedGradientNonnegative Q
    ; physicalDissipationNonnegative =
        PreQ.physicalDissipationNonnegative Q
    ; integratedAbsoluteFluxNonnegative =
        PreQ.integratedAbsoluteFluxNonnegative Q
    ; weightedEnergyNonnegative = PreQ.weightedEnergyNonnegative Q
    ; localizedGradientNonnegative =
        PreQ.localizedGradientNonnegative Q
    ; profileSchurConstantNonnegative =
        PreQ.profileSchurConstantNonnegative Q
    ; universalGradientThresholdNonnegative =
        hardBudgetNonnegative budgets shell
    ; physicalDissipationMeaning = PreQ.physicalDissipationMeaning Q
    ; preterminalProjectedEnergyIdentity =
        PreQ.preterminalProjectedEnergyIdentity Q
    ; signedFluxBelowIntegratedAbsoluteFlux =
        PreQ.signedFluxBelowIntegratedAbsoluteFlux Q
    ; IntegratedFluxIsTimeIntegralOfPointwiseFlux =
        PreQ.IntegratedFluxIsTimeIntegralOfPointwiseFlux Q
    ; integratedFluxIsTimeIntegralOfPointwiseFlux =
        PreQ.integratedFluxIsTimeIntegralOfPointwiseFlux Q
    ; integratedFluxWeightedSchurEstimate =
        PreQ.integratedFluxWeightedSchurEstimate Q
    ; localizedGradientThresholdSmallness =
        localizedGradientBelowHardBudget budgets shell
    ; parabolicWindowDenominator = PreQ.parabolicWindowDenominator Q
    ; parabolicWindowDenominatorMeaning =
        PreQ.parabolicWindowDenominatorMeaning Q
    ; TerminalWindowIsLuoParabolicWindow =
        PreQ.TerminalWindowIsLuoParabolicWindow Q
    ; terminalWindowIsLuoParabolicWindow =
        PreQ.terminalWindowIsLuoParabolicWindow Q
    }

completedPhysicalEnergyTimeAt :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : OfficialLuoPreBudgetData InitialDatum Solution Time} →
  (budgets : DerivedLuoTerminalBudgetFamily data) →
  (shell : Nat) →
  EnergyTime.OfficialLuoPhysicalEnergyTimeIdentification
    (projectorModel data)
    (physicalModes data)
    (OfficialLuo.lerayHopfSolutionAt
      (sourceCarrier data) (initial data) (solution data))
    (terminal data)
    (OfficialLuo.regularBeforeTerminal (sourceSelection data))
    shell
completedPhysicalEnergyTimeAt {data = data} budgets shell =
  let I = preThresholdEnergyTimeAt data shell
  in record
    { projectedEnergyFlux = PreTime.projectedEnergyFlux I
    ; cutoffQuantities = completedCutoffQuantities budgets shell
    ; timeCutoff = PreTime.timeCutoff I
    ; embedCutoffTime = PreTime.embedCutoffTime I
    ; evaluationCutoffTime = PreTime.evaluationCutoffTime I
    ; terminalCutoffTime = PreTime.terminalCutoffTime I
    ; evaluationTime = PreTime.evaluationTime I
    ; evaluationTimeMeaning = PreTime.evaluationTimeMeaning I
    ; terminalTimeMeaning = PreTime.terminalTimeMeaning I
    ; pointwiseProjectedFluxMeaning =
        PreTime.pointwiseProjectedFluxMeaning I
    ; cutoffWindowDenominatorMeaning =
        PreTime.cutoffWindowDenominatorMeaning I
    ; TimeEmbeddingPreservesLuoTerminalWindow =
        PreTime.TimeEmbeddingPreservesLuoTerminalWindow I
    ; timeEmbeddingPreservesLuoTerminalWindow =
        PreTime.timeEmbeddingPreservesLuoTerminalWindow I
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
  ; physicalEnergyTimeAt = completedPhysicalEnergyTimeAt budgets
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

localizedThresholdNoLongerPhysicalDataInput : Bool
localizedThresholdNoLongerPhysicalDataInput = true

preBudgetArchitectureConstructedIsTrue :
  preBudgetArchitectureConstructed ≡ true
preBudgetArchitectureConstructedIsTrue = refl

terminalBudgetNoLongerPhysicalDataInputIsTrue :
  terminalBudgetNoLongerPhysicalDataInput ≡ true
terminalBudgetNoLongerPhysicalDataInputIsTrue = refl

localizedThresholdNoLongerPhysicalDataInputIsTrue :
  localizedThresholdNoLongerPhysicalDataInput ≡ true
localizedThresholdNoLongerPhysicalDataInputIsTrue = refl
