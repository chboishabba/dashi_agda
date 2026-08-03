module DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
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
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Assemble the completed official localized-continuation lane on one carrier:
--
--   * official coefficient-unitary finite Fourier Parseval;
--   * the concrete normalized-exponential Luo cutoff and periodized kernel;
--   * exact hard-high physical triad -> Z3 full-shell pair encoding;
--   * one rational owner for flux, Schur constant, weighted energy and
--     low-pass gradient;
--   * regular Leray--Hopf cutoff energy/dissipation/flux/time identities;
--   * Luo's published T3, unit-viscosity continuation theorem.
--
-- The resulting implication is exact.  The standard multiplier and Luo source
-- theorems retain proof level standardImported and therefore do not by
-- themselves promote any Clay or global-regularity gate.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSZ3CutoffUniformIntegerShellSchur as Z3Shell
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as High
import DASHI.Physics.Closure.NSTriadKNHardHighPhysicalZ3PairEncodingExact as Encoding
import DASHI.Physics.Closure.NSTriadKNLuoCrossCarrierRationalIdentificationExact as Cross
import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoOfficialPhysicalEnergyTimeExact as EnergyTime
import DASHI.Physics.Closure.NSTriadKNLuoConcreteRadialMultiplierKernelExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as MultiplierAbstract
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as OfficialLuo
import DASHI.Physics.Closure.NSTriadKNLuoPublishedContinuationAuthorityExact as Luo

record OfficialLuoContinuationClosure
    {r d s t : Level}
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

    terminalBudgetAt :
      (shell : Nat) →
      MultiplierAbstract.LuoTerminalWindowBudget
        (Multiplier.canonicalLuoMultiplierAuthority multiplierRealization)
        shell solution

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

    thresholdMatchesLuoDelta :
      (shell : Nat) →
      MultiplierAbstract.universalThreshold (terminalBudgetAt shell)
      ≡ OfficialLuo.universalDeltaBKM sourceCarrier

open OfficialLuoContinuationClosure public

officialHardHighListMatchesFullShell :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  Encoding.hardHighPhysicalZ3Pairs shell (cubeCutoffAt C shell)
  ≡ PairKernel.pairs
      (FullShell.pairDataAt
        (z3FullShellFamily C)
        (KAt C shell) (NAt C shell))
officialHardHighListMatchesFullShell C shell =
  Encoding.encodedHardHighListIsFullShellPairList
    (hardHighPairIdentificationAt C shell)

officialPhysicalBridge :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact.PhysicalCutoffFluxWeightedSchurBridge
officialPhysicalBridge C shell =
  Cross.physicalBridgeFromFullShell
    (program C) (KAt C shell) (NAt C shell)
    (crossCarrierAt C shell)

officialFluxCrossCarrierEquality :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  Cross.scalarToRational (crossCarrierAt C shell)
    (DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact.absoluteCutoffFlux
      (Cross.fullShellAdapter (crossCarrierAt C shell)))
  ≡
  DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact.absoluteCutoffFlux
    (officialPhysicalBridge C shell)
officialFluxCrossCarrierEquality C shell =
  Cross.fullShellFluxMatchesPhysicalBridge
    (program C) (KAt C shell) (NAt C shell)
    (crossCarrierAt C shell)

officialSchurCrossCarrierEquality :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  Cross.scalarToRational (crossCarrierAt C shell)
    (DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact.profileSchurConstant
      (Cross.fullShellAdapter (crossCarrierAt C shell)))
  ≡
  DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact.profileSchurConstant
    (officialPhysicalBridge C shell)
officialSchurCrossCarrierEquality C shell =
  Cross.fullShellSchurConstantMatchesPhysicalBridge
    (program C) (KAt C shell) (NAt C shell)
    (crossCarrierAt C shell)

officialEnergyCrossCarrierEquality :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  Cross.scalarToRational (crossCarrierAt C shell)
    (DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact.cutoffEnergyMajorant
      (Cross.fullShellAdapter (crossCarrierAt C shell)))
  ≡
  DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact.cutoffEnergyMajorant
    (officialPhysicalBridge C shell)
officialEnergyCrossCarrierEquality C shell =
  Cross.fullShellEnergyMatchesPhysicalBridge
    (program C) (KAt C shell) (NAt C shell)
    (crossCarrierAt C shell)

officialGradientCrossCarrierEquality :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  Cross.scalarToRational (crossCarrierAt C shell)
    (DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact.lowPassGradientInfinity
      (Cross.fullShellAdapter (crossCarrierAt C shell)))
  ≡
  DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact.lowPassGradientInfinity
    (officialPhysicalBridge C shell)
officialGradientCrossCarrierEquality C shell =
  Cross.fullShellGradientMatchesPhysicalBridge
    (program C) (KAt C shell) (NAt C shell)
    (crossCarrierAt C shell)

officialSmoothCutoffBound :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  MultiplierAbstract.smoothTerminalWindowIntegral
    (Multiplier.canonicalLuoMultiplierAuthority
      (multiplierRealization C))
    shell (solution C)
  ≤ MultiplierAbstract.universalThreshold (terminalBudgetAt C shell)
officialSmoothCutoffBound C shell =
  MultiplierAbstract.luoSmoothCriterionFromHardBudget
    (Multiplier.canonicalLuoMultiplierAuthority
      (multiplierRealization C))
    shell (solution C) (terminalBudgetAt C shell)

officialSourceCutoffBound :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  (shell : Nat) →
  OfficialLuo.localizedGradientIntegral
    (sourceCarrier C) (solution C) (terminal C) shell
  ≤ OfficialLuo.universalDeltaBKM (sourceCarrier C)
officialSourceCutoffBound C shell
  rewrite sym (smoothIntegralMatchesSource C shell)
        | sym (thresholdMatchesLuoDelta C shell) =
  officialSmoothCutoffBound C shell

officialSourceLimsupBound :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  OfficialLuo.LuoLocalizedGradientLimsupBound
    (sourceCarrier C) (solution C) (terminal C)
officialSourceLimsupBound C =
  OfficialLuo.pointwiseThresholdImpliesLimsupBound
    (sourceCarrier C) (solution C) (terminal C)
    (officialSourceCutoffBound C)

officialLuoContinuation :
  ∀ {r d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (C : OfficialLuoContinuationClosure
    {r = r} InitialDatum Solution Time) →
  OfficialLuo.ContinuesBeyond
    (sourceCarrier C) (initial C) (terminal C)
officialLuoContinuation C =
  Luo.luoTheorem11Continuation
    (OfficialLuo.officialPeriodicLuoAuthority (sourceCarrier C))
    (initial C) (solution C) (terminal C)
    (OfficialLuo.smoothInitialData (sourceSelection C))
    (OfficialLuo.solvesFromInitialData (sourceSelection C))
    (officialSourceLimsupBound C)

officialLuoContinuationClosureConstructed : Bool
officialLuoContinuationClosureConstructed = true

allSixOfficialIdentificationTasksComposed : Bool
allSixOfficialIdentificationTasksComposed = true

localizedRoutePromotedToClay : Bool
localizedRoutePromotedToClay = false

officialLuoContinuationClosureConstructedIsTrue :
  officialLuoContinuationClosureConstructed ≡ true
officialLuoContinuationClosureConstructedIsTrue = refl

allSixOfficialIdentificationTasksComposedIsTrue :
  allSixOfficialIdentificationTasksComposed ≡ true
allSixOfficialIdentificationTasksComposedIsTrue = refl

localizedRoutePromotedToClayIsFalse :
  localizedRoutePromotedToClay ≡ false
localizedRoutePromotedToClayIsFalse = refl
