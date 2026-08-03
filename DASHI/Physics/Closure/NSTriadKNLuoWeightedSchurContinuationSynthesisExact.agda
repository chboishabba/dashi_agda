module DASHI.Physics.Closure.NSTriadKNLuoWeightedSchurContinuationSynthesisExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal/year: Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Assemble the exact theorem chain built in the localized Luo lane.  One
-- inhabitant owns the same hard-high physical triads, mature full-shell Schur
-- family, orthogonal projector, literal cutoff energy/dissipation data,
-- hard/smooth terminal-window authority and published Luo continuation
-- theorem.  Pointwise smooth cutoff bounds are transported to the source
-- integral/threshold and assembled into Luo's limsup hypothesis internally.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (_+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorption
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as High
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSTriadKNLuoCutoffEnergyBootstrapExact as Bootstrap
import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellPhysicalIdentificationExact as PhysicalFullShell
import DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact as FullShellFlux
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalEnergyDissipationTimeExact as PhysicalTime
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicMultiplierKernelBoundExact as Multiplier
import DASHI.Physics.Closure.NSTriadKNLuoPublishedContinuationAuthorityExact as Published

record LuoWeightedSchurContinuationSynthesis : Setω where
  field
    program : Closure.CompactGammaAnalyticClosure

    KAt NAt cubeCutoffAt : Nat → Nat

    hardHighPhysicalFullShellAt :
      (shell : Nat) →
      PhysicalFullShell.HardHighPhysicalFullShellIdentification
        program (KAt shell) (NAt shell) shell (cubeCutoffAt shell)

    fullShellFluxAt :
      (shell : Nat) →
      FullShellFlux.LuoFullShellPhysicalIdentification
        program (KAt shell) (NAt shell)

    realLevel : Level
    projectorModel :
      LP.PeriodicHardShellFourierPDE {r = realLevel}
    physicalModes : List Z3.FourierMode

    physicalEnergyTimeAt :
      (shell : Nat) →
      PhysicalTime.LiteralLuoCutoffEnergyDissipationTimeIdentification
        projectorModel physicalModes shell

    State InitialDatum Solution Time : Set

    multiplierAuthority :
      Multiplier.PublishedLuoPeriodicMultiplierKernelAuthority State
    stateAt : Nat → State

    terminalBudgetAt :
      (shell : Nat) →
      Multiplier.LuoTerminalWindowBudget
        multiplierAuthority shell (stateAt shell)

    hardIntegralMatchesPhysicalGradient :
      (shell : Nat) →
      Multiplier.hardTerminalWindowIntegral
        multiplierAuthority shell (stateAt shell)
      ≡
      PhysicalTime.physicalLocalizedLowPassGradientIntegral
        (physicalEnergyTimeAt shell)

    FullShellFluxMatchesProjectedEnergyFlux : Nat → Set
    fullShellFluxMatchesProjectedEnergyFlux :
      (shell : Nat) →
      FullShellFluxMatchesProjectedEnergyFlux shell

    continuationAuthority :
      Published.PublishedLuoTheorem11Authority
        InitialDatum Solution Time

    initialDatum : InitialDatum
    solution : Solution
    terminalTime : Time

    smoothInitialDatum :
      Published.SmoothDivergenceFreeFiniteEnergy
        continuationAuthority initialDatum

    solutionSolves :
      Published.SolvesPeriodicNavierStokesFrom
        continuationAuthority initialDatum solution

    smoothIntegralMatchesSource :
      (shell : Nat) →
      Multiplier.smoothTerminalWindowIntegral
        multiplierAuthority shell (stateAt shell)
      ≡
      Published.localizedGradientIntegral
        continuationAuthority solution terminalTime shell

    multiplierThresholdMatchesLuoDelta :
      (shell : Nat) →
      Multiplier.universalThreshold (terminalBudgetAt shell)
      ≡ Published.universalDeltaBKM continuationAuthority

open LuoWeightedSchurContinuationSynthesis public

hardHighPhysicalListMatchesFullShell :
  (S : LuoWeightedSchurContinuationSynthesis) →
  (shell : Nat) →
  PhysicalFullShell.mapList
    (PhysicalFullShell.encodePhysical
      (hardHighPhysicalFullShellAt S shell))
    (High.hardHighPhysicalTriads shell (cubeCutoffAt S shell))
  ≡
  PairKernel.pairs
    (FullShell.pairDataAt
      (Closure.fullShellFamily (program S))
      (KAt S shell) (NAt S shell))
hardHighPhysicalListMatchesFullShell S shell =
  PhysicalFullShell.selectedPhysicalListIsFullShellPairList
    (program S) (KAt S shell) (NAt S shell)
    shell (cubeCutoffAt S shell)
    (hardHighPhysicalFullShellAt S shell)

hardHighPhysicalCoefficientDominated :
  (S : LuoWeightedSchurContinuationSynthesis) →
  (shell : Nat) →
  (triad : Physical.PhysicalTriadIncidence) →
  Cube._∈_ triad
    (High.hardHighPhysicalTriads shell (cubeCutoffAt S shell)) →
  Absorption._≤_
    (Closure.arithmetic (program S))
    (PhysicalFullShell.physicalSignedMagnitude
      (hardHighPhysicalFullShellAt S shell) triad)
    (PhysicalFullShell.physicalIncidenceMajorant
      (hardHighPhysicalFullShellAt S shell) triad)
hardHighPhysicalCoefficientDominated S shell triad listed =
  PhysicalFullShell.physicalSignedCoefficientDominated
    (program S) (KAt S shell) (NAt S shell)
    shell (cubeCutoffAt S shell)
    (hardHighPhysicalFullShellAt S shell) triad listed

literalPhysicalCutoffRecursion :
  (S : LuoWeightedSchurContinuationSynthesis) →
  (shell : Nat) →
  PhysicalTime.physicalCurrentHardHighEnergy
      (physicalEnergyTimeAt S shell)
    +
  PhysicalTime.physicalIntegratedHardHighDissipation
      (physicalEnergyTimeAt S shell)
  ≤
  PhysicalTime.physicalPreviousHardHighEnergy
      (physicalEnergyTimeAt S shell)
    +
  Bootstrap.profileSchurConstant
      (PhysicalTime.cutoffData (physicalEnergyTimeAt S shell))
    *
  (PhysicalTime.physicalWeightedShellEnergyMajorant
      (physicalEnergyTimeAt S shell)
    *
   Bootstrap.universalGradientThreshold
      (PhysicalTime.cutoffData (physicalEnergyTimeAt S shell)))
literalPhysicalCutoffRecursion S shell =
  PhysicalTime.literalPhysicalLuoEnergyDissipationRecursion
    (physicalEnergyTimeAt S shell)

smoothLuoCutoffBound :
  (S : LuoWeightedSchurContinuationSynthesis) →
  (shell : Nat) →
  Multiplier.smoothTerminalWindowIntegral
    (multiplierAuthority S) shell (stateAt S shell)
  ≤
  Multiplier.universalThreshold (terminalBudgetAt S shell)
smoothLuoCutoffBound S shell =
  Multiplier.luoSmoothCriterionFromHardBudget
    (multiplierAuthority S)
    shell
    (stateAt S shell)
    (terminalBudgetAt S shell)

sourceLuoCutoffBound :
  (S : LuoWeightedSchurContinuationSynthesis) →
  (shell : Nat) →
  Published.localizedGradientIntegral
    (continuationAuthority S) (solution S) (terminalTime S) shell
  ≤ Published.universalDeltaBKM (continuationAuthority S)
sourceLuoCutoffBound S shell
  rewrite sym (smoothIntegralMatchesSource S shell)
        | sym (multiplierThresholdMatchesLuoDelta S shell) =
  smoothLuoCutoffBound S shell

sourceLuoLimsupBound :
  (S : LuoWeightedSchurContinuationSynthesis) →
  Published.LuoLocalizedGradientLimsupBound
    (continuationAuthority S) (solution S) (terminalTime S)
sourceLuoLimsupBound S =
  Published.pointwiseThresholdImpliesLimsupBound
    (continuationAuthority S)
    (solution S)
    (terminalTime S)
    (sourceLuoCutoffBound S)

luoWeightedSchurContinuation :
  (S : LuoWeightedSchurContinuationSynthesis) →
  Published.ContinuesBeyond
    (continuationAuthority S)
    (initialDatum S)
    (terminalTime S)
luoWeightedSchurContinuation S =
  Published.luoTheorem11Continuation
    (continuationAuthority S)
    (initialDatum S)
    (solution S)
    (terminalTime S)
    (smoothInitialDatum S)
    (solutionSolves S)
    (sourceLuoLimsupBound S)

luoWeightedSchurContinuationSynthesisConstructed : Bool
luoWeightedSchurContinuationSynthesisConstructed = true

canonicalLuoWeightedSchurContinuationSynthesisInhabited : Bool
canonicalLuoWeightedSchurContinuationSynthesisInhabited = false

luoWeightedSchurContinuationSynthesisConstructedIsTrue :
  luoWeightedSchurContinuationSynthesisConstructed ≡ true
luoWeightedSchurContinuationSynthesisConstructedIsTrue = refl

canonicalLuoWeightedSchurContinuationSynthesisInhabitedIsFalse :
  canonicalLuoWeightedSchurContinuationSynthesisInhabited ≡ false
canonicalLuoWeightedSchurContinuationSynthesisInhabitedIsFalse = refl
