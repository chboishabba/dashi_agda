module DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellTermFoldExact where

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
-- PURPOSE
-- Close the finite reindexing part of the r_p Fourier realization. The
-- pre-budget physical owner already contains the exact hard-high physical
-- triad to mature analytic-program full-shell pair identification. Mapping any
-- pair contribution over those equal lists, and folding the resulting lists,
-- therefore preserves the exact result, order and multiplicity. No terminal
-- localized-gradient budget is used by this theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoHardHighFullShellPhysicalIdentificationExact as Identification
import DASHI.Physics.Closure.NSTriadKNPhysicalHardHighTriadSelectionExact as High
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSCompactGammaFullShellSchur as FullShell
import DASHI.Physics.Closure.NSPairIncidenceKernel as PairKernel

mapList :
  ∀ {a b} {A : Set a} {B : Set b} →
  (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

foldList :
  ∀ {a} {A : Set a} →
  (A → A → A) → A → List A → A
foldList combine zero [] = zero
foldList combine zero (value ∷ values) =
  combine value (foldList combine zero values)

hardHighPairContributionList :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (data : PreBudget.OfficialLuoPreBudgetData
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution :
    Closure.Pair (PreBudget.program data) → Contribution) →
  List Contribution
hardHighPairContributionList data shell pairContribution =
  mapList pairContribution
    (Identification.mapList
      (Identification.encodePhysical
        (PreBudget.hardHighProgramPairIdentificationAt data shell))
      (High.hardHighPhysicalTriads
        shell (PreBudget.cubeCutoffAt data shell)))

fullShellPairContributionList :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (data : PreBudget.OfficialLuoPreBudgetData
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution :
    Closure.Pair (PreBudget.program data) → Contribution) →
  List Contribution
fullShellPairContributionList data shell pairContribution =
  mapList pairContribution
    (PairKernel.pairs
      (FullShell.pairDataAt
        (Closure.fullShellFamily (PreBudget.program data))
        (PreBudget.KAt data shell)
        (PreBudget.NAt data shell)))

preBudgetHardHighListMatchesProgramFullShell :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (data : PreBudget.OfficialLuoPreBudgetData
    InitialDatum Solution Time) →
  (shell : Nat) →
  Identification.mapList
    (Identification.encodePhysical
      (PreBudget.hardHighProgramPairIdentificationAt data shell))
    (High.hardHighPhysicalTriads
      shell (PreBudget.cubeCutoffAt data shell))
  ≡
  PairKernel.pairs
    (FullShell.pairDataAt
      (Closure.fullShellFamily (PreBudget.program data))
      (PreBudget.KAt data shell)
      (PreBudget.NAt data shell))
preBudgetHardHighListMatchesProgramFullShell data shell =
  Identification.selectedPhysicalListIsFullShellPairList
    (PreBudget.program data)
    (PreBudget.KAt data shell)
    (PreBudget.NAt data shell)
    shell
    (PreBudget.cubeCutoffAt data shell)
    (PreBudget.hardHighProgramPairIdentificationAt data shell)

hardHighContributionListMatchesFullShell :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (data : PreBudget.OfficialLuoPreBudgetData
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution :
    Closure.Pair (PreBudget.program data) → Contribution) →
  hardHighPairContributionList data shell pairContribution
  ≡ fullShellPairContributionList data shell pairContribution
hardHighContributionListMatchesFullShell data shell pairContribution =
  cong (mapList pairContribution)
    (preBudgetHardHighListMatchesProgramFullShell data shell)

hardHighContributionFoldMatchesFullShell :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (data : PreBudget.OfficialLuoPreBudgetData
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution :
    Closure.Pair (PreBudget.program data) → Contribution) →
  (combine : Contribution → Contribution → Contribution) →
  (zero : Contribution) →
  foldList combine zero
    (hardHighPairContributionList data shell pairContribution)
  ≡
  foldList combine zero
    (fullShellPairContributionList data shell pairContribution)
hardHighContributionFoldMatchesFullShell
  data shell pairContribution combine zero =
  cong (foldList combine zero)
    (hardHighContributionListMatchesFullShell
      data shell pairContribution)
