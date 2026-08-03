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
-- Close the finite reindexing part of the r_p Fourier realization.  The
-- official closure already proves that the encoded hard-high physical triad
-- list is exactly the mature analytic-program full-shell pair list.  Mapping
-- any pair contribution over those equal lists, and folding the resulting
-- contribution lists, therefore preserves the exact result and multiplicity.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Official
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
  (official : Official.OfficialLuoContinuationClosure
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution : Closure.Pair (Official.program official) → Contribution) →
  List Contribution
hardHighPairContributionList official shell pairContribution =
  mapList pairContribution
    (Identification.mapList
      (Identification.encodePhysical
        (Official.hardHighProgramPairIdentificationAt official shell))
      (High.hardHighPhysicalTriads
        shell (Official.cubeCutoffAt official shell)))

fullShellPairContributionList :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (official : Official.OfficialLuoContinuationClosure
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution : Closure.Pair (Official.program official) → Contribution) →
  List Contribution
fullShellPairContributionList official shell pairContribution =
  mapList pairContribution
    (PairKernel.pairs
      (FullShell.pairDataAt
        (Closure.fullShellFamily (Official.program official))
        (Official.KAt official shell)
        (Official.NAt official shell)))

hardHighContributionListMatchesFullShell :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (official : Official.OfficialLuoContinuationClosure
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution : Closure.Pair (Official.program official) → Contribution) →
  hardHighPairContributionList official shell pairContribution
  ≡ fullShellPairContributionList official shell pairContribution
hardHighContributionListMatchesFullShell official shell pairContribution =
  cong (mapList pairContribution)
    (Official.officialHardHighListMatchesProgramFullShell official shell)

hardHighContributionFoldMatchesFullShell :
  ∀ {d s t contributionLevel}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {Contribution : Set contributionLevel} →
  (official : Official.OfficialLuoContinuationClosure
    InitialDatum Solution Time) →
  (shell : Nat) →
  (pairContribution : Closure.Pair (Official.program official) → Contribution) →
  (combine : Contribution → Contribution → Contribution) →
  (zero : Contribution) →
  foldList combine zero
    (hardHighPairContributionList official shell pairContribution)
  ≡
  foldList combine zero
    (fullShellPairContributionList official shell pairContribution)
hardHighContributionFoldMatchesFullShell
  official shell pairContribution combine zero =
  cong (foldList combine zero)
    (hardHighContributionListMatchesFullShell
      official shell pairContribution)
