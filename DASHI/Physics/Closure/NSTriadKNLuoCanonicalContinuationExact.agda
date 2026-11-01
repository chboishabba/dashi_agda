module DASHI.Physics.Closure.NSTriadKNLuoCanonicalContinuationExact where

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
-- Final theorem surface for the non-circular, universe-correct localized Luo
-- route.  A concrete inhabitant of the remaining physical analytic inputs
-- yields the canonical cutset, condition (4.1), Section-4 terminal continuity
-- and continuation.  None of those conclusions is an input field.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceFaithfulRealizationExact as Realization
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority

canonicalCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  Realization.CanonicalSourceFaithfulAnalyticInputs data →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
canonicalCutset = Realization.canonicalSourceFaithfulCutset

condition41 :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Realization.CanonicalSourceFaithfulAnalyticInputs data) →
  Uniform.DissipationCriterion41
    (Realization.alphaAboveOneEntry inputs)
condition41 inputs =
  Canonical.canonicalDissipationCriterion41 (canonicalCutset inputs)

section4TerminalContinuity :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Realization.CanonicalSourceFaithfulAnalyticInputs data) →
  ModeEvolution.GronwallContinuityConclusion
    (Realization.section4Continuity inputs)
section4TerminalContinuity inputs =
  Canonical.canonicalSection4Continuity (canonicalCutset inputs)

continuation :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Realization.CanonicalSourceFaithfulAnalyticInputs data) →
  Authority.ContinuesBeyond
    (PreBudget.sourceCarrier data)
    (PreBudget.initial data)
    (PreBudget.terminal data)
continuation inputs =
  Canonical.continuationFromSourceFaithfulCutset (canonicalCutset inputs)

canonicalContinuationTheoremConstructed : Bool
canonicalContinuationTheoremConstructed = true

canonicalAnalyticInputsInhabited : Bool
canonicalAnalyticInputsInhabited = false

canonicalBKMExclusionProved : Bool
canonicalBKMExclusionProved = false

canonicalContinuationTheoremConstructedIsTrue :
  canonicalContinuationTheoremConstructed ≡ true
canonicalContinuationTheoremConstructedIsTrue = refl

canonicalAnalyticInputsInhabitedIsFalse :
  canonicalAnalyticInputsInhabited ≡ false
canonicalAnalyticInputsInhabitedIsFalse = refl

canonicalBKMExclusionProvedIsFalse :
  canonicalBKMExclusionProved ≡ false
canonicalBKMExclusionProvedIsFalse = refl
