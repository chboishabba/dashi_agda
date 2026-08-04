module DASHI.Physics.Closure.NSTriadKNLuoNonCircularCanonicalContinuationExact where

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
-- Export the final non-circular theorem chain.  The input package contains
-- pre-budget physical data plus the remaining analytic identifications and
-- estimates.  It does not contain terminalBudgetAt, localized-gradient
-- smallness, shell decay, condition (4.1), Section-4 terminal continuity, or
-- continuation.  Each of those is constructed downstream.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoOfficialSourceFaithfulRealizationExact as Realization
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority

canonicalSourceFaithfulCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  Realization.OfficialSourceFaithfulNonlinearInputs data →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
canonicalSourceFaithfulCutset =
  Realization.officialCanonicalSourceFaithfulCutset

canonicalCondition41 :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Realization.OfficialSourceFaithfulNonlinearInputs data) →
  Uniform.DissipationCriterion41
    (Realization.alphaAboveOneEntry inputs)
canonicalCondition41 inputs =
  Canonical.canonicalDissipationCriterion41
    (canonicalSourceFaithfulCutset inputs)

canonicalSection4TerminalContinuity :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Realization.OfficialSourceFaithfulNonlinearInputs data) →
  ModeEvolution.GronwallContinuityConclusion
    (Realization.officialSection4Continuity inputs)
canonicalSection4TerminalContinuity inputs =
  Canonical.canonicalSection4Continuity
    (canonicalSourceFaithfulCutset inputs)

canonicalLuoContinuation :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Realization.OfficialSourceFaithfulNonlinearInputs data) →
  Authority.ContinuesBeyond
    (PreBudget.sourceCarrier data)
    (PreBudget.initial data)
    (PreBudget.terminal data)
canonicalLuoContinuation inputs =
  Canonical.continuationFromSourceFaithfulCutset
    (canonicalSourceFaithfulCutset inputs)

nonCircularCanonicalContinuationTheoremConstructed : Bool
nonCircularCanonicalContinuationTheoremConstructed = true

canonicalPhysicalAnalyticInputsInhabited : Bool
canonicalPhysicalAnalyticInputsInhabited = false

canonicalBKMExclusionProved : Bool
canonicalBKMExclusionProved = false

nonCircularCanonicalContinuationTheoremConstructedIsTrue :
  nonCircularCanonicalContinuationTheoremConstructed ≡ true
nonCircularCanonicalContinuationTheoremConstructedIsTrue = refl

canonicalPhysicalAnalyticInputsInhabitedIsFalse :
  canonicalPhysicalAnalyticInputsInhabited ≡ false
canonicalPhysicalAnalyticInputsInhabitedIsFalse = refl

canonicalBKMExclusionProvedIsFalse :
  canonicalBKMExclusionProved ≡ false
canonicalBKMExclusionProvedIsFalse = refl
