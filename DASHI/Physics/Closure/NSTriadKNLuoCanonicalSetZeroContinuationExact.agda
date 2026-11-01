module DASHI.Physics.Closure.NSTriadKNLuoCanonicalSetZeroContinuationExact where

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
-- Final universe-safe theorem surface on the repository's selected Set0
-- periodic NS carriers. A concrete inhabitant of the remaining analytic inputs
-- produces the canonical cutset, condition (4.1), Section-4 terminal
-- continuity and continuation. None of those conclusions is an input field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSetZeroAnalyticInputsExact as Inputs
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority

canonicalCutset :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  Inputs.CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
canonicalCutset = Inputs.canonicalSourceFaithfulCutset

condition41 :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Inputs.CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
  Uniform.DissipationCriterion41
    (Inputs.alphaAboveOneEntry inputs)
condition41 inputs =
  Canonical.canonicalDissipationCriterion41 (canonicalCutset inputs)

section4TerminalContinuity :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Inputs.CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
  ModeEvolution.GronwallContinuityConclusion
    (Inputs.section4Continuity inputs)
section4TerminalContinuity inputs =
  Canonical.canonicalSection4Continuity (canonicalCutset inputs)

continuation :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : Inputs.CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
  Authority.ContinuesBeyond
    (PreBudget.sourceCarrier data)
    (PreBudget.initial data)
    (PreBudget.terminal data)
continuation inputs =
  Canonical.continuationFromSourceFaithfulCutset (canonicalCutset inputs)

canonicalSetZeroContinuationConstructed : Bool
canonicalSetZeroContinuationConstructed = true

canonicalSetZeroAnalyticInputsInhabited : Bool
canonicalSetZeroAnalyticInputsInhabited = false

canonicalBKMExclusionProved : Bool
canonicalBKMExclusionProved = false

canonicalSetZeroContinuationConstructedIsTrue :
  canonicalSetZeroContinuationConstructed ≡ true
canonicalSetZeroContinuationConstructedIsTrue = refl

canonicalSetZeroAnalyticInputsInhabitedIsFalse :
  canonicalSetZeroAnalyticInputsInhabited ≡ false
canonicalSetZeroAnalyticInputsInhabitedIsFalse = refl

canonicalBKMExclusionProvedIsFalse :
  canonicalBKMExclusionProved ≡ false
canonicalBKMExclusionProvedIsFalse = refl
