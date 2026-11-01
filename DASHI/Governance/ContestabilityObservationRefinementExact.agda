module DASHI.Governance.ContestabilityObservationRefinementExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author: Helen Nissenbaum.
-- Title: "Privacy as Contextual Integrity".
-- Venue: Washington Law Review 79(1):119--158 (2004).
-- DOI: no DOI listed in the cited journal record.
--
-- Nissenbaum supplies context-relative information-flow vocabulary only.  The
-- exact observation-refinement theorem is the generic DASHI core generalized
-- from PR #549's defensive side-channel formalism.
--
-- Governance reading: an explanation/appeal coordinate can refine a coarse
-- decision-output equivalence when it distinguishes two cases previously shown
-- identically to the affected subject.  Such refinement improves available
-- distinction in the formal sense; it does not by itself establish fairness,
-- legal sufficiency, or that the extra disclosure is normatively appropriate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.ObservationLanguageRefinementExact as Observation
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

------------------------------------------------------------------------
-- Turn an institutional/disclosed channel plus one explanation coordinate into
-- the generic observation-language refinement carrier.
------------------------------------------------------------------------

record ExplanationRefinementChannel
  (L : Legibility.LegibilityChannel) : Set₁ where
  constructor explanationRefinementChannel
  field
    ExplanationView : Set
    explain : Legibility.Subject L → ExplanationView

open ExplanationRefinementChannel public

asObservationLanguage :
  ∀ {L : Legibility.LegibilityChannel} →
  ExplanationRefinementChannel L →
  Observation.ObservationLanguage
asObservationLanguage {L = L} explanation =
  Observation.observationLanguage
    (Legibility.Subject L)
    (Legibility.SubjectView L)
    (ExplanationView explanation)
    (Legibility.subjectView L)
    (explain explanation)

record ExplanationSeparatesCollapsedCases
  {L : Legibility.LegibilityChannel}
  (E : ExplanationRefinementChannel L) : Set₁ where
  constructor explanationSeparatesCollapsedCases
  field
    left right : Legibility.Subject L
    sameDisclosedView :
      Legibility.subjectView L left ≡ Legibility.subjectView L right
    explanationDiffers : explain E left ≡ explain E right → ⊥

open ExplanationSeparatesCollapsedCases public

explanationSplitWitness :
  ∀ {L : Legibility.LegibilityChannel}
    {E : ExplanationRefinementChannel L} →
  ExplanationSeparatesCollapsedCases E →
  Observation.LanguageSplitWitness (asObservationLanguage E)
explanationSplitWitness split =
  Observation.languageSplitWitness
    (left split)
    (right split)
    (sameDisclosedView split)
    (explanationDiffers split)

explanationStrictlyRefinesSubjectObservation :
  ∀ {L : Legibility.LegibilityChannel}
    {E : ExplanationRefinementChannel L} →
  ExplanationSeparatesCollapsedCases E →
  Observation.StrictObservationRefinement (asObservationLanguage E)
explanationStrictlyRefinesSubjectObservation split =
  Observation.strictObservationRefinement (explanationSplitWitness split)

refinedObservationRejectsCollapsedEquivalence :
  ∀ {L : Legibility.LegibilityChannel}
    {E : ExplanationRefinementChannel L}
    (split : ExplanationSeparatesCollapsedCases E) →
  Observation.ExtendedEquivalent
    (asObservationLanguage E)
    (left split)
    (right split) → ⊥
refinedObservationRejectsCollapsedEquivalence split =
  Observation.strictRefinementRejectsOldCollision
    (explanationStrictlyRefinesSubjectObservation split)

------------------------------------------------------------------------
-- Finite regression on the existing asymmetric-legibility example.  The base
-- public view is constant, while an explanation coordinate exposes the exact
-- internal distinction between the two cases.
------------------------------------------------------------------------

data Explanation2 : Set where explanation0 explanation1 : Explanation2

finiteExplanation : Legibility.Case2 → Explanation2
finiteExplanation Legibility.case0 = explanation0
finiteExplanation Legibility.case1 = explanation1

finiteExplanationChannel :
  ExplanationRefinementChannel Legibility.finiteLegibilityChannel
finiteExplanationChannel =
  explanationRefinementChannel Explanation2 finiteExplanation

finiteExplanationSplit :
  ExplanationSeparatesCollapsedCases finiteExplanationChannel
finiteExplanationSplit =
  explanationSeparatesCollapsedCases
    Legibility.case0
    Legibility.case1
    refl
    (λ ())

finiteExplanationStrictlyRefines :
  Observation.StrictObservationRefinement
    (asObservationLanguage finiteExplanationChannel)
finiteExplanationStrictlyRefines =
  explanationStrictlyRefinesSubjectObservation finiteExplanationSplit

------------------------------------------------------------------------
-- Boundary and provenance receipt.
------------------------------------------------------------------------

record ContestabilityObservationBoundary : Set where
  constructor contestabilityObservationBoundary
  field
    explanationCanRefineCoarseDecisionView : Bool
    explanationRefinementAutomaticallyFair : Bool
    explanationRefinementAutomaticallyLegal : Bool
    everyExtraDisclosureIsLegitimate : Bool
    strictRefinementNeedsConcreteSeparatingWitness : Bool

canonicalContestabilityObservationBoundary : ContestabilityObservationBoundary
canonicalContestabilityObservationBoundary =
  contestabilityObservationBoundary true false false false true

record ContestabilityObservationReceipt : Set where
  constructor contestabilityObservationReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : ContestabilityObservationBoundary

canonicalContestabilityObservationReceipt : ContestabilityObservationReceipt
canonicalContestabilityObservationReceipt =
  contestabilityObservationReceipt
    (Sources.nissenbaumContextualIntegrity ∷ Sources.blackwellExperimentComparison ∷ [])
    canonicalContestabilityObservationBoundary
