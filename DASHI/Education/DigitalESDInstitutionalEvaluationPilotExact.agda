module DASHI.Education.DigitalESDInstitutionalEvaluationPilotExact where

open import DASHI.Core.Prelude

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDPrimarySourceMethodologyAtlasExact as Primary

------------------------------------------------------------------------
-- INSTITUTIONAL / SYSTEM-LEVEL EVALUATION PILOT
--
-- Canonical source:
--   UNECE ECE/CEP/AC.13/2026/3
--   "Learning from each other: achievements, challenges and ways forward —
--    Fifth evaluation report of the Strategy for Education for Sustainable
--    Development"
--
-- The analytic carrier is a regional corpus of national implementation reports,
-- not a human participant sample. The profile therefore exercises the same
-- claim-ceiling machinery without pretending every reported n is a participant n.
------------------------------------------------------------------------

uneceFifthEvaluationPilotProfile : Ceiling.StudyClaimProfile
uneceFifthEvaluationPilotProfile = Ceiling.study-claim-profile
  "unece-2026-fifth-esd-evaluation"
  Primary.uneceFifthESDEvaluationSource
  "candidate regional institutional implementation-synthesis evidence"
  "ECE/CEP/AC.13/2026/3; Executive Summary; Introduction; regional synthesis"
  "regional evaluation of UNECE ESD Strategy implementation for 2021-2025 based on 31 national implementation reports, complemented by qualitative analysis and thematic synthesis"
  (Ceiling.sourceReportedDesignUnmapped
    "regional institutional evaluation using national implementation reports and qualitative thematic synthesis"
    "the analytic carrier is national implementation reporting across ECE member States, not an intervention cohort; no participant-trial design class is manufactured")
  "31 national implementation reports submitted by ECE member States for the fifth evaluation cycle; country self-assessments are synthesized at regional level"
  (Ceiling.explicitlyReportedNat 31 "national implementation reports underlying the fifth regional evaluation")
  (Ceiling.explicitlyReportedNat 31 "national-report corpus entering the regional qualitative/thematic synthesis")
  "not applicable: national reports are not treatment-assigned"
  "cross-country and cross-theme regional synthesis; no untreated jurisdictional control group"
  "national implementation reports, qualitative analysis and thematic synthesis of policy integration, curriculum, educator learning, digital access/platform use, governance, monitoring and implementation challenges"
  "not participant attrition; reporting coverage and self-reporting completeness are institutional-source limitations rather than human dropout"
  "country self-assessment, policy/reporting structures and regional heterogeneity remain potential reporting/context biases; no causal confounding adjustment exists at regional evaluation level"
  "common UNECE strategy/reporting framework supports cross-country synthesis, but implementation/reporting practices remain heterogeneous"
  "multiple themes and country reports are synthesized descriptively; no participant-level multiplicity-testing surface is applicable"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "regional implementation synthesis reports sustained ESD commitment and progress in policy integration, curriculum development and professional learning, alongside uneven digital infrastructure/access, educator competence, governance, monitoring and outcome-assessment capacity"
    "Executive Summary / thematic synthesis"
    "these are regional institutional implementation findings derived from national reports, not effect sizes for a named educational intervention")
  (Ceiling.reported-surface Ceiling.notReported
    "no intervention-effect confidence interval applies to the regional national-report synthesis"
    "institutional evaluation"
    "uncertainty arises from report coverage, self-assessment, thematic synthesis and cross-country heterogeneity rather than a participant sampling CI")
  "implementation phase 2021-2025, with fifth evaluation report issued March 2026"
  "UNECE/ECE regional member-State reporting population; transfer to a particular school, learner population, intervention or non-ECE jurisdiction requires separate evidence"
  (Ceiling.epistemicRoleNotApplicable
    "the study-level object is a regional synthesis of national implementation reports; no single participant epistemic role is applicable")
  Ceiling.reviewSynthesisClaim
  "supports regional claims about reported ESD implementation progress, persistent structural gaps, digital-access/platform expansion and continuing monitoring/outcome-assessment challenges; does not identify local learner effects, intervention causality or automatic digital-ESD transformation"
  "national implementation reports include self-reporting/institutional-reporting limitations; regional synthesis is not independent measurement of every country claim; cross-country heterogeneity remains material; policy/input progress does not establish learner outcomes or system transformation"

institutionalEvaluationReading : String
institutionalEvaluationReading =
  "The UNECE fifth evaluation demonstrates that the claim-ceiling schema is carrier-neutral: 31 is the size of the national-report analytic corpus, not a participant count. Institutional self-report and thematic synthesis can support bounded regional implementation findings while leaving intervention causality, learner outcomes, independent verification of every national claim and local transport unpaid."
