module DASHI.Education.DigitalESDColladoAnalysisSetExact where

open import DASHI.Core.Prelude

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDStudyAnalysisSetRefinementExact as Analysis
import DASHI.Education.DigitalESDColladoLongitudinalClaimExact as Collado

------------------------------------------------------------------------
-- COLLADO ANALYSIS-SET REFINEMENT
--
-- Same study, distinct complete-case carriers:
--   * T0/T1 immediate analysis: 120 experimental + 137 control = 257;
--   * T2 one-year complete longitudinal set: 49 + 49 = 98.
-- The two Ns must not be flattened into one study-wide analysis population.
------------------------------------------------------------------------

colladoImmediateSet : Analysis.AnalysisSetReceipt
colladoImmediateSet = Analysis.analysis-set-receipt
  "collado-t0-t1-complete"
  (Ceiling.derivedNatWithSameObjectReceipt 257
    "120 experimental + 137 control complete T0/T1 cases"
    "same-object arithmetic from Participants and procedure")
  "10.1108/IJSHE-07-2021-0315; Participants and procedure"
  "baseline/immediate intervention-control analysis carrier"
  "source reports only students who completed the intervention and both T0/T1 questionnaires; approximately 18% of T0 respondents were excluded for dropout, missed workshop or missing T1"
  "120 experimental versus 137 non-participation control"
  "n=257 belongs to the immediate complete T0/T1 carrier and must not be reused as the one-year longitudinal complete-case n"

colladoT2Set : Analysis.AnalysisSetReceipt
colladoT2Set = Analysis.analysis-set-receipt
  "collado-t2-complete-longitudinal"
  (Ceiling.explicitlyReportedNat 98
    "49 experimental + 49 control completed T2")
  "10.1108/IJSHE-07-2021-0315; Participants and procedure; one-year follow-up"
  "one-year complete longitudinal carrier"
  "source reports 49 experimental and 49 control T2 completers; overall dropout 61.87% (n=159), final sample with all measures n=98"
  "49 experimental versus 49 control"
  "n=98 is the complete one-year longitudinal carrier; high attrition is part of the inferential boundary and cannot be erased by the precision of the reported mixed-effects CIs"

colladoAnalysisSets : Analysis.StudyAnalysisSetProfile
colladoAnalysisSets = Analysis.study-analysis-set-profile
  Collado.colladoLongitudinalProfile
  (colladoImmediateSet ∷ colladoT2Set ∷ [])
  "immediate and one-year complete-case carriers differ materially because longitudinal attrition reduces 257 T0/T1 cases to 98 participants with all measures"
  false refl

colladoAnalysisSetReading : String
colladoAnalysisSetReading =
  "Collado et al. provides a concrete longitudinal example of one study requiring more than one analysis-set receipt. The immediate T0/T1 carrier is 257 complete cases, while the one-year complete longitudinal carrier is 98. Exact 95% CIs remain valid source-reported model outputs for their estimands, but they do not repair the non-random allocation or 61.87% longitudinal dropout."
