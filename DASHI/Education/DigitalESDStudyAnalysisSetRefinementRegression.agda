module DASHI.Education.DigitalESDStudyAnalysisSetRefinementRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)

import DASHI.Education.DigitalESDStudyAnalysisSetRefinementExact as Refine
import DASHI.Education.DigitalESDStudyClaimPilotExtensionExact as Extension
import DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact as Quant
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact as RCT
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling

fishlockParentRegression :
  Refine.StudyAnalysisSetProfile.parentStudy Refine.fishlockAnalysisSets
  ≡ Extension.fishlockPilotProfile
fishlockParentRegression = refl

greenParentRegression :
  Refine.StudyAnalysisSetProfile.parentStudy Refine.greenAnalysisSets
  ≡ RCT.greenMolloyDugganPilotProfile
greenParentRegression = refl

brasslerParentRegression :
  Refine.StudyAnalysisSetProfile.parentStudy Refine.brasslerAnalysisSets
  ≡ Quant.brasslerPilotProfile
brasslerParentRegression = refl

refinementRequiredRegression :
  Refine.AnalysisSetRefinementBoundary.onePaperMayHaveMultipleAnalysisSets
    Refine.canonicalAnalysisSetRefinementBoundary
  ≡ true
refinementRequiredRegression = refl
