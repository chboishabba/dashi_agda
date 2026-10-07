module DASHI.Biology.IBSGutBrainImmuneSystemsRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as IBS

wholeSystemBoundaryRegression :
  IBS.canonicalIBSWholeSystemBoundary ≡ IBS.canonicalIBSWholeSystemBoundary
wholeSystemBoundaryRegression = refl

inflammationNotMasterCauseRegression :
  IBS.InflammationIsCompleteIBSCausePermission → ⊥
inflammationNotMasterCauseRegression = IBS.inflammationDoesNotExhaustIBS

histamineNotMasterCauseRegression :
  IBS.HistamineIsCompleteIBSCausePermission → ⊥
histamineNotMasterCauseRegression = IBS.histamineDoesNotExhaustIBS

quailLocalInterventionRegression :
  IBS.QuailLocalFibreEqualsWholeSystemTherapyPermission → ⊥
quailLocalInterventionRegression = IBS.quailLocalFibreDoesNotEqualWholeSystemTherapy

feedbackGraphRegression :
  IBS.canonicalIBSFeedbackGraph ≡ IBS.canonicalIBSFeedbackGraph
feedbackGraphRegression = refl
