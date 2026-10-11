module DASHI.Biology.IBSGutBrainImmuneSystemsRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Biology.IBSGutBrainImmuneSystemsHyperfabricExact as IBS

boundaryRetainsRecurrentGraph :
  IBS.IBSWholeSystemBoundary.recurrentBidirectionalGraphRetained
    IBS.canonicalIBSWholeSystemBoundary ≡ true
boundaryRetainsRecurrentGraph = refl

boundaryRejectsInflammationMasterCause :
  IBS.IBSWholeSystemBoundary.inflammationIsUniversalMasterCause
    IBS.canonicalIBSWholeSystemBoundary ≡ false
boundaryRejectsInflammationMasterCause = refl

boundaryRejectsHistamineMasterCause :
  IBS.IBSWholeSystemBoundary.histamineIsUniversalMasterCause
    IBS.canonicalIBSWholeSystemBoundary ≡ false
boundaryRejectsHistamineMasterCause = refl

boundaryRetainsLocalVsWholeSystemSeparation :
  IBS.IBSWholeSystemBoundary.localMechanismDoesNotEqualWholeSystemClosure
    IBS.canonicalIBSWholeSystemBoundary ≡ true
boundaryRetainsLocalVsWholeSystemSeparation = refl

inflammationNotMasterCauseRegression :
  IBS.InflammationIsCompleteIBSCausePermission → ⊥
inflammationNotMasterCauseRegression = IBS.inflammationDoesNotExhaustIBS

histamineNotMasterCauseRegression :
  IBS.HistamineIsCompleteIBSCausePermission → ⊥
histamineNotMasterCauseRegression = IBS.histamineDoesNotExhaustIBS

quailLocalInterventionRegression :
  IBS.QuailLocalFibreEqualsWholeSystemTherapyPermission → ⊥
quailLocalInterventionRegression = IBS.quailLocalFibreDoesNotEqualWholeSystemTherapy

feedbackGraphMembershipRegression :
  IBS.canonicalIBSFeedbackGraph ≡
    IBS.microbiomeImmuneEdge ∷ IBS.immuneSensoryEdge ∷ IBS.barrierImmuneEdge ∷
    IBS.allostaticGutEdge ∷ IBS.gutCentralEdge ∷ IBS.dietMicrobiomeBarrierEdge ∷
    IBS.neurochemicalSystemEdge ∷ []
feedbackGraphMembershipRegression = refl

microbiomeImmuneNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.microbiomeImmuneEdge ≡ false
microbiomeImmuneNotUniversal = refl

immuneSensoryNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.immuneSensoryEdge ≡ false
immuneSensoryNotUniversal = refl

barrierImmuneNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.barrierImmuneEdge ≡ false
barrierImmuneNotUniversal = refl

allostaticGutNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.allostaticGutEdge ≡ false
allostaticGutNotUniversal = refl

gutCentralNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.gutCentralEdge ≡ false
gutCentralNotUniversal = refl

dietMicrobiomeNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.dietMicrobiomeBarrierEdge ≡ false
dietMicrobiomeNotUniversal = refl

neurochemicalSystemNotUniversal :
  IBS.IBSSystemEdge.universalCausalityClaimed IBS.neurochemicalSystemEdge ≡ false
neurochemicalSystemNotUniversal = refl
