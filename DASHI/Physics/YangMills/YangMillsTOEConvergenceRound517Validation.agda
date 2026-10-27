{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsTOEConvergenceRound517Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound517Exact as TOE
open import DASHI.Physics.YangMills.CompactLieProofLevel

sourceAnalysisResidualIsFifteen :
  TOE.toeSourceAnalysisResidualCount ≡ 15
sourceAnalysisResidualIsFifteen = refl

sourceLiteralAttachmentResidualIsEighteen :
  TOE.toeSourceLiteralAttachmentResidualCount ≡ 18
sourceLiteralAttachmentResidualIsEighteen = refl

endpointSemanticResidualIsTwentyOne :
  TOE.toeEndpointSemanticResidualCount ≡ 21
endpointSemanticResidualIsTwentyOne = refl

totalResidualIsFiftyFour :
  TOE.toeTotalResidualCount ≡ 54
totalResidualIsFiftyFour = refl

regularESourceClosureRemainsOpen :
  TOE.toeRegularEPhysicalSourceClosure ≡ false
regularESourceClosureRemainsOpen =
  TOE.toeRegularEPhysicalSourceClosureIsFalse

stressRouteDoesNotPromoteClay :
  TOE.toeStressRouteClayPromotion ≡ false
stressRouteDoesNotPromoteClay =
  TOE.toeStressRouteClayPromotionIsFalse

allClayProvidersNotDerived :
  TOE.toeAllClayProvidersDerivedInRepo ≡ false
allClayProvidersNotDerived =
  TOE.toeAllClayProvidersDerivedInRepoIsFalse

clayStatementBoundaryNotDischarged :
  TOE.toeClayStatementBoundaryDischarged ≡ false
clayStatementBoundaryNotDischarged =
  TOE.toeClayStatementBoundaryDischargedIsFalse

clayYangMillsNotPromoted :
  TOE.toeClayYangMillsPromoted ≡ false
clayYangMillsNotPromoted =
  TOE.toeClayYangMillsPromotedIsFalse

toeConvergenceCompilerMachineChecked :
  TOE.round517TOEConvergenceCompilerLevel ≡ machineChecked
toeConvergenceCompilerMachineChecked = refl
