module DASHI.Wikimedia.MaboResidualDrivenWorldExpansionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Wikimedia.MaboResidualDrivenWorldExpansionExact as Target

checkTargetNovelObjects : Target.targetNovelObjects ≡ 100
checkTargetNovelObjects = Target.targetNovelObjectsIs100

checkHopDepthIsNotTarget : Target.hopDepthIsNotTarget Target.canonicalWorldExpansionBoundary ≡ true
checkHopDepthIsNotTarget = Target.hopDepthIsNotTargetTrue

checkLegalFirstResidualIndexed :
  Target.legalFirstIsResidualIndexed Target.canonicalWorldExpansionBoundary ≡ true
checkLegalFirstResidualIndexed = Target.legalFirstIsResidualIndexedTrue

checkLegalFirstNotLegalOnly :
  Target.legalFirstMeansLegalOnly Target.canonicalWorldExpansionBoundary ≡ false
checkLegalFirstNotLegalOnly = Target.legalFirstMeansLegalOnlyFalse

checkFirstLinkNotController :
  Target.firstLinkControlsSemantics Target.canonicalWorldExpansionBoundary ≡ false
checkFirstLinkNotController = Target.firstLinkControlsSemanticsFalse

checkReachabilityNotAdmission :
  Target.reachabilityCreatesAdmission Target.canonicalWorldExpansionBoundary ≡ false
checkReachabilityNotAdmission = Target.reachabilityCreatesAdmissionFalse

checkQidNotAuthority :
  Target.qidCreatesAuthority Target.canonicalWorldExpansionBoundary ≡ false
checkQidNotAuthority = Target.qidCreatesAuthorityFalse

checkAdmissionNotTruth :
  Target.admissionCreatesClaimTruth Target.canonicalWorldExpansionBoundary ≡ false
checkAdmissionNotTruth = Target.admissionCreatesClaimTruthFalse
