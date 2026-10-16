module DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.RationalAlbertF4ClassificationInstantiationBoundaryExact as C

allLocalExceptionalHypothesesOwned :
  C.allConcreteExceptionalHypothesesOwned C.canonicalBoundary ≡ true
allLocalExceptionalHypothesesOwned = refl

modernRingLevelClassificationSourceLocated :
  C.modernRingLevelClassificationSourceLocated C.canonicalBoundary ≡ true
modernRingLevelClassificationSourceLocated = refl

classificationNoLongerSourceDiscovery :
  C.remainingClassificationIsSourceDiscovery C.canonicalBoundary ≡ false
classificationNoLongerSourceDiscovery = refl

classificationStillQFormAndGroupLevel :
  C.remainingClassificationIsQFormAndGroupLevel C.canonicalBoundary ≡ true
classificationStillQFormAndGroupLevel = refl

normUnitRigidityLocatedCrossKernel :
  C.normUnitRigiditySourceWrittenCrossKernel C.canonicalBoundary ≡ true
normUnitRigidityLocatedCrossKernel = refl

unitStabilizerStructurallyReduced :
  C.unitStabilizerJordanEqualityStructurallyReduced C.canonicalBoundary ≡ true
unitStabilizerStructurallyReduced = refl

crossKernelAuthorityNotTransferred :
  C.normUnitRigidityAgdaAuthorityPaid C.canonicalBoundary ≡ false
crossKernelAuthorityNotTransferred = refl

exactRealPlaceTraceDiagnosticPaid :
  C.exactPositiveTraceFormRealPlaceDiagnosticPaid C.canonicalBoundary ≡ true
exactRealPlaceTraceDiagnosticPaid = refl

compactRealPlaceSuggested :
  C.compactRealPlaceSuggested C.canonicalBoundary ≡ true
compactRealPlaceSuggested = refl

compactRealPlaceNotYetClassified :
  C.compactRealPlaceClassificationPaid C.canonicalBoundary ≡ false
compactRealPlaceNotYetClassified = refl

realPlaceDoesNotClassifyGlobalQForm :
  C.realPlaceDiagnosticClassifiesOriginalQForm C.canonicalBoundary ≡ false
realPlaceDoesNotClassifyGlobalQForm = refl

originalQFormClassificationStillOpen :
  C.actualQFormGroupInstantiationInhabited C.canonicalBoundary ≡ false
originalQFormClassificationStillOpen = refl
