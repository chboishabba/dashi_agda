module DASHI.Core.OrthogonalStatusDecompositionAuditRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Core.OrthogonalStatusDecompositionAuditExact as Audit

archaeologyIsPaymentAxis :
  Audit.archaeologyPaymentStatusIsPurePaymentAxis
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ true
archaeologyIsPaymentAxis = refl

riemannStatusMixesAxes :
  Audit.riemannPaymentStatusIsPurePaymentAxis
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
riemannStatusMixesAxes = refl

governanceStatusMixesPaymentAndResidual :
  Audit.governancePropositionStatusIsPurePaymentAxis
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
governanceStatusMixesPaymentAndResidual = refl

sameEnumNameDoesNotFixMeaning :
  Audit.sameEnumNameDeterminesSemanticAxis
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
sameEnumNameDoesNotFixMeaning = refl

megaEnumNotYetPromoted :
  Audit.canonicalFiveAxisProductReadyForPromotion
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
megaEnumNotYetPromoted = refl

representativeAuditSupportsFactorisation :
  Audit.representativeAuditSupportsOrthogonalFactorisation
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ true
representativeAuditSupportsFactorisation = refl

multilingualSurfaceAssertionIsIndependent :
  Audit.multilingualSurfaceAssertionIsIndependentCoordinate
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ true
multilingualSurfaceAssertionIsIndependent = refl

fiveStatusAxesDoNotCaptureSurfaceSemanticsAlone :
  Audit.fiveStatusAxesSufficientForMultilingualSurfaceSemantics
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
fiveStatusAxesDoNotCaptureSurfaceSemanticsAlone = refl

sharedQidDoesNotPayTranslationEquivalence :
  Audit.sharedQidPaysTranslationEquivalence
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
sharedQidDoesNotPayTranslationEquivalence = refl

semanticPropagationDoesNotAssertTargetSurface :
  Audit.semanticPropagationAssertsTargetSurface
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
semanticPropagationDoesNotAssertTargetSurface = refl

simpleWikiRemainsPeerSurface :
  Audit.simpleWikiPresumedEnglishSubset
    Audit.canonicalOrthogonalStatusAuditBoundary ≡ false
simpleWikiRemainsPeerSurface = refl
