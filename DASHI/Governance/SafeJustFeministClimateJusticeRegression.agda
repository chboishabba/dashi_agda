module DASHI.Governance.SafeJustFeministClimateJusticeRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.SafeJustFeministClimateJusticeBoundaryExact as Feminist
import DASHI.Governance.Kallis2025EvidenceAtlasExact as Kallis

countedOutputCollision :
  Feminist.countedOutput Feminist.noActivity ≡
  Feminist.countedOutput Feminist.unpaidCare
countedOutputCollision = Feminist.sameCountedOutput

countedOutputDoesNotRecoverProvisioning :
  Feminist.provisioningContribution Feminist.noActivity ≡
  Feminist.provisioningContribution Feminist.unpaidCare → ⊥
countedOutputDoesNotRecoverProvisioning =
  Feminist.countedOutputDoesNotRecoverProvisioning

responsibilityResidualIsNotDataResidual :
  Feminist.responsibilityImpactAsymmetryResidual ≡ Feminist.epistemicResidual → ⊥
responsibilityResidualIsNotDataResidual =
  Feminist.responsibilityResidualDiffersFromDataResidual

reviewEvidenceClassesDoNotCollapse :
  Kallis.allReviewClaimsShareOneEvidenceClass
    Kallis.canonicalKallisEvidenceAtlasBoundary ≡ false
reviewEvidenceClassesDoNotCollapse = refl

reviewDoesNotCloseNorthSouthFrontier :
  Kallis.globalNorthSouthQuestionIsClosedByTheReview
    Kallis.canonicalKallisEvidenceAtlasBoundary ≡ false
reviewDoesNotCloseNorthSouthFrontier = refl

reviewDoesNotCloseTransitionPolitics :
  Kallis.politicsOfTransitionIsClosedByTheReview
    Kallis.canonicalKallisEvidenceAtlasBoundary ≡ false
reviewDoesNotCloseTransitionPolitics = refl
