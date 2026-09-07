module DASHI.Cognition.PNF.SensibLawFiniteLegalSearchEverything where

------------------------------------------------------------------------
-- FINITE LEGAL SEARCH CAPSTONE
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchProofPromotionExact as Promotion
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutProofPromotionExact as CutPromotion
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact as CutGuard
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardRegressionExact as CutRegression
import DASHI.Cognition.PNF.SensibLawFiniteLegalIssueProjectionRegressionExact as IssueRegression
import DASHI.Cognition.PNF.SensibLawAuthorityTransformationUniversalCutBridgeExact as CutBridge
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent
import DASHI.Cognition.PNF.SensibLawCullenClimateDistinguishingPromotionExact as CullenDistinction
import DASHI.Cognition.PNF.SensibLawPabaiTransformationPromotionExact as PabaiTransform
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen

------------------------------------------------------------------------
-- Positive route / proof promotion.
------------------------------------------------------------------------

maboExecutableAndProofRelevant :
  Search.ReachabilityPromotion
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboExecutableAndProofRelevant = Promotion.maboSearchPromotion

cullenExecutableAndProofRelevant :
  Search.ReachabilityPromotion
    1 Regression.cullenGraph Regression.cullenFacts Cullen.cullenDutyProposition
cullenExecutableAndProofRelevant = Promotion.cullenSearchPromotion

maboCutExecutableAndProofRelevant :
  Search.CutPromotion
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
    (Search.ruleKey Regression.maboSurvivalRule ∷ [])
maboCutExecutableAndProofRelevant = CutPromotion.maboCutPromotion

cullenCutExecutableAndProofRelevant :
  Search.CutPromotion
    1 Regression.cullenGraph Regression.cullenFacts Cullen.cullenDutyProposition
    (Search.ruleKey Regression.cullenDutyRule ∷ [])
cullenCutExecutableAndProofRelevant = CutPromotion.cullenCutPromotion

maboProofRelevantMinimalCut :
  Algebra.MinimalCut Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboProofRelevantMinimalCut = CutPromotion.maboSurvivalMinimalCut

cullenProofRelevantMinimalCut :
  Algebra.MinimalCut Regression.cullenGraph Regression.cullenFacts
    Cullen.cullenDutyProposition
cullenProofRelevantMinimalCut = CutPromotion.cullenDutyMinimalCut

------------------------------------------------------------------------
-- Issue-specific execution remains a projection of the universal graph.
------------------------------------------------------------------------

maboIssueProjectionKeepsRouteWhenRequiredRulesActive :
  Search.issueReachable
    2 Regression.maboGraph Regression.maboFacts
    IssueRegression.maboRecognitionIssue
    IssueRegression.maboFullExecutableProjection
  ≡ true
maboIssueProjectionKeepsRouteWhenRequiredRulesActive =
  IssueRegression.maboIssueReachableWithRequiredActiveRules

maboIssueProjectionCanBlockRouteWithoutDeletingUniversalRule :
  Search.issueReachable
    2 Regression.maboGraph Regression.maboFacts
    IssueRegression.maboRecognitionIssue
    IssueRegression.maboSurvivalOnlyProjection
  ≡ false
maboIssueProjectionCanBlockRouteWithoutDeletingUniversalRule =
  IssueRegression.maboIssueBlockedWhenRadicalTitleRuleProjectedOut

------------------------------------------------------------------------
-- Precedent distinguishing promotion.
------------------------------------------------------------------------

cullenClimateExecutableMismatch :
  Search.minimalDistinguishingCandidate
    Cullen.cullenDutyHolding Regression.climateComparatorCase
  ≡ Search.found Cullen.positiveOperationalAct
cullenClimateExecutableMismatch = CullenDistinction.executableFirstMissingFeature

cullenClimatePolicyDistinction :
  Precedent.PolicyMinimalDistinguishingSet
    CullenDistinction.cullenClimatePolicy
cullenClimatePolicyDistinction =
  CullenDistinction.cullenClimateMinimalDistinguishingSet

cullenClimateDistinctionStillPolicyIndexed :
  CullenDistinction.FixtureCorrespondencePolicyIsBindingHighCourtLaw → ⊥
cullenClimateDistinctionStillPolicyIndexed =
  CullenDistinction.fixturePolicyDoesNotBecomeBindingLaw

------------------------------------------------------------------------
-- Negative current route / typed repair promotion.
------------------------------------------------------------------------

pabaiCurrentRouteStillUnreachable :
  Search.reachable 1 Regression.pabaiGraph Regression.pabaiFacts
    Negligence.dutyProposition ≡ false
pabaiCurrentRouteStillUnreachable = Regression.pabaiComputedCurrentlyUnreachable

pabaiDoesNotProduceVacuousEmptyCut :
  CutGuard.searchReachableMinimalCut
    1 Regression.pabaiGraph Regression.pabaiFacts Negligence.dutyProposition
  ≡ Search.notFound
pabaiDoesNotProduceVacuousEmptyCut = CutRegression.pabaiGuardedCutSearch

pabaiRepairCandidateFound :
  Search.firstReopeningTransformation 1 Negligence.dutyProposition
    (Regression.pabaiReformulationCandidate ∷ [])
  ≡ Search.found Regression.pabaiReformulationCandidate
pabaiRepairCandidateFound = Regression.pabaiTransformationSearch

pabaiRepairCandidateTypedAndProofRelevant :
  Search.TransformationPromotion
    1 Negligence.dutyProposition Regression.pabaiReformulationCandidate
pabaiRepairCandidateTypedAndProofRelevant =
  PabaiTransform.pabaiTransformationPromotion

pabaiTransformationStillNeedsLegalAvailability :
  PabaiTransform.PabaiTransformationAvailableUnderControllingAuthorities → ⊥
pabaiTransformationStillNeedsLegalAvailability =
  PabaiTransform.pabaiLegalAvailabilityStillOpen

------------------------------------------------------------------------
-- Computation status.
------------------------------------------------------------------------

maboCutSearchStatus :
  CutBridge.maboCutStatus ≡ CutBridge.proofRelevantCutComputed
maboCutSearchStatus = refl

cullenCutSearchStatus :
  CutBridge.cullenCutStatus ≡ CutBridge.proofRelevantCutComputed
cullenCutSearchStatus = refl

pabaiCutSearchStatus :
  CutBridge.pabaiCutStatus ≡ CutBridge.finiteExecutableCandidateComputed
pabaiCutSearchStatus = refl

pabaiTransformationSearchStatus :
  CutBridge.pabaiTransformationStatus
  ≡ CutBridge.typedTransformationReopensGoal
pabaiTransformationSearchStatus = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteSearchAggregateMeansCorpusComplete : Set where
data ExecutableCounterfactualMeansLegallyAvailable : Set where

data PolicyDistinctionMeansUniversalDistinction : Set where

finiteSearchDoesNotClaimCorpusCompleteness :
  FiniteSearchAggregateMeansCorpusComplete → ⊥
finiteSearchDoesNotClaimCorpusCompleteness ()

counterfactualSearchDoesNotCreateLegalAvailability :
  ExecutableCounterfactualMeansLegallyAvailable → ⊥
counterfactualSearchDoesNotCreateLegalAvailability ()

policyDistinctionDoesNotBecomeUniversal :
  PolicyDistinctionMeansUniversalDistinction → ⊥
policyDistinctionDoesNotBecomeUniversal ()
