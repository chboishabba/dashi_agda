module DASHI.Law.LegalVisualisationIRProjectionBoundaryRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.LegalVisualisationIRProjectionBoundaryExact as Visual

boundary : Visual.LegalVisualisationIRBoundary
boundary =
  Visual.canonicalLegalVisualisationIRBoundary

sourceStaysProjection :
  Visual.sourceIsProjectionGraph boundary ≡ true
sourceStaysProjection =
  Visual.sourceIsProjectionGraphIsTrue boundary

visualisationInventsNoIdentity :
  Visual.visualisationMayInventSemanticIdentity boundary ≡ false
visualisationInventsNoIdentity =
  Visual.visualisationMayInventSemanticIdentityIsFalse boundary

visualisationCreatesNoAuthority :
  Visual.visualisationCreatesLegalAuthority boundary ≡ false
visualisationCreatesNoAuthority =
  Visual.visualisationCreatesLegalAuthorityIsFalse boundary

sankeyCarriesCounts :
  Visual.sankeyWeightMeansObservedCountOrTopologyCount boundary ≡ true
sankeyCarriesCounts =
  Visual.sankeyWeightMeansObservedCountOrTopologyCountIsTrue boundary

sankeyIsNotImportance :
  Visual.sankeyWeightMeansLegalImportance boundary ≡ false
sankeyIsNotImportance =
  Visual.sankeyWeightMeansLegalImportanceIsFalse boundary

sankeyIsNotAuthorityStrength :
  Visual.sankeyWeightMeansAuthorityStrength boundary ≡ false
sankeyIsNotAuthorityStrength =
  Visual.sankeyWeightMeansAuthorityStrengthIsFalse boundary

researchFlowShowsResiduals :
  Visual.researchFlowMayExposeReviewAndResidualStages boundary ≡ true
researchFlowShowsResiduals =
  Visual.researchFlowMayExposeReviewAndResidualStagesIsTrue boundary

renderChoiceDoesNotChangeSemantics :
  Visual.renderChoiceMayChangeDomainCommandSemantics boundary ≡ false
renderChoiceDoesNotChangeSemantics =
  Visual.renderChoiceMayChangeDomainCommandSemanticsIsFalse boundary
