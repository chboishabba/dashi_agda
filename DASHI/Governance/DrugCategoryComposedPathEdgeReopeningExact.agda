module DASHI.Governance.DrugCategoryComposedPathEdgeReopeningExact where

open import DASHI.Core.Prelude

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.DrugCategoryPartialTranslationPathCategoryExact as Path
import DASHI.Governance.DrugCategoryTranslationEdgeIndexedReopeningExact as Edge

------------------------------------------------------------------------
-- COMPOSED-PATH EDGE MEMBERSHIP -> SELECTIVE REOPENING
--
-- This owner removes the remaining manual seam between the translation path
-- calculus and reverse dependency.  Membership is now proved against the actual
-- ordered TranslationPath used by a maintained consequence.
------------------------------------------------------------------------

data LegHasEdge :
    ∀ {source target} →
    Path.TranslationLeg source target →
    Edge.TranslationEdgeInstance → Set where
  stateClinicalLegHasEdge :
    LegHasEdge Path.stateClinicalLeg Edge.stateToClinicalEdge
  clinicalLivedLegHasEdge :
    LegHasEdge Path.clinicalLivedLeg Edge.clinicalToLivedEdge
  indigenousCommercialLegHasEdge :
    LegHasEdge Path.indigenousCommercialLeg Edge.indigenousToCommercialEdge

data EdgeOccursInPath
    (edge : Edge.TranslationEdgeInstance)
    : ∀ {source target} → Path.TranslationPath source target → Set where
  edgeHere :
    ∀ {source middle target}
      {leg : Path.TranslationLeg source middle}
      {rest : Path.TranslationPath middle target} →
    LegHasEdge leg edge →
    EdgeOccursInPath edge (Path.pathStep leg rest)
  edgeThere :
    ∀ {source middle target}
      {leg : Path.TranslationLeg source middle}
      {rest : Path.TranslationPath middle target} →
    EdgeOccursInPath edge rest →
    EdgeOccursInPath edge (Path.pathStep leg rest)

stateClinicalOccursInComposedLivedPath :
  EdgeOccursInPath Edge.stateToClinicalEdge Path.stateClinicalLivedPath
stateClinicalOccursInComposedLivedPath =
  edgeHere stateClinicalLegHasEdge

clinicalLivedOccursInComposedLivedPath :
  EdgeOccursInPath Edge.clinicalToLivedEdge Path.stateClinicalLivedPath
clinicalLivedOccursInComposedLivedPath =
  edgeThere (edgeHere clinicalLivedLegHasEdge)

clinicalLivedDoesNotOccurInStateClinicalOnlyPath :
  EdgeOccursInPath
    Edge.clinicalToLivedEdge
    (Path.pathStep Path.stateClinicalLeg Path.pathId) → ⊥
clinicalLivedDoesNotOccurInStateClinicalOnlyPath
  (edgeHere ())
clinicalLivedDoesNotOccurInStateClinicalOnlyPath
  (edgeThere ())

------------------------------------------------------------------------
-- Maintained consequences carry the exact path whose translations justified
-- them.  This makes dependency language generated from path membership rather
-- than from broad artifact class.
------------------------------------------------------------------------

data MaintainedTranslationConsequence : Set where
  clinicalSafetyMaintained
  livedSubjectMaintained
  sovereignCommercialExtractionMaintained
  : MaintainedTranslationConsequence

maintainedPathSource : MaintainedTranslationConsequence → Atlas.CategoryChart
maintainedPathSource clinicalSafetyMaintained = Atlas.stateLegalChart
maintainedPathSource livedSubjectMaintained = Atlas.stateLegalChart
maintainedPathSource sovereignCommercialExtractionMaintained = Atlas.indigenousSovereignChart

maintainedPathTarget : MaintainedTranslationConsequence → Atlas.CategoryChart
maintainedPathTarget clinicalSafetyMaintained = Atlas.biomedicalChart
maintainedPathTarget livedSubjectMaintained = Atlas.livedSubjectChart
maintainedPathTarget sovereignCommercialExtractionMaintained = Atlas.commercialChart

maintainedPath :
  (consequence : MaintainedTranslationConsequence) →
  Path.TranslationPath
    (maintainedPathSource consequence)
    (maintainedPathTarget consequence)
maintainedPath clinicalSafetyMaintained =
  Path.pathStep Path.stateClinicalLeg Path.pathId
maintainedPath livedSubjectMaintained = Path.stateClinicalLivedPath
maintainedPath sovereignCommercialExtractionMaintained =
  Path.indigenousCommercialPath

data PathIndexedArtifact : Set where
  edgeArtifact : Edge.TranslationEdgeInstance → PathIndexedArtifact
  pathCertificate : MaintainedTranslationConsequence → PathIndexedArtifact
  consumerCertificate : MaintainedTranslationConsequence → PathIndexedArtifact

data Depends : PathIndexedArtifact → PathIndexedArtifact → Set where
  membershipCreatesPathDependency :
    ∀ {edge consequence} →
    EdgeOccursInPath edge (maintainedPath consequence) →
    Depends (edgeArtifact edge) (pathCertificate consequence)
  pathFeedsConsumer :
    ∀ {consequence} →
    Depends (pathCertificate consequence) (consumerCertificate consequence)

membershipCreatesReopening :
  ∀ {edge consequence} →
  EdgeOccursInPath edge (maintainedPath consequence) →
  Affected.ReopeningObligation
    Depends (edgeArtifact edge) (pathCertificate consequence)
membershipCreatesReopening membership =
  Affected.oneEdgeCreatesReopeningObligation
    (membershipCreatesPathDependency membership)

membershipReopensConsumer :
  ∀ {edge consequence} →
  EdgeOccursInPath edge (maintainedPath consequence) →
  Affected.ReopeningObligation
    Depends (edgeArtifact edge) (consumerCertificate consequence)
membershipReopensConsumer membership =
  Affected.obligationsCompose
    (membershipCreatesReopening membership)
    (Affected.oneEdgeCreatesReopeningObligation pathFeedsConsumer)

stateClinicalRevisionReopensLivedSubjectConsumer :
  Affected.ReopeningObligation
    Depends
    (edgeArtifact Edge.stateToClinicalEdge)
    (consumerCertificate livedSubjectMaintained)
stateClinicalRevisionReopensLivedSubjectConsumer =
  membershipReopensConsumer stateClinicalOccursInComposedLivedPath

clinicalLivedRevisionReopensLivedSubjectConsumer :
  Affected.ReopeningObligation
    Depends
    (edgeArtifact Edge.clinicalToLivedEdge)
    (consumerCertificate livedSubjectMaintained)
clinicalLivedRevisionReopensLivedSubjectConsumer =
  membershipReopensConsumer clinicalLivedOccursInComposedLivedPath

indigenousCommercialRevisionReopensExtractionConsumer :
  Affected.ReopeningObligation
    Depends
    (edgeArtifact Edge.indigenousToCommercialEdge)
    (consumerCertificate sovereignCommercialExtractionMaintained)
indigenousCommercialRevisionReopensExtractionConsumer =
  membershipReopensConsumer (edgeHere indigenousCommercialLegHasEdge)

------------------------------------------------------------------------
-- Hard boundaries.
------------------------------------------------------------------------

data SameEndpointsPromoteSameAffectedSet : Set where

data EdgeTypePromotesOccurrence : Set where

data ReopeningPromotesRefutation : Set where

sameEndpointsDoNotPromoteSameAffectedSet :
  SameEndpointsPromoteSameAffectedSet → ⊥
sameEndpointsDoNotPromoteSameAffectedSet ()

edgeTypeDoesNotPromoteOccurrence : EdgeTypePromotesOccurrence → ⊥
edgeTypeDoesNotPromoteOccurrence ()

reopeningDoesNotPromoteRefutation : ReopeningPromotesRefutation → ⊥
reopeningDoesNotPromoteRefutation ()

record ComposedPathEdgeReopeningBoundary : Set where
  constructor composedPathEdgeReopeningBoundary
  field
    exactPathMembershipCreatesDependency : Bool
    exactPathMembershipCreatesDependencyIsTrue :
      exactPathMembershipCreatesDependency ≡ true
    exactPathMembershipReopensConsumer : Bool
    exactPathMembershipReopensConsumerIsTrue :
      exactPathMembershipReopensConsumer ≡ true
    edgeFamilyWithoutMembershipForcesReopening : Bool
    edgeFamilyWithoutMembershipForcesReopeningIsFalse :
      edgeFamilyWithoutMembershipForcesReopening ≡ false
    reopeningMeansRefutation : Bool
    reopeningMeansRefutationIsFalse : reopeningMeansRefutation ≡ false

canonicalComposedPathEdgeReopeningBoundary : ComposedPathEdgeReopeningBoundary
canonicalComposedPathEdgeReopeningBoundary =
  composedPathEdgeReopeningBoundary
    true refl
    true refl
    false refl
    false refl
