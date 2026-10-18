module DASHI.Law.LegalVisualisationIRProjectionBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- VisualisationIR is a downstream readout carrier.
--
-- It may rearrange already-admitted semantic identities into graph, timeline,
-- proof-topology, comparative, or Sankey forms.  It may not invent authority.
-- Sankey weights in the current v0 are topology/event counts, not legal weight.
------------------------------------------------------------------------

data VisualisationKind : Set where
  timeline graph sankey researchFrontier proofTopology comparative :
    VisualisationKind

record LegalVisualisationIRBoundary : Set where
  constructor legalVisualisationIRBoundary
  field
    sourceIsProjectionGraph : Bool
    sourceIsProjectionGraphIsTrue :
      sourceIsProjectionGraph ≡ true

    visualisationMayInventSemanticIdentity : Bool
    visualisationMayInventSemanticIdentityIsFalse :
      visualisationMayInventSemanticIdentity ≡ false

    visualisationCreatesLegalAuthority : Bool
    visualisationCreatesLegalAuthorityIsFalse :
      visualisationCreatesLegalAuthority ≡ false

    sankeyWeightMeansObservedCountOrTopologyCount : Bool
    sankeyWeightMeansObservedCountOrTopologyCountIsTrue :
      sankeyWeightMeansObservedCountOrTopologyCount ≡ true

    sankeyWeightMeansLegalImportance : Bool
    sankeyWeightMeansLegalImportanceIsFalse :
      sankeyWeightMeansLegalImportance ≡ false

    sankeyWeightMeansAuthorityStrength : Bool
    sankeyWeightMeansAuthorityStrengthIsFalse :
      sankeyWeightMeansAuthorityStrength ≡ false

    researchFlowMayExposeReviewAndResidualStages : Bool
    researchFlowMayExposeReviewAndResidualStagesIsTrue :
      researchFlowMayExposeReviewAndResidualStages ≡ true

    renderChoiceMayChangeDomainCommandSemantics : Bool
    renderChoiceMayChangeDomainCommandSemanticsIsFalse :
      renderChoiceMayChangeDomainCommandSemantics ≡ false

open LegalVisualisationIRBoundary public

canonicalLegalVisualisationIRBoundary :
  LegalVisualisationIRBoundary
canonicalLegalVisualisationIRBoundary =
  legalVisualisationIRBoundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl

data SankeyCountAutomaticallyLegalImportance : Set where
data VisualisationAutomaticallyAuthority : Set where
data RenderChoiceAutomaticallyChangesSemantics : Set where

sankeyCountDoesNotBecomeLegalImportance :
  SankeyCountAutomaticallyLegalImportance → ⊥
sankeyCountDoesNotBecomeLegalImportance ()

visualisationDoesNotCreateAuthority :
  VisualisationAutomaticallyAuthority → ⊥
visualisationDoesNotCreateAuthority ()

renderChoiceDoesNotChangeSemanticCommand :
  RenderChoiceAutomaticallyChangesSemantics → ⊥
renderChoiceDoesNotChangeSemanticCommand ()
