module DASHI.Reasoning.EpistemicAuthorityBroadVisualFindingExact where

------------------------------------------------------------------------
-- Reification of findings produced by viewing the broad visual proof.
--
-- The first broad diagram used ordinary arrows too aggressively.  By direct
-- inspection it suggested two false derivations:
--
--   public rules -> institutional evaluation
--   folk evaluator -> institutional evaluator
--
-- The refined diagram types these relations separately.  This module records
-- the semantic lesson and connects it to the non-descent theorem in the broad
-- theory: the institutional observer is not, in general, reconstructible from
-- the folk observer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Reasoning.FolkLawEpistemicAuthorityCaptureExact as Base
import DASHI.Reasoning.FolkLawEpistemicAuthorityBroadExact as Broad

------------------------------------------------------------------------
-- 1. Typed visual-relation grammar
------------------------------------------------------------------------

data RelationKind : Set where
  authorityProfileTransition : RelationKind
  sharedInputComputation      : RelationKind
  epistemicRefinement         : RelationKind
  capabilityInclusion         : RelationKind

data VisualRelation : Set where
  directed : RelationKind → VisualRelation
  juxtaposedTradeoff : VisualRelation

record RefinedVisualGrammar : Set where
  constructor refinedVisualGrammar
  field
    captureUsesProfileTransition : VisualRelation
    evaluatorUsesSharedInput : VisualRelation
    verificationUsesRefinement : VisualRelation
    aiUsesCapabilityInclusion : VisualRelation

canonicalRefinedVisualGrammar : RefinedVisualGrammar
canonicalRefinedVisualGrammar =
  refinedVisualGrammar
    (directed authorityProfileTransition)
    (directed sharedInputComputation)
    (directed epistemicRefinement)
    (directed capabilityInclusion)

------------------------------------------------------------------------
-- 2. The visual finding has a mathematical counterpart: no generic sequential
--    map folk-observation -> institutional-observation can recover both fine
--    states in the collision fibre.
------------------------------------------------------------------------

visualNoFolkToInstitutionalDerivation :
  (reconstruct : Base.FolkObservation → Base.InstitutionalObservation) →
  ((state : Base.FineLegalState) →
    reconstruct (Base.folkObserver state) ≡ Base.institutionalObserver state) →
  ⊥
visualNoFolkToInstitutionalDerivation =
  Broad.institutionalObserverDoesNotDescendThroughFolk

------------------------------------------------------------------------
-- 3. Capture is not secrecy.  The refined visual keeps public rule visibility
--    orthogonal to institutional evaluation authority.
------------------------------------------------------------------------

visualPublicRulesWithCapturedInterpretation : Broad.CaptureWithoutSecrecy
visualPublicRulesWithCapturedInterpretation = Broad.canonicalCaptureWithoutSecrecy

------------------------------------------------------------------------
-- 4. Receipt of the introspective correction.
------------------------------------------------------------------------

record BroadVisualFindingBoundary : Set where
  constructor broadVisualFindingBoundary
  field
    untypedArrowsCanOverstateDerivation : Bool
    untypedArrowsCanOverstateDerivationIsTrue :
      untypedArrowsCanOverstateDerivation ≡ true
    folkEvaluatorSequentiallyDeterminesInstitutionalEvaluator : Bool
    folkEvaluatorSequentiallyDeterminesInstitutionalEvaluatorIsFalse :
      folkEvaluatorSequentiallyDeterminesInstitutionalEvaluator ≡ false
    sharedInputsMustRemainExplicit : Bool
    sharedInputsMustRemainExplicitIsTrue : sharedInputsMustRemainExplicit ≡ true
    captureImpliesRuleSecrecy : Bool
    captureImpliesRuleSecrecyIsFalse : captureImpliesRuleSecrecy ≡ false
    refinedVisualSeparatesRelationKinds : Bool
    refinedVisualSeparatesRelationKindsIsTrue :
      refinedVisualSeparatesRelationKinds ≡ true

canonicalBroadVisualFindingBoundary : BroadVisualFindingBoundary
canonicalBroadVisualFindingBoundary =
  broadVisualFindingBoundary
    true refl
    false refl
    true refl
    false refl
    true refl
