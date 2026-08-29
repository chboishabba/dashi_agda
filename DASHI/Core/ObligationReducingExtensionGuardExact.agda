module DASHI.Core.ObligationReducingExtensionGuardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- OBLIGATION-REDUCING EXTENSION GUARD
--
-- Generic admission rule for new conceptual / architectural layers.
--
-- A new layer is promotion-relevant only when it demonstrably changes the
-- live obligation surface by one of three routes:
--
--   * discharges a previously live obligation;
--   * strictly refines an observer / representation so a previously hidden
--     distinction becomes available;
--   * exposes a new live empirical or mathematical obligation that was hidden
--     by the previous chart.
--
-- Mere renaming, commentary, parallel vocabulary, or extra abstraction does
-- not itself advance the proof / experiment frontier.
------------------------------------------------------------------------

data ExtensionEffect : Set where
  dischargesLiveObligation
  strictlyRefinesRequiredObserver
  exposesPreviouslyHiddenObligation
  scaffoldingOnly

record ExtensionAdmission : Set where
  constructor extensionAdmission
  field
    extensionName : String
    effect : ExtensionEffect
    liveObligationReference : String
    evidenceReceiptReference : String
    sourceOrInternalProvenance : String

open ExtensionAdmission public

PromotionRelevant : ExtensionAdmission → Set
PromotionRelevant admission with effect admission
... | dischargesLiveObligation = ⊤
... | strictlyRefinesRequiredObserver = ⊤
... | exposesPreviouslyHiddenObligation = ⊤
... | scaffoldingOnly = ⊥

record ObligationReducingGuardBoundary : Set where
  constructor obligationReducingGuardBoundary
  field
    newVocabularyAloneAdvancesFrontier : Bool
    newVocabularyAloneAdvancesFrontierIsFalse :
      newVocabularyAloneAdvancesFrontier ≡ false

    parallelArchitectureAloneAdvancesFrontier : Bool
    parallelArchitectureAloneAdvancesFrontierIsFalse :
      parallelArchitectureAloneAdvancesFrontier ≡ false

    dischargedObligationMayAdvanceFrontier : Bool
    dischargedObligationMayAdvanceFrontierIsTrue :
      dischargedObligationMayAdvanceFrontier ≡ true

    strictRequiredRefinementMayAdvanceFrontier : Bool
    strictRequiredRefinementMayAdvanceFrontierIsTrue :
      strictRequiredRefinementMayAdvanceFrontier ≡ true

    newlyExposedRealObligationMayAdvanceFrontier : Bool
    newlyExposedRealObligationMayAdvanceFrontierIsTrue :
      newlyExposedRealObligationMayAdvanceFrontier ≡ true

    guardDoesNotDecideScientificTruth : Bool
    guardDoesNotDecideScientificTruthIsTrue :
      guardDoesNotDecideScientificTruth ≡ true

canonicalObligationReducingGuardBoundary : ObligationReducingGuardBoundary
canonicalObligationReducingGuardBoundary =
  obligationReducingGuardBoundary
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Tiny exact regressions.
------------------------------------------------------------------------

commentaryOnly : ExtensionAdmission
commentaryOnly =
  extensionAdmission
    "commentary-only layer"
    scaffoldingOnly
    "none"
    "none"
    "internal explanatory scaffolding"

commentaryOnlyCannotPromote : PromotionRelevant commentaryOnly → ⊥
commentaryOnlyCannotPromote ()

witnessedRefinement : ExtensionAdmission
witnessedRefinement =
  extensionAdmission
    "witnessed observer refinement"
    strictlyRefinesRequiredObserver
    "consumer collision on current observer"
    "strict refinement witness"
    "internal theorem-bearing refinement"

witnessedRefinementIsPromotionRelevant : PromotionRelevant witnessedRefinement
witnessedRefinementIsPromotionRelevant = tt

newlyExposedLeaf : ExtensionAdmission
newlyExposedLeaf =
  extensionAdmission
    "newly exposed analytic leaf"
    exposesPreviouslyHiddenObligation
    "hidden residual after exact decomposition"
    "same-object decomposition receipt"
    "internal theorem-bearing frontier reduction"

newlyExposedLeafIsPromotionRelevant : PromotionRelevant newlyExposedLeaf
newlyExposedLeafIsPromotionRelevant = tt
