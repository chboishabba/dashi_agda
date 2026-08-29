module DASHI.Core.ObligationReducingExtensionGuardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- OBLIGATION-REDUCING EXTENSION GUARD
--
-- Generic admission rule for new conceptual / architectural layers.
--
-- A new layer is promotion-relevant only when it carries one of three actual
-- receipts:
--
--   * a live obligation disappears from the after-frontier;
--   * an old observer collision is separated by a new observer;
--   * an obligation hidden by the old chart becomes explicitly visible in the
--     refined frontier.
--
-- Mere renaming, commentary, parallel vocabulary, or extra abstraction has no
-- promotion constructor.
------------------------------------------------------------------------

record DischargeReceipt (Obligation : Set)
                        (liveBefore liveAfter : Obligation → Set) : Set where
  constructor dischargeReceipt
  field
    dischargedObligation : Obligation
    wasLive : liveBefore dischargedObligation
    isClosedAfter : liveAfter dischargedObligation → ⊥

open DischargeReceipt public

record StrictObserverRefinementReceipt
    (Fine Old New : Set)
    (oldObserve : Fine → Old)
    (newObserve : Fine → New) : Set where
  constructor strictObserverRefinementReceipt
  field
    collisionLeft collisionRight : Fine
    oldCollision : oldObserve collisionLeft ≡ oldObserve collisionRight
    newSeparation : newObserve collisionLeft ≡ newObserve collisionRight → ⊥

open StrictObserverRefinementReceipt public

record ExposureReceipt (Obligation : Set)
                       (visibleBefore visibleAfter : Obligation → Set) : Set where
  constructor exposureReceipt
  field
    exposedObligation : Obligation
    wasNotVisible : visibleBefore exposedObligation → ⊥
    isVisibleAfter : visibleAfter exposedObligation

open ExposureReceipt public

data ExtensionProgressReceipt : Set₁ where
  discharged :
    {Obligation : Set} →
    {liveBefore liveAfter : Obligation → Set} →
    DischargeReceipt Obligation liveBefore liveAfter →
    ExtensionProgressReceipt

  refined :
    {Fine Old New : Set} →
    {oldObserve : Fine → Old} →
    {newObserve : Fine → New} →
    StrictObserverRefinementReceipt Fine Old New oldObserve newObserve →
    ExtensionProgressReceipt

  exposed :
    {Obligation : Set} →
    {visibleBefore visibleAfter : Obligation → Set} →
    ExposureReceipt Obligation visibleBefore visibleAfter →
    ExtensionProgressReceipt

data ExtensionStatus : Set₁ where
  theoremBearingProgress : ExtensionProgressReceipt → ExtensionStatus
  scaffoldingOnly : ExtensionStatus

record ExtensionAdmission : Set₁ where
  constructor extensionAdmission
  field
    extensionName : String
    status : ExtensionStatus
    evidenceReceiptReference : String
    sourceOrInternalProvenance : String

open ExtensionAdmission public

PromotionRelevant : ExtensionAdmission → Set
PromotionRelevant admission with status admission
... | theoremBearingProgress receipt = ⊤
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
    "internal explanatory scaffolding"

commentaryOnlyCannotPromote : PromotionRelevant commentaryOnly → ⊥
commentaryOnlyCannotPromote ()

data FineExample : Set where
  leftExample rightExample : FineExample

data OldExample : Set where
  oldCollapsed : OldExample

data NewExample : Set where
  newLeft newRight : NewExample

oldExampleObserve : FineExample → OldExample
oldExampleObserve leftExample = oldCollapsed
oldExampleObserve rightExample = oldCollapsed

newExampleObserve : FineExample → NewExample
newExampleObserve leftExample = newLeft
newExampleObserve rightExample = newRight

newExampleSeparation : newLeft ≡ newRight → ⊥
newExampleSeparation ()

canonicalRefinementReceipt :
  StrictObserverRefinementReceipt
    FineExample OldExample NewExample
    oldExampleObserve newExampleObserve
canonicalRefinementReceipt =
  strictObserverRefinementReceipt
    leftExample rightExample refl newExampleSeparation

witnessedRefinement : ExtensionAdmission
witnessedRefinement =
  extensionAdmission
    "witnessed observer refinement"
    (theoremBearingProgress (refined canonicalRefinementReceipt))
    "strict observer-refinement receipt"
    "internal theorem-bearing refinement"

witnessedRefinementIsPromotionRelevant : PromotionRelevant witnessedRefinement
witnessedRefinementIsPromotionRelevant = tt
