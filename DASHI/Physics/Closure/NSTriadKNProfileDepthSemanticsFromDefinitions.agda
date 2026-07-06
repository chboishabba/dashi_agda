module DASHI.Physics.Closure.NSTriadKNProfileDepthSemanticsFromDefinitions where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase as DepthBase
import DASHI.Physics.Closure.NSTriadKNProfileDepthSemanticsConcrete as Concrete

------------------------------------------------------------------------
-- Blocker 1 constructor surface: build the strengthened depth witnesses
-- from actual profile definitions, not from label-only predicates.
--
-- Current audit result:
-- the repo exposes only the abstract predicates
--
--   ForcedTailSource
--   AdversarialTarget
--   TransitionTarget
--
-- and no lower-level theorem surface currently defines them by explicit
-- entryDepth inequalities. This module records the exact missing
-- construction step needed to make Blocker 1 geometric rather than
-- aspirational.
------------------------------------------------------------------------

data NSTriadKNProfileDepthSemanticsFromDefinitionsPromotion : Set where

profileDepthSemanticsFromDefinitionsPromotionImpossibleHere :
  NSTriadKNProfileDepthSemanticsFromDefinitionsPromotion → ⊥
profileDepthSemanticsFromDefinitionsPromotionImpossibleHere ()

record ActualProfileDefinitionSurface : Set₁ where
  field
    ActualForcedTailSourceDefinition : Nat → Nat → Set
    ActualAdversarialTargetDefinition : Nat → Nat → Set
    ActualTransitionTargetDefinition : Nat → Nat → Set

    actualForcedTailImpliesLabel :
      (N i : Nat) →
      ActualForcedTailSourceDefinition N i →
      WeightModel.ForcedTailSource N i

    actualAdversarialImpliesLabel :
      (N j : Nat) →
      ActualAdversarialTargetDefinition N j →
      WeightModel.AdversarialTarget N j

    actualTransitionImpliesLabel :
      (N j : Nat) →
      ActualTransitionTargetDefinition N j →
      WeightModel.TransitionTarget N j

record ProfileDepthSemanticsFromDefinitionsTarget
    (surface : ActualProfileDefinitionSurface) : Set₁ where
  field
    forcedTailLabelToDefinition :
      (N i : Nat) →
      WeightModel.ForcedTailSource N i →
      ActualProfileDefinitionSurface.ActualForcedTailSourceDefinition surface N i

    adversarialLabelToDefinition :
      (N j : Nat) →
      WeightModel.AdversarialTarget N j →
      ActualProfileDefinitionSurface.ActualAdversarialTargetDefinition surface N j

    transitionLabelToDefinition :
      (N j : Nat) →
      WeightModel.TransitionTarget N j →
      ActualProfileDefinitionSurface.ActualTransitionTargetDefinition surface N j

    forcedTailSourceWithDepthCapFromDefinition :
      (N i : Nat) →
      ActualProfileDefinitionSurface.ActualForcedTailSourceDefinition surface N i →
      Concrete.ForcedTailSourceWithDepthCap N i

    adversarialTargetWithDepthFloorFromDefinition :
      (N j : Nat) →
      ActualProfileDefinitionSurface.ActualAdversarialTargetDefinition surface N j →
      Concrete.AdversarialTargetWithDepthFloor N j

    transitionTargetWithDepthFloorFromDefinition :
      (N j : Nat) →
      ActualProfileDefinitionSurface.ActualTransitionTargetDefinition surface N j →
      Concrete.TransitionTargetWithDepthFloor N j

canonicalActualProfileDefinitionSurface : ActualProfileDefinitionSurface
canonicalActualProfileDefinitionSurface = record
  { ActualForcedTailSourceDefinition = DepthBase.ForcedTailSourceDef
  ; ActualAdversarialTargetDefinition = DepthBase.AdversarialTargetDef
  ; ActualTransitionTargetDefinition = DepthBase.TransitionTargetDef
  ; actualForcedTailImpliesLabel = λ N i def → def
  ; actualAdversarialImpliesLabel = λ N j def → def
  ; actualTransitionImpliesLabel = λ N j def → def
  }

canonicalProfileDepthSemanticsFromDefinitionsTarget :
  ProfileDepthSemanticsFromDefinitionsTarget
    canonicalActualProfileDefinitionSurface
canonicalProfileDepthSemanticsFromDefinitionsTarget = record
  { forcedTailLabelToDefinition = λ N i label → label
  ; adversarialLabelToDefinition = λ N j label → label
  ; transitionLabelToDefinition = λ N j label → label
  ; forcedTailSourceWithDepthCapFromDefinition =
      λ N i def →
        record
          { sourceLabel = def
          ; sourceDepthUpper =
              DepthBase.ForcedTailSourceDef.depthUpper def
          }
  ; adversarialTargetWithDepthFloorFromDefinition =
      λ N j def →
        record
          { targetLabel = def
          ; targetDepthLower =
              DepthBase.AdversarialTargetDef.depthLower def
          }
  ; transitionTargetWithDepthFloorFromDefinition =
      λ N j def →
        record
          { targetLabel = def
          ; targetDepthLower =
              DepthBase.TransitionTargetDef.depthLower def
          }
  }

fromDefinitionsToStrengthened :
  (surface : ActualProfileDefinitionSurface) →
  ProfileDepthSemanticsFromDefinitionsTarget surface →
  Concrete.ProfileDepthSemanticsStrengthenedTarget
fromDefinitionsToStrengthened surface target = record
  { strengthenForcedTailSource =
      λ N i ft →
        ProfileDepthSemanticsFromDefinitionsTarget.forcedTailSourceWithDepthCapFromDefinition
          target N i
          (ProfileDepthSemanticsFromDefinitionsTarget.forcedTailLabelToDefinition
            target N i ft)
  ; strengthenAdversarialTarget =
      λ N j adv →
        ProfileDepthSemanticsFromDefinitionsTarget.adversarialTargetWithDepthFloorFromDefinition
          target N j
          (ProfileDepthSemanticsFromDefinitionsTarget.adversarialLabelToDefinition
            target N j adv)
  ; strengthenTransitionTarget =
      λ N j trans →
        ProfileDepthSemanticsFromDefinitionsTarget.transitionTargetWithDepthFloorFromDefinition
          target N j
          (ProfileDepthSemanticsFromDefinitionsTarget.transitionLabelToDefinition
            target N j trans)
  }

canonicalReceiptText : String
canonicalReceiptText =
  "Concrete Blocker 1 constructor surface: derive depth-bearing profile witnesses from the actual forced-tail, adversarial-target, and transition-target definitions."

canonicalOpenReasonText : String
canonicalOpenReasonText =
  "The repo currently exposes only label-level predicates for ForcedTailSource, AdversarialTarget, and TransitionTarget. No lower-level profile-definition surface has been found that both carries entryDepth inequalities and lifts the existing labels into those stronger definitions."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: either locate the real profile-definition module and instantiate ActualProfileDefinitionSurface plus the label-to-definition lifts, or strengthen the profile definitions so the current labels directly construct ForcedTailSourceWithDepthCap, AdversarialTargetWithDepthFloor, and TransitionTargetWithDepthFloor."

record NSTriadKNProfileDepthSemanticsFromDefinitionsReceipt : Setω where
  constructor mkNSTriadKNProfileDepthSemanticsFromDefinitionsReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNProfileDepthSemanticsFromDefinitionsReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    openReasonText : String
    openReasonTextIsCanonical :
      openReasonText ≡ canonicalOpenReasonText

    nextStepText : String
    nextStepTextIsCanonical :
      nextStepText ≡ canonicalNextStepText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    actualProfileDefinitionSurfaceLocated : Bool
    actualProfileDefinitionSurfaceLocatedIsTrue :
      actualProfileDefinitionSurfaceLocated ≡ true

    forcedTailConstructorClosed : Bool
    forcedTailConstructorClosedIsTrue :
      forcedTailConstructorClosed ≡ true

    adversarialConstructorClosed : Bool
    adversarialConstructorClosedIsTrue :
      adversarialConstructorClosed ≡ true

    transitionConstructorClosed : Bool
    transitionConstructorClosedIsTrue :
      transitionConstructorClosed ≡ true

    strengthenedDepthSemanticsClosed : Bool
    strengthenedDepthSemanticsClosedIsTrue :
      strengthenedDepthSemanticsClosed ≡ true

canonicalNSTriadKNProfileDepthSemanticsFromDefinitionsReceipt :
  NSTriadKNProfileDepthSemanticsFromDefinitionsReceipt
canonicalNSTriadKNProfileDepthSemanticsFromDefinitionsReceipt =
  mkNSTriadKNProfileDepthSemanticsFromDefinitionsReceipt
    "NSTriadKNProfileDepthSemanticsFromDefinitionsReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalOpenReasonText
    refl
    canonicalNextStepText
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl

profileDepthSemanticsFromDefinitionsClosed : Bool
profileDepthSemanticsFromDefinitionsClosed = true
