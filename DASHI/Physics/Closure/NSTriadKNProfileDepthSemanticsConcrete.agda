module DASHI.Physics.Closure.NSTriadKNProfileDepthSemanticsConcrete where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤)

import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase as DepthBase

------------------------------------------------------------------------
-- Concrete Blocker 1 depth-semantics surface for FT→adv.
--
-- The classifier-backed FT→adv incidence and witness packaging are now
-- real. The remaining local theorem content is purely geometric:
--
--   ForcedTailSource N i  -> entryDepth i <= D_FT(N)
--   AdversarialTarget N j -> D_FT(N) + N <= entryDepth j
--
-- Until these are inhabited from actual profile definitions, the FT→adv
-- depth-separation route must remain fail-closed.
------------------------------------------------------------------------

data NSTriadKNProfileDepthSemanticsConcretePromotion : Set where

profileDepthSemanticsConcretePromotionImpossibleHere :
  NSTriadKNProfileDepthSemanticsConcretePromotion → ⊥
profileDepthSemanticsConcretePromotionImpossibleHere ()

record ForcedTailSourceWithDepthCap (N i : Nat) : Set where
  field
    sourceLabel :
      WeightModel.ForcedTailSource N i

    sourceDepthUpper :
      WeightModel.entryDepth i ≤ WeightModel.forcedTailSourceDepthCap N

record AdversarialTargetWithDepthFloor (N j : Nat) : Set where
  field
    targetLabel :
      WeightModel.AdversarialTarget N j

    targetDepthLower :
      WeightModel.forcedTailSourceDepthCap N + WeightModel.advLogDepthRequired N
        ≤ WeightModel.entryDepth j

record TransitionTargetWithDepthFloor (N j : Nat) : Set where
  field
    targetLabel :
      WeightModel.TransitionTarget N j

    targetDepthLower :
      WeightModel.forcedTailSourceDepthCap N + WeightModel.transLogDepthRequired N
        ≤ WeightModel.entryDepth j

record ProfileDepthSemanticsConcreteTarget : Set₁ where
  field
    forcedTailSourceDepthUpper :
      (N i : Nat) →
      WeightModel.ForcedTailSource N i →
      WeightModel.entryDepth i ≤ WeightModel.forcedTailSourceDepthCap N

    adversarialTargetDepthLower :
      (N j : Nat) →
      WeightModel.AdversarialTarget N j →
      WeightModel.forcedTailSourceDepthCap N + WeightModel.advLogDepthRequired N
        ≤ WeightModel.entryDepth j

record ProfileDepthSemanticsStrengthenedTarget : Set₁ where
  field
    strengthenForcedTailSource :
      (N i : Nat) →
      WeightModel.ForcedTailSource N i →
      ForcedTailSourceWithDepthCap N i

    strengthenAdversarialTarget :
      (N j : Nat) →
      WeightModel.AdversarialTarget N j →
      AdversarialTargetWithDepthFloor N j

    strengthenTransitionTarget :
      (N j : Nat) →
      WeightModel.TransitionTarget N j →
      TransitionTargetWithDepthFloor N j

strengthenedTargetToConcrete :
  ProfileDepthSemanticsStrengthenedTarget →
  ProfileDepthSemanticsConcreteTarget
strengthenedTargetToConcrete strengthened = record
  { forcedTailSourceDepthUpper =
      λ N i ft →
        ForcedTailSourceWithDepthCap.sourceDepthUpper
          (ProfileDepthSemanticsStrengthenedTarget.strengthenForcedTailSource
            strengthened N i ft)
  ; adversarialTargetDepthLower =
      λ N j adv →
        AdversarialTargetWithDepthFloor.targetDepthLower
          (ProfileDepthSemanticsStrengthenedTarget.strengthenAdversarialTarget
            strengthened N j adv)
  }

canonicalProfileDepthSemanticsStrengthenedTarget :
  ProfileDepthSemanticsStrengthenedTarget
canonicalProfileDepthSemanticsStrengthenedTarget = record
  { strengthenForcedTailSource =
      λ N i ft → record
        { sourceLabel = ft
        ; sourceDepthUpper =
            DepthBase.ForcedTailSourceDef.depthUpper ft
        }
  ; strengthenAdversarialTarget =
      λ N j adv → record
        { targetLabel = adv
        ; targetDepthLower =
            DepthBase.AdversarialTargetDef.depthLower adv
        }
  ; strengthenTransitionTarget =
      λ N j trans → record
        { targetLabel = trans
        ; targetDepthLower =
            DepthBase.TransitionTargetDef.depthLower trans
        }
  }

canonicalProfileDepthSemanticsConcreteTarget :
  ProfileDepthSemanticsConcreteTarget
canonicalProfileDepthSemanticsConcreteTarget =
  strengthenedTargetToConcrete
    canonicalProfileDepthSemanticsStrengthenedTarget

ftAdvDepthSeparationFromConcreteDepthSemantics :
  (target : ProfileDepthSemanticsConcreteTarget) →
  (N i j : Nat) →
  WeightModel.ForcedTailSource N i →
  WeightModel.AdversarialTarget N j →
  WeightModel.entryDepth i + WeightModel.advLogDepthRequired N
    ≤ WeightModel.entryDepth j
ftAdvDepthSeparationFromConcreteDepthSemantics target N i j ft adv =
  ≤-trans
    (+-mono-≤
      (ProfileDepthSemanticsConcreteTarget.forcedTailSourceDepthUpper
        target N i ft)
      ≤-refl)
    (ProfileDepthSemanticsConcreteTarget.adversarialTargetDepthLower
      target N j adv)

canonicalReceiptText : String
canonicalReceiptText =
  "Concrete FT->adv depth-semantics target: derive the source and target entryDepth inequalities needed for ftAdvDepthSeparationLinear from actual ForcedTailSource and AdversarialTarget semantics."

canonicalOpenReasonText : String
canonicalOpenReasonText =
  "The canonical ForcedTailSource and AdversarialTarget definitions carry the required entryDepth bounds projectionally."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: consume the concrete depth semantics in the active forced-tail cross route."

canonicalStrengthenedReceiptText : String
canonicalStrengthenedReceiptText =
  "Strengthened FT->adv depth-semantics target: upgrade the label-only ForcedTailSource and AdversarialTarget predicates to witness-carrying records whose depth inequalities are projectional."

canonicalStrengthenedOpenReasonText : String
canonicalStrengthenedOpenReasonText =
  "The canonical strengthened depth semantics are now projectional from the profile definitions."

canonicalStrengthenedNextStepText : String
canonicalStrengthenedNextStepText =
  "Next step: use the projected depth witnesses in the active forced-tail cross route."

record NSTriadKNProfileDepthSemanticsConcreteReceipt : Setω where
  constructor mkNSTriadKNProfileDepthSemanticsConcreteReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNProfileDepthSemanticsConcreteReceipt"

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

    sourceDepthUpperClosed : Bool
    sourceDepthUpperClosedIsTrue :
      sourceDepthUpperClosed ≡ true

    targetDepthLowerClosed : Bool
    targetDepthLowerClosedIsTrue :
      targetDepthLowerClosed ≡ true

    ftAdvDepthSeparationClosed : Bool
    ftAdvDepthSeparationClosedIsTrue :
      ftAdvDepthSeparationClosed ≡ true

record NSTriadKNProfileDepthSemanticsStrengthenedReceipt : Setω where
  constructor mkNSTriadKNProfileDepthSemanticsStrengthenedReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNProfileDepthSemanticsStrengthenedReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalStrengthenedReceiptText

    openReasonText : String
    openReasonTextIsCanonical :
      openReasonText ≡ canonicalStrengthenedOpenReasonText

    nextStepText : String
    nextStepTextIsCanonical :
      nextStepText ≡ canonicalStrengthenedNextStepText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    strengtheningClosed : Bool
    strengtheningClosedIsTrue :
      strengtheningClosed ≡ true

    projectionToConcreteAvailable : Bool
    projectionToConcreteAvailableIsTrue :
      projectionToConcreteAvailable ≡ true

canonicalNSTriadKNProfileDepthSemanticsConcreteReceipt :
  NSTriadKNProfileDepthSemanticsConcreteReceipt
canonicalNSTriadKNProfileDepthSemanticsConcreteReceipt =
  mkNSTriadKNProfileDepthSemanticsConcreteReceipt
    "NSTriadKNProfileDepthSemanticsConcreteReceipt"
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

canonicalNSTriadKNProfileDepthSemanticsStrengthenedReceipt :
  NSTriadKNProfileDepthSemanticsStrengthenedReceipt
canonicalNSTriadKNProfileDepthSemanticsStrengthenedReceipt =
  mkNSTriadKNProfileDepthSemanticsStrengthenedReceipt
    "NSTriadKNProfileDepthSemanticsStrengthenedReceipt"
    refl
    canonicalStrengthenedReceiptText
    refl
    canonicalStrengthenedOpenReasonText
    refl
    canonicalStrengthenedNextStepText
    refl
    true
    refl
    true
    refl
    true
    refl

profileDepthSemanticsConcreteClosed : Bool
profileDepthSemanticsConcreteClosed = true

profileDepthSemanticsStrengtheningClosed : Bool
profileDepthSemanticsStrengtheningClosed = true
