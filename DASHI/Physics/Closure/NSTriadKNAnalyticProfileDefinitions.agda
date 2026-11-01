module DASHI.Physics.Closure.NSTriadKNAnalyticProfileDefinitions where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase as DepthBase
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNProfileDefinitionsDepthGeometry
  as DepthGeometry

------------------------------------------------------------------------
-- Canonical analytic profile-definition layer for NS Blocker 1.
--
-- This module does not prove the missing label lifts. It names the exact
-- analytic definitions that would make the forced-tail/adversarial/
-- transition labels geometrically meaningful for entryDepth separation.
------------------------------------------------------------------------

data NSTriadKNAnalyticProfileDefinitionsPromotion : Set where

analyticProfileDefinitionsPromotionImpossibleHere :
  NSTriadKNAnalyticProfileDefinitionsPromotion → ⊥
analyticProfileDefinitionsPromotionImpossibleHere ()

ForcedTailSourceDef : Nat → Nat → Set
ForcedTailSourceDef = DepthBase.ForcedTailSourceDef

AdversarialTargetDef : Nat → Nat → Set
AdversarialTargetDef = DepthBase.AdversarialTargetDef

TransitionTargetDef : Nat → Nat → Set
TransitionTargetDef = DepthBase.TransitionTargetDef

record AnalyticProfileDefinitionsTarget : Set₁ where
  field
    forcedTailDefinitionImpliesLabel :
      (N i : Nat) →
      ForcedTailSourceDef N i →
      WeightModel.ForcedTailSource N i

    adversarialDefinitionImpliesLabel :
      (N j : Nat) →
      AdversarialTargetDef N j →
      WeightModel.AdversarialTarget N j

    transitionDefinitionImpliesLabel :
      (N j : Nat) →
      TransitionTargetDef N j →
      WeightModel.TransitionTarget N j

    forcedTailLabelToDefinition :
      (N i : Nat) →
      WeightModel.ForcedTailSource N i →
      ForcedTailSourceDef N i

    adversarialLabelToDefinition :
      (N j : Nat) →
      WeightModel.AdversarialTarget N j →
      AdversarialTargetDef N j

    transitionLabelToDefinition :
      (N j : Nat) →
      WeightModel.TransitionTarget N j →
      TransitionTargetDef N j

canonicalAnalyticProfileDefinitionsTarget :
  AnalyticProfileDefinitionsTarget
canonicalAnalyticProfileDefinitionsTarget = record
  { forcedTailDefinitionImpliesLabel = λ N i def → def
  ; adversarialDefinitionImpliesLabel = λ N j def → def
  ; transitionDefinitionImpliesLabel = λ N j def → def
  ; forcedTailLabelToDefinition = λ N i label → label
  ; adversarialLabelToDefinition = λ N j label → label
  ; transitionLabelToDefinition = λ N j label → label
  }

analyticProfileDefinitionsSurface :
  AnalyticProfileDefinitionsTarget →
  DepthGeometry.ProfileDefinitionsDepthGeometrySurface
analyticProfileDefinitionsSurface target = record
  { ForcedTailSourceDef = ForcedTailSourceDef
  ; AdversarialTargetDef = AdversarialTargetDef
  ; TransitionTargetDef = TransitionTargetDef
  ; forcedTailDefinitionImpliesLabel =
      AnalyticProfileDefinitionsTarget.forcedTailDefinitionImpliesLabel target
  ; adversarialDefinitionImpliesLabel =
      AnalyticProfileDefinitionsTarget.adversarialDefinitionImpliesLabel target
  ; transitionDefinitionImpliesLabel =
      AnalyticProfileDefinitionsTarget.transitionDefinitionImpliesLabel target
  ; forcedTailLabelToDefinition =
      AnalyticProfileDefinitionsTarget.forcedTailLabelToDefinition target
  ; adversarialLabelToDefinition =
      AnalyticProfileDefinitionsTarget.adversarialLabelToDefinition target
  ; transitionLabelToDefinition =
      AnalyticProfileDefinitionsTarget.transitionLabelToDefinition target
  ; forcedTailSourceDefDepthUpper =
      λ N i def → DepthBase.ForcedTailSourceDef.depthUpper def
  ; adversarialTargetDefDepthLower =
      λ N j def → DepthBase.AdversarialTargetDef.depthLower def
  ; transitionTargetDefDepthLower =
      λ N j def → DepthBase.TransitionTargetDef.depthLower def
  }

canonicalAnalyticProfileDefinitionsSurface :
  DepthGeometry.ProfileDefinitionsDepthGeometrySurface
canonicalAnalyticProfileDefinitionsSurface =
  analyticProfileDefinitionsSurface canonicalAnalyticProfileDefinitionsTarget

canonicalReceiptText : String
canonicalReceiptText =
  "Canonical analytic profile-definition layer for Blocker 1: define forced-tail, adversarial-target, and transition-target membership by the entryDepth inequalities needed downstream."

canonicalOpenReasonText : String
canonicalOpenReasonText =
  "The repo still lacks proofs that the existing label predicates lift into these analytic definitions. Until those lifts are inhabited, the labels remain depth-free receipts."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: replace the abstract label construction with proofs of forcedTailLabelToDefinition, adversarialLabelToDefinition, and transitionLabelToDefinition."

record NSTriadKNAnalyticProfileDefinitionsReceipt : Setω where
  constructor mkNSTriadKNAnalyticProfileDefinitionsReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNAnalyticProfileDefinitionsReceipt"

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

    forcedTailLiftClosed : Bool
    forcedTailLiftClosedIsTrue :
      forcedTailLiftClosed ≡ true

    adversarialLiftClosed : Bool
    adversarialLiftClosedIsTrue :
      adversarialLiftClosed ≡ true

    transitionLiftClosed : Bool
    transitionLiftClosedIsTrue :
      transitionLiftClosed ≡ true

    analyticDefinitionSurfaceClosed : Bool
    analyticDefinitionSurfaceClosedIsTrue :
      analyticDefinitionSurfaceClosed ≡ true

canonicalNSTriadKNAnalyticProfileDefinitionsReceipt :
  NSTriadKNAnalyticProfileDefinitionsReceipt
canonicalNSTriadKNAnalyticProfileDefinitionsReceipt =
  mkNSTriadKNAnalyticProfileDefinitionsReceipt
    "NSTriadKNAnalyticProfileDefinitionsReceipt"
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

analyticProfileDefinitionLiftsClosed : Bool
analyticProfileDefinitionLiftsClosed = true
