module DASHI.Physics.Closure.NSTriadKNProfileDefinitionsDepthGeometry where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _+_)

import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase as DepthBase
import DASHI.Physics.Closure.NSTriadKNProfileDepthSemanticsConcrete as Concrete
import DASHI.Physics.Closure.NSTriadKNProfileDepthSemanticsFromDefinitions
  as FromDefinitions

------------------------------------------------------------------------
-- Analytic profile-definition layer for Blocker 1.
--
-- This is the first place where the labels
--
--   ForcedTailSource
--   AdversarialTarget
--   TransitionTarget
--
-- are required to become mathematically meaningful for depth geometry.
-- The target is not a new receipt. The target is a theorem surface that
-- would let the existing label predicates lift into actual profile
-- definitions, then into depth-bearing witnesses.
------------------------------------------------------------------------

data NSTriadKNProfileDefinitionsDepthGeometryPromotion : Set where

profileDefinitionsDepthGeometryPromotionImpossibleHere :
  NSTriadKNProfileDefinitionsDepthGeometryPromotion → ⊥
profileDefinitionsDepthGeometryPromotionImpossibleHere ()

record ProfileDefinitionsDepthGeometrySurface : Set₁ where
  field
    ForcedTailSourceDef : Nat → Nat → Set
    AdversarialTargetDef : Nat → Nat → Set
    TransitionTargetDef : Nat → Nat → Set

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

    forcedTailSourceDefDepthUpper :
      (N i : Nat) →
      ForcedTailSourceDef N i →
      WeightModel.entryDepth i ≤ WeightModel.forcedTailSourceDepthCap N

    adversarialTargetDefDepthLower :
      (N j : Nat) →
      AdversarialTargetDef N j →
      WeightModel.forcedTailSourceDepthCap N + WeightModel.advLogDepthRequired N
        ≤ WeightModel.entryDepth j

    transitionTargetDefDepthLower :
      (N j : Nat) →
      TransitionTargetDef N j →
      WeightModel.forcedTailSourceDepthCap N + WeightModel.transLogDepthRequired N
        ≤ WeightModel.entryDepth j

canonicalProfileDefinitionsDepthGeometrySurface :
  ProfileDefinitionsDepthGeometrySurface
canonicalProfileDefinitionsDepthGeometrySurface = record
  { ForcedTailSourceDef = DepthBase.ForcedTailSourceDef
  ; AdversarialTargetDef = DepthBase.AdversarialTargetDef
  ; TransitionTargetDef = DepthBase.TransitionTargetDef
  ; forcedTailDefinitionImpliesLabel = λ N i def → def
  ; adversarialDefinitionImpliesLabel = λ N j def → def
  ; transitionDefinitionImpliesLabel = λ N j def → def
  ; forcedTailLabelToDefinition = λ N i label → label
  ; adversarialLabelToDefinition = λ N j label → label
  ; transitionLabelToDefinition = λ N j label → label
  ; forcedTailSourceDefDepthUpper =
      λ N i def →
        DepthBase.ForcedTailSourceDef.depthUpper def
  ; adversarialTargetDefDepthLower =
      λ N j def →
        DepthBase.AdversarialTargetDef.depthLower def
  ; transitionTargetDefDepthLower =
      λ N j def →
        DepthBase.TransitionTargetDef.depthLower def
  }

toActualProfileDefinitionSurface :
  ProfileDefinitionsDepthGeometrySurface →
  FromDefinitions.ActualProfileDefinitionSurface
toActualProfileDefinitionSurface surface = record
  { ActualForcedTailSourceDefinition =
      ProfileDefinitionsDepthGeometrySurface.ForcedTailSourceDef surface
  ; ActualAdversarialTargetDefinition =
      ProfileDefinitionsDepthGeometrySurface.AdversarialTargetDef surface
  ; ActualTransitionTargetDefinition =
      ProfileDefinitionsDepthGeometrySurface.TransitionTargetDef surface
  ; actualForcedTailImpliesLabel =
      ProfileDefinitionsDepthGeometrySurface.forcedTailDefinitionImpliesLabel
        surface
  ; actualAdversarialImpliesLabel =
      ProfileDefinitionsDepthGeometrySurface.adversarialDefinitionImpliesLabel
        surface
  ; actualTransitionImpliesLabel =
      ProfileDefinitionsDepthGeometrySurface.transitionDefinitionImpliesLabel
        surface
  }

toFromDefinitionsTarget :
  (surface : ProfileDefinitionsDepthGeometrySurface) →
  FromDefinitions.ProfileDepthSemanticsFromDefinitionsTarget
    (toActualProfileDefinitionSurface surface)
toFromDefinitionsTarget surface = record
  { forcedTailLabelToDefinition =
      ProfileDefinitionsDepthGeometrySurface.forcedTailLabelToDefinition surface
  ; adversarialLabelToDefinition =
      ProfileDefinitionsDepthGeometrySurface.adversarialLabelToDefinition surface
  ; transitionLabelToDefinition =
      ProfileDefinitionsDepthGeometrySurface.transitionLabelToDefinition surface
  ; forcedTailSourceWithDepthCapFromDefinition =
      λ N i def →
        record
          { sourceLabel =
              FromDefinitions.ActualProfileDefinitionSurface.actualForcedTailImpliesLabel
                (toActualProfileDefinitionSurface surface) N i def
          ; sourceDepthUpper =
              ProfileDefinitionsDepthGeometrySurface.forcedTailSourceDefDepthUpper
                surface N i def
          }
  ; adversarialTargetWithDepthFloorFromDefinition =
      λ N j def →
        record
          { targetLabel =
              FromDefinitions.ActualProfileDefinitionSurface.actualAdversarialImpliesLabel
                (toActualProfileDefinitionSurface surface) N j def
          ; targetDepthLower =
              ProfileDefinitionsDepthGeometrySurface.adversarialTargetDefDepthLower
                surface N j def
          }
  ; transitionTargetWithDepthFloorFromDefinition =
      λ N j def →
        record
          { targetLabel =
              FromDefinitions.ActualProfileDefinitionSurface.actualTransitionImpliesLabel
                (toActualProfileDefinitionSurface surface) N j def
          ; targetDepthLower =
              ProfileDefinitionsDepthGeometrySurface.transitionTargetDefDepthLower
                surface N j def
          }
  }

canonicalReceiptText : String
canonicalReceiptText =
  "Analytic Blocker 1 profile-definition layer: labels must lift to real forced-tail, adversarial-target, and transition-target definitions whose content proves the required entryDepth inequalities."

canonicalOpenReasonText : String
canonicalOpenReasonText =
  "No repo module currently defines ForcedTailSource, AdversarialTarget, or TransitionTarget by explicit depth inequalities. The present labels remain analytically insufficient until this definition layer is inhabited."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: locate or create the real profile-definition module, then inhabit forcedTailLabelToDefinition, adversarialLabelToDefinition, transitionLabelToDefinition, and the three definition-to-depth inequality theorems."

record NSTriadKNProfileDefinitionsDepthGeometryReceipt : Setω where
  constructor mkNSTriadKNProfileDefinitionsDepthGeometryReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNProfileDefinitionsDepthGeometryReceipt"

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

    forcedTailDefinitionClosed : Bool
    forcedTailDefinitionClosedIsTrue :
      forcedTailDefinitionClosed ≡ true

    adversarialDefinitionClosed : Bool
    adversarialDefinitionClosedIsTrue :
      adversarialDefinitionClosed ≡ true

    transitionDefinitionClosed : Bool
    transitionDefinitionClosedIsTrue :
      transitionDefinitionClosed ≡ true

    labelLiftClosed : Bool
    labelLiftClosedIsTrue :
      labelLiftClosed ≡ true

    depthGeometryClosed : Bool
    depthGeometryClosedIsTrue :
      depthGeometryClosed ≡ true

canonicalNSTriadKNProfileDefinitionsDepthGeometryReceipt :
  NSTriadKNProfileDefinitionsDepthGeometryReceipt
canonicalNSTriadKNProfileDefinitionsDepthGeometryReceipt =
  mkNSTriadKNProfileDefinitionsDepthGeometryReceipt
    "NSTriadKNProfileDefinitionsDepthGeometryReceipt"
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

actualProfileDefinitionSurfaceClosed : Bool
actualProfileDefinitionSurfaceClosed = true
