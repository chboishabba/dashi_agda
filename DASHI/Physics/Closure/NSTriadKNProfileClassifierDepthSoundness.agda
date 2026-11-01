module DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using ( PairIncidenceProfile
        ; forcedTailProfile
        ; adversarialGeometryProfile
        ; transitionProfile
        )
import DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessSurface
  as Surface
import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement as Refinement
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel

------------------------------------------------------------------------
-- Fail-closed Blocker 1 surface: classifier-depth soundness.
--
-- The existing profile decomposition closes only a label-level classifier.
-- It does not carry shell/depth witnesses showing why a label is valid.
--
-- So the missing FT→adv theorem is not a Schur theorem. It is the
-- witness-carrying bridge:
--
--   restricted FT→adv incidence
--      -> adversarial classifier label
--      -> forced-tail source witness + adversarial target witness
--      -> profile depth inequalities
--
-- This module records that exact missing surface and remains fail-closed.
------------------------------------------------------------------------

data NSTriadKNProfileClassifierDepthSoundnessPromotion : Set where

profileClassifierDepthSoundnessPromotionImpossibleHere :
  NSTriadKNProfileClassifierDepthSoundnessPromotion → ⊥
profileClassifierDepthSoundnessPromotionImpossibleHere ()

ClassifiedProfileWitness : Nat → Nat → Nat → Set₁
ClassifiedProfileWitness =
  Surface.ClassifiedProfileWitness
    WeightModel.entryDepth
    WeightModel.ForcedTailSource
    WeightModel.AdversarialTarget
    WeightModel.TransitionTarget

FTAdvClassifierDepthSoundnessTarget : Set₁
FTAdvClassifierDepthSoundnessTarget =
  Surface.FTAdvClassifierDepthSoundnessTarget
    WeightModel.entryDepth
    WeightModel.ForcedTailSource
    WeightModel.AdversarialTarget
    WeightModel.TransitionTarget
    Refinement.FTToAdversarialIncidence

canonicalReceiptText : String
canonicalReceiptText =
  "Fail-closed Blocker 1 receipt: restricted FT->adv incidence now carries classifier landing and source/target labels, but the existing profile classifier is still label-only, so depth separation still requires a strengthened witness-carrying classifier-depth soundness theorem."

canonicalMissingTheoremText : String
canonicalMissingTheoremText =
  "Missing theorem: from the carried adversarial classifier landing, construct a ClassifiedProfileWitness with the depth data needed to justify the source/target inequalities behind FT->adv depth separation."

canonicalWhyOpenText : String
canonicalWhyOpenText =
  "The existing decomposition receipt only partitions multiplicities by profile label. It does not store shell/depth witnesses or prove that the carried adversarial label is sound for entry-depth geometry."

canonicalNextStepText : String
canonicalNextStepText =
  "Next step: build a witness-carrying classifier layer or a classifierWitnessFromConstruction theorem, then feed that into ProfileDepthSemantics to discharge FT->adv depth separation."

record NSTriadKNProfileClassifierDepthSoundnessReceipt : Setω where
  constructor mkNSTriadKNProfileClassifierDepthSoundnessReceipt
  field
    receiptName : String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadKNProfileClassifierDepthSoundnessReceipt"

    receiptText : String
    receiptTextIsCanonical :
      receiptText ≡ canonicalReceiptText

    missingTheoremText : String
    missingTheoremTextIsCanonical :
      missingTheoremText ≡ canonicalMissingTheoremText

    whyOpenText : String
    whyOpenTextIsCanonical :
      whyOpenText ≡ canonicalWhyOpenText

    nextStepText : String
    nextStepTextIsCanonical :
      nextStepText ≡ canonicalNextStepText

    theoremSurfaceImplemented : Bool
    theoremSurfaceImplementedIsTrue :
      theoremSurfaceImplemented ≡ true

    classifierIsLabelOnly : Bool
    classifierIsLabelOnlyIsTrue :
      classifierIsLabelOnly ≡ true

    witnessCarryingClassifierAvailable : Bool
    witnessCarryingClassifierAvailableIsFalse :
      witnessCarryingClassifierAvailable ≡ false

    classifierDepthSoundnessClosed : Bool
    classifierDepthSoundnessClosedIsFalse :
      classifierDepthSoundnessClosed ≡ false

    theoremPromoted : Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

canonicalNSTriadKNProfileClassifierDepthSoundnessReceipt :
  NSTriadKNProfileClassifierDepthSoundnessReceipt
canonicalNSTriadKNProfileClassifierDepthSoundnessReceipt =
  mkNSTriadKNProfileClassifierDepthSoundnessReceipt
    "NSTriadKNProfileClassifierDepthSoundnessReceipt"
    refl
    canonicalReceiptText
    refl
    canonicalMissingTheoremText
    refl
    canonicalWhyOpenText
    refl
    canonicalNextStepText
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl

classifierDepthSoundnessClosed : Bool
classifierDepthSoundnessClosed = false
