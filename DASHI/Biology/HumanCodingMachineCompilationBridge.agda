module DASHI.Biology.HumanCodingMachineCompilationBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Human qualitative coding / machine compilation bridge.
--
-- The source paper uses manually assigned OEF labels as supervised training
-- data.  This module records the common architecture shared with qualitative
-- coding practices:
--
--   text + coding frame + interpreter -> categorised-meaning candidate
--
-- Machine classification scales a previously encoded interpretive frame.  It
-- does not remove interpretation, discover neutral themes, or promote itself
-- to semantic authority.

data Never : Set where

data CodingMode : Set where
  manualQualitativeCoding : CodingMode
  manualOEFContentCoding : CodingMode
  supervisedTrainingCompilation : CodingMode
  modelPredictionCoding : CodingMode
  contextualHumanReview : CodingMode

canonicalCodingModes : List CodingMode
canonicalCodingModes =
  manualQualitativeCoding
  ∷ manualOEFContentCoding
  ∷ supervisedTrainingCompilation
  ∷ modelPredictionCoding
  ∷ contextualHumanReview
  ∷ []

record CodingFrame : Set where
  constructor mkCodingFrame
  field
    frameLabel : String
    frameElements : List OEF.OEFElement
    frameHumanConstructed : Bool
    frameHumanConstructedIsTrue : frameHumanConstructed ≡ true
    frameInterpretive : Bool
    frameInterpretiveIsTrue : frameInterpretive ≡ true
    frameNotNeutralOntology : Bool
    frameNotNeutralOntologyIsTrue : frameNotNeutralOntology ≡ true

open CodingFrame public

canonicalOEFCodingFrame : CodingFrame
canonicalOEFCodingFrame =
  mkCodingFrame
    "human-constructed OEF coding frame"
    OEF.canonicalOEFElements
    true refl
    true refl
    true refl

record CodingTransition : Set where
  constructor mkCodingTransition
  field
    transitionLabel : String
    sourceMode : CodingMode
    targetMode : CodingMode
    sourceTextSurface : String
    sourceFrame : CodingFrame
    outputBundle : OEF.OEFBundle
    transitionInterpretive : Bool
    transitionInterpretiveIsTrue : transitionInterpretive ≡ true
    transitionRepeatable : Bool
    transitionRepeatableIsTrue : transitionRepeatable ≡ true
    transitionNotSemanticClosure : Bool
    transitionNotSemanticClosureIsTrue : transitionNotSemanticClosure ≡ true
    transitionRequiresReview : Bool
    transitionRequiresReviewIsTrue : transitionRequiresReview ≡ true

open CodingTransition public

canonicalHumanToTrainingTransition : CodingTransition
canonicalHumanToTrainingTransition =
  mkCodingTransition
    "manual OEF coding to supervised training datum"
    manualOEFContentCoding
    supervisedTrainingCompilation
    "voluntary end-of-course feedback comment"
    canonicalOEFCodingFrame
    OEF.canonicalForumBundle
    true refl
    true refl
    true refl
    true refl

canonicalModelToReviewTransition : CodingTransition
canonicalModelToReviewTransition =
  mkCodingTransition
    "model-predicted OEF bundle to contextual human review"
    modelPredictionCoding
    contextualHumanReview
    "model prediction surface"
    canonicalOEFCodingFrame
    OEF.canonicalForumBundle
    true refl
    true refl
    true refl
    true refl

data CodingPromotionRoute : Set where
  compiledInterpretiveFrameRoute : CodingPromotionRoute
  machineRemovesInterpretationRoute : CodingPromotionRoute
  predictedThemeEqualsLatentMeaningRoute : CodingPromotionRoute
  repeatabilityEqualsObjectivityRoute : CodingPromotionRoute
  codeEqualsStudentEssenceRoute : CodingPromotionRoute

AdmissibleCodingPromotionRoute : CodingPromotionRoute → Set
AdmissibleCodingPromotionRoute compiledInterpretiveFrameRoute = ⊤
AdmissibleCodingPromotionRoute machineRemovesInterpretationRoute = Never
AdmissibleCodingPromotionRoute predictedThemeEqualsLatentMeaningRoute = Never
AdmissibleCodingPromotionRoute repeatabilityEqualsObjectivityRoute = Never
AdmissibleCodingPromotionRoute codeEqualsStudentEssenceRoute = Never

compiledInterpretiveFrameRouteAdmissible :
  AdmissibleCodingPromotionRoute compiledInterpretiveFrameRoute
compiledInterpretiveFrameRouteAdmissible = tt

machineRemovesInterpretationBlocked :
  AdmissibleCodingPromotionRoute machineRemovesInterpretationRoute → Never
machineRemovesInterpretationBlocked ()

predictedThemeEqualsLatentMeaningBlocked :
  AdmissibleCodingPromotionRoute predictedThemeEqualsLatentMeaningRoute → Never
predictedThemeEqualsLatentMeaningBlocked ()

repeatabilityEqualsObjectivityBlocked :
  AdmissibleCodingPromotionRoute repeatabilityEqualsObjectivityRoute → Never
repeatabilityEqualsObjectivityBlocked ()

codeEqualsStudentEssenceBlocked :
  AdmissibleCodingPromotionRoute codeEqualsStudentEssenceRoute → Never
codeEqualsStudentEssenceBlocked ()

record HumanCodingMachineCompilationBridge : Set where
  constructor mkHumanCodingMachineCompilationBridge
  field
    sourceSystem : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceSystemIsCanonical : sourceSystem ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    codingFrame : CodingFrame
    codingFrameIsCanonical : codingFrame ≡ canonicalOEFCodingFrame
    humanToTrainingTransition : CodingTransition
    humanToTrainingTransitionIsCanonical :
      humanToTrainingTransition ≡ canonicalHumanToTrainingTransition
    modelToReviewTransition : CodingTransition
    modelToReviewTransitionIsCanonical :
      modelToReviewTransition ≡ canonicalModelToReviewTransition
    route : CodingPromotionRoute
    routeIsCompiledInterpretive : route ≡ compiledInterpretiveFrameRoute
    routeAdmissible : AdmissibleCodingPromotionRoute route
    machineScalesHumanCoding : Bool
    machineScalesHumanCodingIsTrue : machineScalesHumanCoding ≡ true
    interpretationPreserved : Bool
    interpretationPreservedIsTrue : interpretationPreserved ≡ true
    contextualReviewRequired : Bool
    contextualReviewRequiredIsTrue : contextualReviewRequired ≡ true
    noSemanticClosure : Bool
    noSemanticClosureIsTrue : noSemanticClosure ≡ true
    reading : String

open HumanCodingMachineCompilationBridge public

canonicalHumanCodingMachineCompilationBridge :
  HumanCodingMachineCompilationBridge
canonicalHumanCodingMachineCompilationBridge =
  mkHumanCodingMachineCompilationBridge
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalOEFCodingFrame refl
    canonicalHumanToTrainingTransition refl
    canonicalModelToReviewTransition refl
    compiledInterpretiveFrameRoute refl tt
    true refl
    true refl
    true refl
    true refl
    "The OEF classifier compiles and scales a humanly constructed qualitative coding frame. Repeatability is useful, but does not erase interpretation or turn predicted categories into latent student meaning."

HumanLabelCompiledNotRemoved : Set
HumanLabelCompiledNotRemoved =
  machineScalesHumanCoding canonicalHumanCodingMachineCompilationBridge ≡ true

humanLabelCompiledNotRemoved : HumanLabelCompiledNotRemoved
humanLabelCompiledNotRemoved =
  machineScalesHumanCodingIsTrue canonicalHumanCodingMachineCompilationBridge
